import Utils
import CAiger

struct ExplicitEncoding: BoSyEncoding {
    
    let automaton: CoBüchiAutomaton
    let semantics: TransitionSystemType
    let inputs: [String]
    let outputs: [String]
    
    // intermediate results
    var assignments: BooleanAssignment?
    var solutionBound: Int
    
    init(automaton: CoBüchiAutomaton, semantics: TransitionSystemType, inputs: [String], outputs: [String]) {
        self.automaton = automaton
        self.semantics = semantics
        self.inputs = inputs
        self.outputs = outputs
        
        assignments = nil
        solutionBound = 0
    }
    
    func getEncoding(forBound bound: Int) -> Boolean? {
        
        let states = 0..<bound
        
        let inputPropositions: [Proposition] = inputs.map({ Proposition($0) })

        // assignment that represents initial state condition
        var initialAssignment: BooleanAssignment = [:]
        for state in automaton.initialStates {
            initialAssignment[lambda(0, state)] = Literal.True
        }
        
        var matrix: [Boolean] = []
        //matrix.append(automaton.initialStates.reduce(Literal.True, combine: { (val, state) in val & lambda(0, state) }))
        
        for source in states {
            // for every valuation of inputs, there must be at least one tau enabled
            var conjunction: [Boolean] = []
            for i in allBooleanAssignments(variables: inputPropositions) {
                let disjunction = states.map({ target in tau(source, i, target) })
                                        .reduce(Literal.False, combine: |)
                conjunction.append(disjunction)
            }
            matrix.append(conjunction.reduce(Literal.True, combine: &))
            
            func getRenamer(i: BooleanAssignment) -> RenamingBooleanVisitor {
                if semantics == .Mealy {
                    return RenamingBooleanVisitor(rename: { name in self.outputs.contains(name) ? self.output(name, forState: source, andInputs: i) : name })
                } else {
                    return RenamingBooleanVisitor(rename: { name in self.outputs.contains(name) ? self.output(name, forState: source) : name })
                }
            }
            
            for q in automaton.states {
                var conjunct: [Boolean] = []
                
                if let condition = automaton.safetyConditions[q] {
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        let evaluatedCondition = condition.eval(assignment: i)
                        let renamer = getRenamer(i: i)
                        conjunct.append(evaluatedCondition.accept(visitor: renamer))
                    }
                }
                
                guard let outgoing = automaton.transitions[q] else {
                    assert(conjunct.isEmpty)
                    continue
                }
                
                for (qPrime, guardCondition) in outgoing {
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        let evaluatedCondition = guardCondition.eval(assignment: i)
                        let transitionCondition = requireTransition(from: source, q: q, i: i, qPrime: qPrime, bound: bound, rejectingStates: automaton.rejectingStates)
                        if evaluatedCondition as? Literal != nil && evaluatedCondition as! Literal == Literal.True {
                            conjunct.append(transitionCondition)
                        } else {
                            let renamer = getRenamer(i: i)
                            conjunct.append(BinaryOperator(.Implication, operands: [evaluatedCondition.accept(visitor: renamer), transitionCondition]))
                        }
                    }
                }
                matrix.append(BinaryOperator(.Implication, operands: [
                    lambda(source, q),
                    conjunct.reduce(Literal.True, combine: &)
                ]))
            }
        }
        
        let formula: Boolean = matrix.reduce(Literal.True, combine: &)
        
        var lambdas: [Proposition] = []
        for s in 0..<bound {
            for q in automaton.states {
                lambdas.append(lambda(s, q))
            }
        }
        var lambdaSharps: [Proposition] = []
        for s in 0..<bound {
            for q in automaton.states {
                lambdaSharps.append(lambdaSharp(s, q))
            }
        }
        var taus: [Proposition] = []
        for s in 0..<bound {
            for i in allBooleanAssignments(variables: inputPropositions) {
                taus += (0..<bound).map({ sPrime in tau(s, i, sPrime) })
            }
        }
        var outputPropositions: [Proposition] = []
        for o in outputs {
            for s in 0..<bound {
                if semantics == .Mealy {
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        outputPropositions.append(Proposition(output(o, forState: s, andInputs: i)))
                    }
                } else {
                    outputPropositions.append(Proposition(output(o, forState: s)))
                }
            }
        }
        
        let existentials: [Proposition] = lambdas + lambdaSharps + taus + outputPropositions
        
        var qbf: Boolean = Quantifier(.Exists, variables: existentials, scope: formula)
        
        qbf = qbf.eval(assignment: initialAssignment)
        
        //print(qbf)
        
        let boundednessCheck = BoundednessVisitor()
        assert(qbf.accept(visitor: boundednessCheck))
        
        let removeComparable = RemoveComparableVisitor(bound: bound)
        qbf = qbf.accept(visitor: removeComparable)
        
        return qbf
    }
    
    func requireTransition(from s: Int, q: CoBüchiAutomaton.State, i: BooleanAssignment, qPrime: CoBüchiAutomaton.State, bound: Int, rejectingStates: Set<CoBüchiAutomaton.State>) -> Boolean {
        let validTransition: [Boolean]
        if automaton.isStateInNonRejectingSCC(q) || automaton.isStateInNonRejectingSCC(qPrime) || !automaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            validTransition = (0..<bound).map({
                sPrime in
                BinaryOperator(
                    .Implication,
                    operands: [
                        tauNextStateAssertion(state: s, i, nextState: sPrime, bound: bound),
                        lambda(sPrime, qPrime)
                    ]
                )
            })
        } else {
            validTransition = (0..<bound).map({
                sPrime in
                BinaryOperator(
                    .Implication,
                    operands: [
                        tauNextStateAssertion(state: s, i, nextState: sPrime, bound: bound),
                        lambda(sPrime, qPrime) & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual, lhs: lambdaSharp(sPrime, qPrime), rhs: lambdaSharp(s, q))
                    ]
                )
            })
        }
        return validTransition.reduce(Literal.True, combine: &)
    }
    
    func tauNextStateAssertion(state: Int, _ inputs: BooleanAssignment, nextState: Int, bound: Int) -> Boolean {
        return tau(state, inputs, nextState)
    }
    
    func lambda(_ state: Int, _ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("λ_\(state)_\(automatonState)")
    }
    
    func lambdaSharp(_ state: Int, _ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("λ#_\(state)_\(automatonState)")
    }
    
    func tau(_ fromState: Int, _ inputs: BooleanAssignment, _ toState: Int) -> Proposition {
        return Proposition("τ_\(fromState)_\(bitStringFromAssignment(inputs))_\(toState)")
    }
    
    func output(_ name: String, forState state: Int, andInputs inputs: BooleanAssignment? = nil) -> String {
        guard let inputs = inputs else {
            assert(semantics == .Moore)
            return "\(name)_\(state)"
        }
        assert(semantics == .Mealy)
        return "\(name)_\(state)_\(bitStringFromAssignment(inputs))"
    }

    
    mutating func solve(forBound bound: Int) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")
        
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        //print(instance)
        
        let dimacsVisitor = DIMACSVisitor()
        let _ = instance.accept(visitor: dimacsVisitor)
        //print(dimacsVisitor)
        
        guard let (result, assignments) = picosat(dimacs: "\(dimacsVisitor)") else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        
        if result == .SAT {
            // keep top level valuations of solver
            self.assignments = dimacsVisitor.getAssignment(fromAssignment: assignments!)
            self.solutionBound = bound
            return true
        }
        return false
    }
    
    func extractSolution() -> BoSySolution? {
        let inputPropositions: [Proposition] = inputs.map({ Proposition($0) })
        
        guard let assignments = assignments else {
            Logger.default().error("hasSolution() must be true before calling this function")
            return nil
        }
        
        var solution = ExplicitStateSolution(bound: solutionBound, inputs: inputs, outputs: outputs)
        for source in 0..<solutionBound {
            for target in 0..<solutionBound {
                var transitions: [Boolean] = []
                for i in allBooleanAssignments(variables: inputPropositions) {
                    if assignments[tau(source, i, target)]! == Literal.False {
                        let clause = i.map({ v, val in val == Literal.True ? !v : v })
                        transitions.append(clause.reduce(Literal.False, combine: |))
                    }
                }
                let transition = transitions.reduce(Literal.True, combine: &)
                if transition as? Literal != nil && transition as! Literal == Literal.False {
                    continue
                }
                solution.addTransition(from: source, to: target, withGuard: transition)
            }
            for output in outputs {
                let enabled: Boolean
                switch semantics {
                case .Mealy:
                    var clauses: [Boolean] = []
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        let proposition = Proposition(self.output(output, forState: source, andInputs: i))
                        if assignments[proposition]! == Literal.False {
                            let clause = i.map({ v, val in val == Literal.True ? !v : v })
                            clauses.append(clause.reduce(Literal.False, combine: |))
                        }
                    }
                    enabled = clauses.reduce(Literal.True, combine: &)
                case .Moore:
                    let proposition = Proposition(self.output(output, forState: source))
                    enabled = assignments[proposition]!
                }
                solution.add(output: output, inState: source, withGuard: enabled)
            }
        }
        return solution
    }
}
