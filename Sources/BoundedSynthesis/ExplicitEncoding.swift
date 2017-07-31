import Utils
import CAiger
import Logic
import Automata
import Specification
import TransitionSystem

struct ExplicitEncoding: BoSyEncoding {
    
    let options: BoSyOptions
    let automaton: CoBüchiAutomaton
    let specification: SynthesisSpecification
    
    // intermediate results
    var assignments: BooleanAssignment?
    var solutionBound: Int
    
    init(options: BoSyOptions, automaton: CoBüchiAutomaton, specification: SynthesisSpecification) {
        self.options = options
        self.automaton = automaton
        self.specification = specification
        
        assignments = nil
        solutionBound = 0
    }
    
    func getEncoding(forBound bound: Int) -> Logic? {
        
        let states = 0..<bound
        
        let inputPropositions: [Proposition] = specification.inputs.map({ Proposition($0) })

        // assignment that represents initial state condition
        var initialAssignment: BooleanAssignment = [:]
        for state in automaton.initialStates {
            initialAssignment[lambda(0, state)] = Literal.True
        }
        
        var matrix: [Logic] = []
        //matrix.append(automaton.initialStates.reduce(Literal.True, { (val, state) in val & lambda(0, state) }))
        
        for source in states {
            // for every valuation of inputs, there must be at least one tau enabled
            var conjunction: [Logic] = []
            for i in allBooleanAssignments(variables: inputPropositions) {
                let disjunction = states.map({ target in tau(source, i, target) })
                                        .reduce(Literal.False, |)
                conjunction.append(disjunction)
            }
            matrix.append(conjunction.reduce(Literal.True, &))
            
            func getRenamer(i: BooleanAssignment) -> RenamingBooleanVisitor {
                if specification.semantics == .mealy {
                    return RenamingBooleanVisitor(rename: { name in self.specification.outputs.contains(name) ? self.output(name, forState: source, andInputs: i) : name })
                } else {
                    return RenamingBooleanVisitor(rename: { name in self.specification.outputs.contains(name) ? self.output(name, forState: source) : name })
                }
            }
            
            for q in automaton.states {
                var conjunct: [Logic] = []
                
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
                            conjunct.append(evaluatedCondition.accept(visitor: renamer) --> transitionCondition)
                        }
                    }
                }
                matrix.append(lambda(source, q) -->  conjunct.reduce(Literal.True, &))
            }
        }
        
        let formula: Logic = matrix.reduce(Literal.True, &)
        
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
        for o in specification.outputs {
            for s in 0..<bound {
                if specification.semantics == .mealy {
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        outputPropositions.append(Proposition(output(o, forState: s, andInputs: i)))
                    }
                } else {
                    outputPropositions.append(Proposition(output(o, forState: s)))
                }
            }
        }
        
        let existentials: [Proposition] = lambdas + lambdaSharps + taus + outputPropositions
        
        var qbf: Logic = Quantifier(.Exists, variables: existentials, scope: formula)
        
        qbf = qbf.eval(assignment: initialAssignment)
        
        //print(qbf)
        
        let boundednessCheck = BoundednessVisitor()
        assert(qbf.accept(visitor: boundednessCheck))
        
        let removeComparable = RemoveComparableVisitor(bound: bound)
        qbf = qbf.accept(visitor: removeComparable)
        
        return qbf
    }
    
    func requireTransition(from s: Int, q: CoBüchiAutomaton.State, i: BooleanAssignment, qPrime: CoBüchiAutomaton.State, bound: Int, rejectingStates: Set<CoBüchiAutomaton.State>) -> Logic {
        let validTransition: [Logic]
        if automaton.isStateInNonRejectingSCC(q) || automaton.isStateInNonRejectingSCC(qPrime) || !automaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            validTransition = (0..<bound).map({
                sPrime in
                tauNextStateAssertion(state: s, i, nextState: sPrime, bound: bound) --> lambda(sPrime, qPrime)
            })
        } else {
            validTransition = (0..<bound).map({
                sPrime in
                tauNextStateAssertion(state: s, i, nextState: sPrime, bound: bound) -->
                (lambda(sPrime, qPrime) & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual, lhs: lambdaSharp(sPrime, qPrime), rhs: lambdaSharp(s, q)))
            })
        }
        return validTransition.reduce(Literal.True, &)
    }
    
    func tauNextStateAssertion(state: Int, _ inputs: BooleanAssignment, nextState: Int, bound: Int) -> Logic {
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
            assert(specification.semantics == .moore)
            return "\(name)_\(state)"
        }
        assert(specification.semantics == .mealy)
        return "\(name)_\(state)_\(bitStringFromAssignment(inputs))"
    }

    
    mutating func solve(forBound bound: Int) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")
        
        let constraintTimer = options.statistics?.startTimer(phase: .constraintGeneration)
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        constraintTimer?.stop()
        //print(instance)
        
        guard let solver = options.solver?.instance as? SatSolver else {
            throw BoSyEncodingError.SolvingFailed("solver creation failed")
        }
        
        let solvingTimer = options.statistics?.startTimer(phase: .solving)
        guard let result = solver.solve(formula: instance) else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        solvingTimer?.stop()
        
        if case .sat(let assignments) = result {
            // keep top level valuations of solver
            self.assignments = assignments
            self.solutionBound = bound
            return true
        }
        return false
    }
    
    func extractSolution() -> TransitionSystem? {
        let extractionTimer = options.statistics?.startTimer(phase: .solutionExtraction)
        let inputPropositions: [Proposition] = specification.inputs.map({ Proposition($0) })
        
        guard let assignments = assignments else {
            Logger.default().error("hasSolution() must be true before calling this function")
            return nil
        }
        
        var solution = ExplicitStateSolution(bound: solutionBound, specification: specification)
        for source in 0..<solutionBound {
            for target in 0..<solutionBound {
                var transitions: [Logic] = []
                for i in allBooleanAssignments(variables: inputPropositions) {
                    if assignments[tau(source, i, target)]! == Literal.False {
                        let clause = i.map({ v, val in val == Literal.True ? !v : v })
                        transitions.append(clause.reduce(Literal.False, |))
                    }
                }
                let transition = transitions.reduce(Literal.True, &)
                if transition as? Literal != nil && transition as! Literal == Literal.False {
                    continue
                }
                solution.addTransition(from: source, to: target, withGuard: transition)
            }
            for output in specification.outputs {
                let enabled: Logic
                switch specification.semantics {
                case .mealy:
                    var clauses: [Logic] = []
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        let proposition = Proposition(self.output(output, forState: source, andInputs: i))
                        if assignments[proposition]! == Literal.False {
                            let clause = i.map({ v, val in val == Literal.True ? !v : v })
                            clauses.append(clause.reduce(Literal.False, |))
                        }
                    }
                    enabled = clauses.reduce(Literal.True, &)
                case .moore:
                    let proposition = Proposition(self.output(output, forState: source))
                    enabled = assignments[proposition]!
                }
                solution.add(output: output, inState: source, withGuard: enabled)
            }
        }
        extractionTimer?.stop()
        return solution
    }
}
