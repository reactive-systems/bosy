import Utils
import CAiger

struct InputSymbolicEncoding: BoSyEncoding {
    
    let automaton: CoBüchiAutomaton
    let semantics: TransitionSystemType
    let inputs: [String]
    let outputs: [String]
    
    // intermediate results
    var assignments: BooleanAssignment?
    var instance: Boolean?
    var solutionBound: Int
    
    init(automaton: CoBüchiAutomaton, semantics: TransitionSystemType, inputs: [String], outputs: [String]) {
        self.automaton = automaton
        self.semantics = semantics
        self.inputs = inputs
        self.outputs = outputs
        
        assignments = nil
        instance = nil
        solutionBound = 0
    }
    
    func getEncoding(forBound bound: Int) -> Boolean? {
        
        let states = 0..<bound

        // assignment that represents initial state condition
        var initialAssignment: BooleanAssignment = [:]
        for state in automaton.initialStates {
            initialAssignment[lambda(0, state)] = Literal.True
        }
        
        var matrix: [Boolean] = []
        
        for source in states {
            // there must be at least one transition
            let exists = states.map({ target in tau(source, target)})
                               .reduce(Literal.False, |)
            matrix.append(exists)
            
            let renamer = RenamingBooleanVisitor(rename: { name in self.outputs.contains(name) ? self.output(name, forState: source) : name })
            
            for q in automaton.states {
                var conjunct: [Boolean] = []
                
                if let condition = automaton.safetyConditions[q] {
                    conjunct.append(condition.accept(visitor: renamer))
                }
                
                guard let outgoing = automaton.transitions[q] else {
                    assert(conjunct.isEmpty)
                    continue
                }
                
                for (qPrime, guardCondition) in outgoing {
                    let transitionCondition = requireTransition(from: source, q: q, qPrime: qPrime, bound: bound, rejectingStates: automaton.rejectingStates)
                    if guardCondition as? Literal != nil && guardCondition as! Literal == Literal.True {
                        conjunct.append(transitionCondition)
                    } else {
                        conjunct.append(BinaryOperator(.Implication, operands: [guardCondition.accept(visitor: renamer), transitionCondition]))
                    }
                }
                matrix.append(BinaryOperator(.Implication, operands: [
                    lambda(source, q),
                    conjunct.reduce(Literal.True, &)
                ]))
            }
        }
        
        let formula: Boolean = matrix.reduce(Literal.True, &)
        
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
            taus += (0..<bound).map({ sPrime in tau(s, sPrime) })
        }
        var outputPropositions: [Proposition] = []
        for o in outputs {
            for s in 0..<bound {
                outputPropositions.append(Proposition(output(o, forState: s)))
            }
        }
        let inputPropositions: [Proposition] = inputs.map({ input in Proposition(input) })
        
        let innerExistentials: [Proposition]
        let outerExistentials: [Proposition]
        
        switch semantics {
        case .Mealy:
            innerExistentials = taus + outputPropositions
            outerExistentials = lambdas + lambdaSharps
        case .Moore:
            innerExistentials = taus
            outerExistentials = lambdas + lambdaSharps + outputPropositions
        }
        
        var qbf: Boolean = Quantifier(.Exists, variables: innerExistentials, scope: formula)
        qbf = Quantifier(.Forall, variables: inputPropositions, scope: qbf)
        qbf = Quantifier(.Exists, variables: outerExistentials, scope: qbf)
        
        qbf = qbf.eval(assignment: initialAssignment)
        
        //print(qbf)
        
        let boundednessCheck = BoundednessVisitor()
        assert(qbf.accept(visitor: boundednessCheck))
        
        let removeComparable = RemoveComparableVisitor(bound: bound)
        qbf = qbf.accept(visitor: removeComparable)
        
        return qbf
    }
    
    func requireTransition(from s: Int, q: CoBüchiAutomaton.State, qPrime: CoBüchiAutomaton.State, bound: Int, rejectingStates: Set<CoBüchiAutomaton.State>) -> Boolean {
        let validTransition: [Boolean]
        if automaton.isStateInNonRejectingSCC(q) || automaton.isStateInNonRejectingSCC(qPrime) || !automaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            validTransition = (0..<bound).map({
                sPrime in
                BinaryOperator(
                    .Implication,
                    operands: [
                        tauNextStateAssertion(state: s, nextState: sPrime, bound: bound),
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
                        tauNextStateAssertion(state: s, nextState: sPrime, bound: bound),
                        lambda(sPrime, qPrime) & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual, lhs: lambdaSharp(sPrime, qPrime), rhs: lambdaSharp(s, q))
                    ]
                )
            })
        }
        return validTransition.reduce(Literal.True, &)
    }
    
    func tauNextStateAssertion(state: Int, nextState: Int, bound: Int) -> Boolean {
        return tau(state, nextState)
    }
    
    func lambda(_ state: Int, _ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("λ_\(state)_\(automatonState)")
    }
    
    func lambdaSharp(_ state: Int, _ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("λ#_\(state)_\(automatonState)")
    }
    
    func tau(_ fromState: Int, _ toState: Int) -> Proposition {
        return Proposition("τ_\(fromState)_\(toState)")
    }
    
    func output(_ name: String, forState state: Int) -> String {
        return "\(name)_\(state)"
    }
    
    mutating func solve(forBound bound: Int) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")
        
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        //print(instance)
        
        let qdimacsVisitor = QDIMACSVisitor()
        let _ = instance.accept(visitor: qdimacsVisitor)
        //print(qdimacsVisitor)
        guard let (result, assignments) = rareqs(qdimacs: bloqqer(qdimacs: "\(qdimacsVisitor)")) else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        
        if result == .SAT {
            // keep top level valuations of solver
            let topLevel = instance as! Quantifier
            var assignments = qdimacsVisitor.getAssignment(fromAssignment: assignments!)
            let remove = assignments.filter({ (key, value) in !topLevel.variables.contains(key) })
            for (proposition, _) in remove {
                assignments.removeValue(forKey: proposition)
            }
            self.assignments = assignments
            self.instance = instance.eval(assignment: assignments)
            self.solutionBound = bound
            return true
        }
        return false
    }
    
    func extractSolution() -> BoSySolution? {
        guard let instance = self.instance, let assignments = self.assignments else {
            Logger.default().error("hasSolution() must be true before calling this function")
            return nil
        }
        //print(instance)
        
        let qdimacsVisitor = QDIMACSVisitor()
        let _ = instance.accept(visitor: qdimacsVisitor)
        
        // have to solve it again without preprocessor to get useful assignments
        guard let (result, additionalAssignments) = rareqs(qdimacs: "\(qdimacsVisitor)") else {
            Logger.default().error("solver failed on instance")
            return nil
        }
        assert(result == .SAT)
        
        //print(assignments)
        let origAssignment = qdimacsVisitor.getAssignment(fromAssignment: additionalAssignments!)
        //print(origAssignment)
        let reducedInstance = instance.eval(assignment: origAssignment)
        //print(reducedInstance)
        
        let newVisitor = QCIRVisitor()
        let _ = reducedInstance.accept(visitor: newVisitor)
        guard let (res, cert) = quabs(qcir: "\(newVisitor)") else {
            Logger.default().error("could not certify with QuAbS")
            return nil
        }
        assert(res == .SAT)
        guard let certificate = cert else {
            return nil
        }
        guard let minimizedCertificate = minimizeWithABC(certificate) else {
            Logger.default().error("could not minimize certificate with ABC")
            return nil
        }
        aiger_reset(certificate)
        var functions = newVisitor.translate(certificate: minimizedCertificate)
        aiger_reset(minimizedCertificate)
        for (proposition, literal) in origAssignment {
            functions[proposition] = literal
        }
        for (proposition, literal) in assignments {
            functions[proposition] = literal
        }
        
        var solution = ExplicitStateSolution(bound: solutionBound, inputs: inputs, outputs: outputs)
        for source in 0..<solutionBound {
            for target in 0..<solutionBound {
                let transition = functions[tau(source, target)]!
                if transition as? Literal != nil && transition as! Literal == Literal.False {
                    continue
                }
                solution.addTransition(from: source, to: target, withGuard: transition)
            }
            for output in outputs {
                let proposition = Proposition(self.output(output, forState: source))
                let enabled = functions[proposition]!
                solution.add(output: output, inState: source, withGuard: enabled)
            }
        }
        return solution
    }
}
