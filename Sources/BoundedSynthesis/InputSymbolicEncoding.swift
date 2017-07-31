import Utils
import CAiger
import Logic
import Automata
import Specification
import TransitionSystem

struct InputSymbolicEncoding: BoSyEncoding {
    
    let options: BoSyOptions
    let automaton: CoBüchiAutomaton
    let specification: SynthesisSpecification
    let synthesize: Bool
    
    // intermediate results
    var assignments: BooleanAssignment?
    var instance: Logic?
    var solutionBound: Int
    
    init(options: BoSyOptions, automaton: CoBüchiAutomaton, specification: SynthesisSpecification, synthesize: Bool) {
        self.options = options
        self.automaton = automaton
        self.specification = specification
        self.synthesize = synthesize
        
        assignments = nil
        instance = nil
        solutionBound = 0
    }
    
    func getEncoding(forBound bound: Int) -> Logic? {
        
        let states = 0..<bound

        // assignment that represents initial state condition
        var initialAssignment: BooleanAssignment = [:]
        for state in automaton.initialStates {
            initialAssignment[lambda(0, state)] = Literal.True
        }
        
        var matrix: [Logic] = []
        
        for source in states {
            // there must be at least one transition
            let exists = states.map({ target in tau(source, target)})
                               .reduce(Literal.False, |)
            matrix.append(exists)
            
            let renamer = RenamingBooleanVisitor(rename: { name in self.specification.outputs.contains(name) ? self.output(name, forState: source) : name })
            
            for q in automaton.states {
                var conjunct: [Logic] = []
                
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
                        conjunct.append(guardCondition.accept(visitor: renamer) --> transitionCondition)
                    }
                }
                matrix.append(lambda(source, q) --> conjunct.reduce(Literal.True, &))
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
            taus += (0..<bound).map({ sPrime in tau(s, sPrime) })
        }
        var outputPropositions: [Proposition] = []
        for o in specification.outputs {
            for s in 0..<bound {
                outputPropositions.append(Proposition(output(o, forState: s)))
            }
        }
        let inputPropositions: [Proposition] = specification.inputs.map({ input in Proposition(input) })
        
        let innerExistentials: [Proposition]
        let outerExistentials: [Proposition]
        
        switch specification.semantics {
        case .mealy:
            innerExistentials = taus + outputPropositions
            outerExistentials = lambdas + lambdaSharps
        case .moore:
            innerExistentials = taus
            outerExistentials = lambdas + lambdaSharps + outputPropositions
        }
        
        var qbf: Logic = Quantifier(.Exists, variables: innerExistentials, scope: formula)
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
    
    func requireTransition(from s: Int, q: CoBüchiAutomaton.State, qPrime: CoBüchiAutomaton.State, bound: Int, rejectingStates: Set<CoBüchiAutomaton.State>) -> Logic {
        let validTransition: [Logic]
        if automaton.isStateInNonRejectingSCC(q) || automaton.isStateInNonRejectingSCC(qPrime) || !automaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            validTransition = (0..<bound).map({
                sPrime in
                tauNextStateAssertion(state: s, nextState: sPrime, bound: bound) --> lambda(sPrime, qPrime)
            })
        } else {
            validTransition = (0..<bound).map({
                sPrime in
                tauNextStateAssertion(state: s, nextState: sPrime, bound: bound) -->
                (lambda(sPrime, qPrime) & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual, lhs: lambdaSharp(sPrime, qPrime), rhs: lambdaSharp(s, q)))
            })
        }
        return validTransition.reduce(Literal.True, &)
    }
    
    func tauNextStateAssertion(state: Int, nextState: Int, bound: Int) -> Logic {
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
        
        let constraintTimer = options.statistics?.startTimer(phase: .constraintGeneration)
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        constraintTimer?.stop()
        //print(instance)
        
        guard let solver = options.solver?.instance as? QbfSolver else {
            throw BoSyEncodingError.SolvingFailed("solver creation failed")
        }
        
        let solvingTimer = options.statistics?.startTimer(phase: .solving)
        guard let preprocessorName = options.qbfPreprocessor else {
            throw BoSyEncodingError.SolvingFailed("no preprocessor selected")
        }
        let preprocessor: QbfPreprocessor = preprocessorName.getInstance(preserveAssignments: self.synthesize)
        guard let result = solver.solve(formula: instance, preprocessor: preprocessor) else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        solvingTimer?.stop()
        
        if case .sat(var assignments) = result {
            // keep top level valuations of solver
            let topLevel = instance as! Quantifier
            let remove = assignments.filter({ (key, value) in !topLevel.variables.contains(key) })
            for (proposition, _) in remove {
                assignments.removeValue(forKey: proposition)
            }
            self.assignments = assignments
            self.instance = instance//.eval(assignment: assignments)
            self.solutionBound = bound
            return true
        }
        
        return false
    }
    
    func extractSolution() -> TransitionSystem? {
        let extractionTimer = options.statistics?.startTimer(phase: .solutionExtraction)
        guard let instance = self.instance, let assignments = self.assignments else {
            Logger.default().error("hasSolution() must be true before calling this function")
            return nil
        }
        //print(instance)
        
        guard let solver = options.solver?.instance as? QbfSolver else {
            return nil
        }
        
        let reducedInstance = instance.eval(assignment: assignments)
        // have to solve it again without preprocessor to get assignments of remaining top-level variables
        guard let result = solver.solve(formula: reducedInstance, preprocessor: nil) else {
            Logger.default().error("solver failed on instance")
            return nil
        }
        guard case .sat(let additionalAssignments) = result else {
            Logger.default().error("solver gave unexpected result")
            return nil
        }
        
        //print(additionalAssignments)
        let twoQBFInstance = reducedInstance.eval(assignment: additionalAssignments)
        //print(twoQBFInstance)
        
        /*let greedyOptimizeLambda = false
        if greedyOptimizeLambda {
            var totalAssignment = assignments
            for (variable, assigmment) in additionalAssignments {
                assert(totalAssignment[variable] == nil)
                totalAssignment[variable] = assigmment
            }
            let before = totalAssignment
            let topLevel = instance as! Quantifier
            for variable in topLevel.variables {
                if totalAssignment[variable] == Literal.True {
                    totalAssignment[variable] = Literal.False
                }
                guard let result = solver.solve(formula: instance.eval(assignment: totalAssignment), preprocessor: nil) else {
                    Logger.default().error("solver failed on instance")
                    return nil
                }
                if case .unsat = result {
                    totalAssignment[variable] = Literal.True
                }
            }
            //print(before)
            //print(totalAssignment)
            
            twoQBFInstance = instance.eval(assignment: totalAssignment)
        }*/
        //print(QCIRVisitor(formula: twoQBFInstance).description)
        
        guard let certifier = options.qbfCertifier?.instance as? CertifyingQbfSolver else {
            return nil
        }
        
        guard let certificationResult = certifier.solve(formula: twoQBFInstance) else {
            Logger.default().error("could not certify QBF query")
            return nil
        }
        
        guard case .sat(var functions) = certificationResult else {
            Logger.default().error("solver gave unexpected result")
            return nil
        }

        for (proposition, literal) in additionalAssignments {
            functions[proposition] = literal
        }
        for (proposition, literal) in assignments {
            functions[proposition] = literal
        }
        
        var solution = ExplicitStateSolution(bound: solutionBound, specification: specification)
        for source in 0..<solutionBound {
            for target in 0..<solutionBound {
                let transition = functions[tau(source, target)]!
                if transition as? Literal != nil && transition as! Literal == Literal.False {
                    continue
                }
                solution.addTransition(from: source, to: target, withGuard: transition)
            }
            for output in specification.outputs {
                let proposition = Proposition(self.output(output, forState: source))
                let enabled = functions[proposition]!
                solution.add(output: output, inState: source, withGuard: enabled)
            }
        }
        extractionTimer?.stop()
        return solution
    }
}
