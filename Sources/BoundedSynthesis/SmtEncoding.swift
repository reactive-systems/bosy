import Utils
import CAiger
import Logic
import Automata
import Specification
import TransitionSystem

struct SmtEncoding: BoSyEncoding {
    
    let options: BoSyOptions
    let automaton: CoBüchiAutomaton
    let specification: SynthesisSpecification
    
    // intermediate results
    var assignments: BooleanAssignment?
    var instance: Logic?
    var solutionBound: Int
    var solver: SmtSolver?
    
    init(options: BoSyOptions, automaton: CoBüchiAutomaton, specification: SynthesisSpecification) {
        self.options = options
        self.automaton = automaton
        self.specification = specification
        
        assignments = nil
        instance = nil
        solutionBound = 0
    }
    
    func getEncoding(forBound bound: Int) -> String? {
        
        let states = 0..<bound
        
        var smt = "(set-logic UFDTLIA)\n"
        
        // states
        smt.append("(declare-datatypes () ((S \(states.map({ "(s\($0))" }).joined(separator: " ")))))\n")
        
        // lambdas
        for q in automaton.states {
            smt.append("(declare-fun \(lambda(q)) (S) Bool)\n")
        }
        
        // lambda sharp
        for q in automaton.states {
            smt.append("(declare-fun \(lambdaSharp(q)) (S) Int)\n")
        }
        
        // tau
        smt.append("(declare-fun tau (S \(specification.inputs.map({ name in "Bool" }).joined(separator: " "))) S)\n")
        
        switch specification.semantics {
        case .moore:
            for o in specification.outputs {
                smt.append("(declare-fun \(o) (S) Bool)\n")
            }
        case .mealy:
            for o in specification.outputs {
                smt.append("(declare-fun \(o) (S \(specification.inputs.map({ name in "Bool" }).joined(separator: " "))) Bool)\n")
            }
        }
        for state in automaton.initialStates {
            smt.append("(assert (\(lambda(state)) s0))\n")
        }

        let printer = SmtPrinter()
        
        for q in automaton.states {
            
            let replacer = ReplacingPropositionVisitor(replace: {
                proposition in
                if self.specification.outputs.contains(proposition.name) {
                    switch self.specification.semantics {
                    case .mealy:
                        let inputProps = [Proposition("s")] + self.specification.inputs.map({Proposition($0)})
                        return FunctionApplication(function: proposition, application: inputProps)
                    case .moore:
                        return FunctionApplication(function: proposition, application: [Proposition("s")])
                    }
                } else {
                    return nil
                }
            })
            
            if let condition = automaton.safetyConditions[q] {
                let assertion = FunctionApplication(function: lambda(q), application: [Proposition("s")]) --> condition.accept(visitor: replacer)
                smt.append("(assert (forall ((s S) \(specification.inputs.map({ "(\($0) Bool)" }).joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
            guard let outgoing = automaton.transitions[q] else {
                continue
            }
            
            for (qPrime, guardCondition) in outgoing {
                let transitionCondition = requireTransition(q: q, qPrime: qPrime, rejectingStates: automaton.rejectingStates)
                let assertion = (FunctionApplication(function: lambda(q), application: [Proposition("s")]) & guardCondition.accept(visitor: replacer)) --> transitionCondition
                smt.append("(assert (forall ((s S) \(specification.inputs.map({ "(\($0) Bool)" }).joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
        }
        
        return smt
    }
    
    func requireTransition(q: CoBüchiAutomaton.State, qPrime: CoBüchiAutomaton.State, rejectingStates: Set<CoBüchiAutomaton.State>) -> Logic {
        let lambdaNext = FunctionApplication(function: lambda(qPrime), application: [
            FunctionApplication(function: Proposition("tau"), application: [
                Proposition("s")
                ] + specification.inputs.map(Proposition.init) as [Proposition])
            ])
        if automaton.isStateInNonRejectingSCC(q) || automaton.isStateInNonRejectingSCC(qPrime) || !automaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            return lambdaNext
        } else {
            return lambdaNext & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual,
                                                  lhs: FunctionApplication(function: lambdaSharp(qPrime), application: [
                                                    FunctionApplication(function: Proposition("tau"), application: [
                                                        Proposition("s")
                                                        ] + specification.inputs.map(Proposition.init) as [Proposition])
                                                    ]),
                                                  rhs: FunctionApplication(function: lambdaSharp(q), application: [Proposition("s")]))
        }
    }
    
    func lambda(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("lambda_\(automatonState)")
    }
    
    func lambdaSharp(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("lambdaSharp_\(automatonState)")
    }

    mutating func solve(forBound bound: Int) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")
        
        let constraintTimer = options.statistics?.startTimer(phase: .constraintGeneration)
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        constraintTimer?.stop()
        //print(instance)
        
        guard let solver = options.solver?.instance as? SmtSolver else {
            throw BoSyEncodingError.SolvingFailed("solver creation failed")
        }
        self.solver = solver
        
        let solvingTimer = options.statistics?.startTimer(phase: .solving)
        guard let result = solver.solve(formula: instance) else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        solvingTimer?.stop()
        
        if result == .sat {
            self.solutionBound = bound
        }
        
        return result == .sat
    }
    
    func extractSolution() -> TransitionSystem? {
        guard let solver = solver else {
            return nil
        }
        
        let printer = SmtPrinter()
        
        let extractionTimer = options.statistics?.startTimer(phase: .solutionExtraction)
        let inputPropositions: [Proposition] = specification.inputs.map({ Proposition($0) })

        var solution = ExplicitStateSolution(bound: solutionBound, specification: specification)
        
        // extract solution: transition relation
        for source in 0..<solutionBound {
            for i in allBooleanAssignments(variables: inputPropositions) {
                let parameters = inputPropositions.map({ i[$0]! })
                let tauApplication = FunctionApplication(function: Proposition("tau"), application: [Proposition("s\(source)")] as [Logic] + parameters)
                guard let value = solver.getValue(expression: tauApplication.accept(visitor: printer)) else {
                    return nil
                }
                guard let proposition = value as? Proposition else {
                    return nil
                }
                let transition = i.map({ v, val in val == Literal.True ? v : !v }).reduce(Literal.True, &)
                guard let target = Int(proposition.name[proposition.name.index(after: proposition.name.startIndex)..<proposition.name.endIndex], radix: 10) else {
                    return nil
                }
                solution.addTransition(from: source, to: target, withGuard: transition)
            }
        }
        
        // extract solution: outputs
        for output in specification.outputs {
            for source in 0..<solutionBound {
                let enabled: Logic
                switch self.specification.semantics {
                case .mealy:
                    var clauses: [Logic] = []
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        let parameters: [Logic] = inputPropositions.map({ i[$0]! })
                        let inputProps: [Logic] = [Proposition("s\(source)")] + parameters
                        let outputApplication = FunctionApplication(function: Proposition(output), application: inputProps)
                        guard let value = solver.getValue(expression: outputApplication.accept(visitor: printer)) else {
                            return nil
                        }
                        guard let literal = value as? Literal else {
                            return nil
                        }
                        if literal == Literal.False {
                            let clause = i.map({ v, val in val == Literal.True ? !v : v })
                            clauses.append(clause.reduce(Literal.False, |))
                        }
                    }
                    enabled = clauses.reduce(Literal.True, &)
                case .moore:
                    let outputApplication = FunctionApplication(function: Proposition(output), application: [Proposition("s\(source)")])
                    guard let value = solver.getValue(expression: outputApplication.accept(visitor: printer)) else {
                        return nil
                    }
                    guard let literal = value as? Literal else {
                        return nil
                    }
                    enabled = literal
                }
                solution.add(output: output, inState: source, withGuard: enabled)
            }
        }
        extractionTimer?.stop()
        return solution
    }
}
