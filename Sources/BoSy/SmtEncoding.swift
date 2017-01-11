import Utils
import CAiger

struct SmtEncoding: BoSyEncoding {
    
    let automaton: CoBüchiAutomaton
    let semantics: TransitionSystemType
    let inputs: [String]
    let outputs: [String]
    
    // intermediate results
    var assignments: BooleanAssignment?
    var instance: Logic?
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
    
    func getEncoding(forBound bound: Int) -> String? {
        
        let states = 0..<bound
        
        var smt = String()
        
        // states
        smt.append("(declare-datatypes () ((S \(states.map({ "s\($0)" }).joined(separator: " ")))))\n")
        
        // lambdas
        for q in automaton.states {
            smt.append("(declare-fun \(lambda(q)) (S) Bool)\n")
        }
        
        // lambda sharp
        for q in automaton.states {
            smt.append("(declare-fun \(lambdaSharp(q)) (S) Int)\n")
        }
        
        // tau
        smt.append("(declare-fun tau (S \(inputs.map({ name in "Bool" }).joined(separator: " "))) S)\n")
        
        switch semantics {
        case .Moore:
            for o in outputs {
                smt.append("(declare-fun \(o) (S) Bool)\n")
            }
        case .Mealy:
            for o in outputs {
                smt.append("(declare-fun \(o) (S \(inputs.map({ name in "Bool" }).joined(separator: " "))) Bool)\n")
            }
        }
        for state in automaton.initialStates {
            smt.append("(assert (\(lambda(state)) s0))\n")
        }

        let printer = SmtPrinter()
        
        for q in automaton.states {
            
            let replacer = ReplacingPropositionVisitor(replace: {
                proposition in
                if self.outputs.contains(proposition.name) {
                    switch self.semantics {
                    case .Mealy:
                        let inputProps = [Proposition("s")] + self.inputs.map({Proposition($0)})
                        return FunctionApplication(function: proposition, application: inputProps)
                    case .Moore:
                        return FunctionApplication(function: proposition, application: [Proposition("s")])
                    }
                } else {
                    return nil
                }
            })
            
            if let condition = automaton.safetyConditions[q] {
                let assertion = FunctionApplication(function: lambda(q), application: [Proposition("s")]) --> condition.accept(visitor: replacer)
                smt.append("(assert (forall ((s S) \(inputs.map({ "(\($0) Bool)" }).joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
            guard let outgoing = automaton.transitions[q] else {
                continue
            }
            
            for (qPrime, guardCondition) in outgoing {
                let transitionCondition = requireTransition(q: q, qPrime: qPrime, rejectingStates: automaton.rejectingStates)
                let assertion = (FunctionApplication(function: lambda(q), application: [Proposition("s")]) & guardCondition.accept(visitor: replacer)) --> transitionCondition
                smt.append("(assert (forall ((s S) \(inputs.map({ "(\($0) Bool)" }).joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
        }
        
        smt.append("(check-sat)\n")
        
        return smt
    }
    
    func requireTransition(q: CoBüchiAutomaton.State, qPrime: CoBüchiAutomaton.State, rejectingStates: Set<CoBüchiAutomaton.State>) -> Logic {
        let lambdaNext = FunctionApplication(function: lambda(qPrime), application: [
            FunctionApplication(function: Proposition("tau"), application: [
                Proposition("s")
                ] + inputs.map(Proposition.init) as [Proposition])
            ])
        if automaton.isStateInNonRejectingSCC(q) || automaton.isStateInNonRejectingSCC(qPrime) || !automaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            return lambdaNext
        } else {
            return lambdaNext & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual,
                                                  lhs: FunctionApplication(function: lambdaSharp(qPrime), application: [
                                                    FunctionApplication(function: Proposition("tau"), application: [
                                                        Proposition("s")
                                                        ] + inputs.map(Proposition.init) as [Proposition])
                                                    ]),
                                                  rhs: FunctionApplication(function: lambdaSharp(q), application: [Proposition("s")]))
        }
    }

    func lambda(_ automatonState: CoBüchiAutomaton.State) -> String {
        return "lambda_\(automatonState)"
    }
    
    func lambda(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition(lambda(automatonState))
    }
    
    func lambdaSharp(_ automatonState: CoBüchiAutomaton.State) -> String {
        return "lambdaSharp_\(automatonState)"
    }
    
    func lambdaSharp(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition(lambdaSharp(automatonState))
    }

    mutating func solve(forBound bound: Int) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")
        
        let constraintTimer = options.statistics?.startTimer(phase: .constraintGeneration)
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        constraintTimer?.stop()
        //print(instance)
        
        let solvingTimer = options.statistics?.startTimer(phase: .solving)
        guard let result = z3(smt2: instance) else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        solvingTimer?.stop()
        
        return result == .SAT
    }
    
    func extractSolution() -> BoSySolution? {
        return nil
    }
}
