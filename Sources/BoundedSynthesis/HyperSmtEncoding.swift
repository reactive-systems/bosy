import Utils
import CAiger
import Logic
import Automata
import Specification
import TransitionSystem
import LTL

public struct HyperSmtEncoding: BoSyEncoding {
    
    let options: BoSyOptions
    let automaton: CoBüchiAutomaton
    let specification: SynthesisSpecification
    
    // intermediate results
    var assignments: BooleanAssignment?
    var instance: Logic?
    var solutionBound: Int
    var solver: SmtSolver?
    
    public init(options: BoSyOptions, automaton: CoBüchiAutomaton, specification: SynthesisSpecification) {
        self.options = options
        self.automaton = automaton
        self.specification = specification
        
        assignments = nil
        instance = nil
        solutionBound = 0
    }
    
    func getEncoding(forBound bound: Int) -> String? {

        guard specification.guarantees.count == 1,
            specification.assumptions.count == 0 else {
                fatalError()
        }
        guard let hyperltl = specification.guarantees.first else {
            fatalError()
        }
        let pathVariables = hyperltl.pathVariables
        guard pathVariables.count > 1 else {
            fatalError()
        }
        
        let states = 0..<bound
        
        var smt = "(set-logic UFDTLIA)\n"
        
        // states
        smt.append("(declare-datatypes () ((S \(states.map({ "(s\($0))" }).joined(separator: " ")))))\n")
        
        // lambdas
        for q in automaton.states {
            smt.append("(declare-fun \(lambda(q)) (\(pathVariables.map({ _ in "S" }).joined(separator: " "))) Bool)\n")
        }
        
        // lambda sharp
        for q in automaton.states {
            smt.append("(declare-fun \(lambdaSharp(q)) (\(pathVariables.map({ _ in "S" }).joined(separator: " "))) Int)\n")
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
        guard automaton.initialStates.count == 1 else {
            fatalError()
        }
        guard let automatonInitial = automaton.initialStates.first else {
            fatalError()
        }
        smt.append("(assert (\(lambda(automatonInitial)) \(pathVariables.map({ _ in "s0" }).joined(separator: " "))))\n")

        let printer = SmtPrinter()

        var inputs: [LTLPathVariable: [Proposition]] = [:]
        for variable in pathVariables {
            inputs[variable] = specification.inputs.map({ input in Proposition("\(input)_\(variable)_") })
        }
        print(inputs)

        var outputs: [LTLPathVariable: [Proposition]] = [:]
        for variable in pathVariables {
            outputs[variable] = specification.outputs.map({ output in Proposition(LTL.pathProposition(LTLAtomicProposition(name: output), variable).description) })
        }
        print(outputs)

        let pstates: [Proposition] = pathVariables.map({ variable in Proposition("s_\(variable)_") })
        print(pstates)
        
        for q in automaton.states {
            
            let replacer = ReplacingPropositionVisitor(replace: {
                proposition in
                for (variable, variableOutputs) in outputs {
                    if variableOutputs.contains(proposition) {
                        let base = proposition.name.replacingOccurrences(of: "[\(variable)]", with: "")
                        switch self.specification.semantics {
                        case .mealy:
                            let inputProps = [Proposition("s_\(variable)_")] + inputs[variable]!
                            return FunctionApplication(function: Proposition(base), application: inputProps)
                        case .moore:
                            return FunctionApplication(function: Proposition(base), application: [Proposition("s_\(variable)_")])
                        }
                    }
                }
                // has to be an input
                // transform to SMT-suitable format
                var p = proposition
                for variable in pathVariables {
                    p.name = p.name.replacingOccurrences(of: "[\(variable)]", with: "_\(variable)_")
                }
                return p
            })
            
            if let condition = automaton.safetyConditions[q] {
                let assertion = FunctionApplication(function: lambda(q), application: pstates) --> condition.accept(visitor: replacer)
                smt.append("(assert (forall (\(pstates.map({ "(\($0) S)" }).joined(separator: " ")) \(inputs.flatMap({ $0.value }).map({ "(\($0) Bool)" }).joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
            guard let outgoing = automaton.transitions[q] else {
                continue
            }
            
            for (qPrime, guardCondition) in outgoing {
                let transitionCondition = requireTransition(q: q, qPrime: qPrime, rejectingStates: automaton.rejectingStates, variables: pathVariables, inputs: inputs)
                let assertion = (FunctionApplication(function: lambda(q), application: pstates) & guardCondition.accept(visitor: replacer)) --> transitionCondition
                smt.append("(assert (forall (\(pstates.map({ "(\($0) S)" }).joined(separator: " ")) \(inputs.flatMap({ $0.value }).map({ "(\($0) Bool)" }).joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
        }

        //print(smt)
        
        return smt
    }
    
    func requireTransition(q: CoBüchiAutomaton.State, qPrime: CoBüchiAutomaton.State, rejectingStates: Set<CoBüchiAutomaton.State>, variables: [LTLPathVariable], inputs: [LTLPathVariable: [Proposition]]) -> Logic {
        let lambdaNext = FunctionApplication(function: lambda(qPrime), application: variables.map({
            variable in
            return FunctionApplication(function: Proposition("tau"), application: [
                Proposition("s_\(variable)_")
                ] + inputs[variable]!)
        }))
        if automaton.isStateInNonRejectingSCC(q) || automaton.isStateInNonRejectingSCC(qPrime) || !automaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            return lambdaNext
        } else {
            return lambdaNext & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual,
                                                  lhs: FunctionApplication(function: lambdaSharp(qPrime), application: variables.map({
                                                        variable in
                                                        return FunctionApplication(function: Proposition("tau"), application: [
                                                            Proposition("s_\(variable)_")
                                                        ] + inputs[variable]!)
                                                  })),
                                                  rhs: FunctionApplication(function: lambdaSharp(q), application: variables.map({ Proposition("s_\($0)_") })))
        }
    }
    
    func lambda(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("lambda_\(automatonState)")
    }
    
    func lambdaSharp(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("lambdaSharp_\(automatonState)")
    }

    public mutating func solve(forBound bound: Int) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")
        
        let constraintTimer = options.statistics?.startTimer(phase: .constraintGeneration)
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        constraintTimer?.stop()
        //print(instance)
        
        guard let solver = SolverInstance.z3.instance as? SmtSolver else {
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
    
    public func extractSolution() -> TransitionSystem? {
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
                guard let target = Int(proposition.name.substring(from: proposition.name.index(after: proposition.name.startIndex)), radix: 10) else {
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
