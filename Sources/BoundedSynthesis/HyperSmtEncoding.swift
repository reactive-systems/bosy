import Automata
import CAiger
import Logic
import LTL
import Specification
import TransitionSystem
import Utils

/**
 * Bounded Synthesis encoding for synthesizing system strategies given
 * a universal HyperLTL specification.
 * Uses an SMT solver as backend.
 */
public class HyperSmtEncoding: BoSyEncoding {
    let options: BoSyOptions
    let linearAutomaton: CoBüchiAutomaton
    let hyperAutomaton: CoBüchiAutomaton
    let specification: SynthesisSpecification

    // intermediate results
    var assignments: BooleanAssignment?
    var instance: Logic?
    var solutionBound: Int
    var solver: SmtSolver?

    public init(options: BoSyOptions, linearAutomaton: CoBüchiAutomaton, hyperAutomaton: CoBüchiAutomaton, specification: SynthesisSpecification) {
        self.options = options
        self.linearAutomaton = linearAutomaton
        self.hyperAutomaton = hyperAutomaton
        self.specification = specification

        assignments = nil
        instance = nil
        solutionBound = 0
    }

    func getEncoding(forBound bound: Int) -> String? {
        let states = 0 ..< bound

        var smt = "(set-logic UFDTLIA)\n"

        // states
        smt.append("(declare-datatypes () ((S \(states.map { "(s\($0))" }.joined(separator: " ")))))\n")

        // tau
        smt.append("(declare-fun tau_ (S \(specification.inputs.map { _ in "Bool" }.joined(separator: " "))) S)\n")

        switch specification.semantics {
        case .moore:
            for o in specification.outputs {
                smt.append("(declare-fun \(o) (S) Bool)\n")
            }
        case .mealy:
            for o in specification.outputs {
                smt.append("(declare-fun \(o) (S \(specification.inputs.map { _ in "Bool" }.joined(separator: " "))) Bool)\n")
            }
        }

        encodeLinearAutomaton(smt: &smt)
        encodeHyperAutomaton(smt: &smt)

        print(smt)
        print()

        return smt
    }

    func encodeLinearAutomaton(smt: inout String) {
        // lambdas
        for q in linearAutomaton.states {
            smt.append("(declare-fun \(lambda(q)) (S) Bool)\n")
        }

        // lambda sharp
        for q in linearAutomaton.states {
            smt.append("(declare-fun \(lambdaSharp(q)) (S) Int)\n")
        }

        // tau
//        smt.append("(declare-fun tau_ (S \(specification.inputs.map { _ in "Bool" }.joined(separator: " "))) S)\n")

//        switch specification.semantics {
//        case .moore:
//            for o in specification.outputs {
//                smt.append("(declare-fun \(o) (S) Bool)\n")
//            }
//        case .mealy:
//            for o in specification.outputs {
//                smt.append("(declare-fun \(o) (S \(specification.inputs.map { _ in "Bool" }.joined(separator: " "))) Bool)\n")
//            }
//        }
        for state in linearAutomaton.initialStates {
            smt.append("(assert (\(lambda(state)) s0))\n")
        }

        let printer = SmtPrinter()

        for q in linearAutomaton.states {
            let replacer = ReplacingPropositionVisitor(replace: {
                proposition in
                if self.specification.outputs.contains(proposition.name) {
                    switch self.specification.semantics {
                    case .mealy:
                        let inputProps = [Proposition("s")] + self.specification.inputs.map { Proposition($0) }
                        return FunctionApplication(function: proposition, application: inputProps)
                    case .moore:
                        return FunctionApplication(function: proposition, application: [Proposition("s")])
                    }
                } else {
                    return nil
                }
            })

            if let condition = linearAutomaton.safetyConditions[q] {
                let assertion = FunctionApplication(function: lambda(q), application: [Proposition("s")]) --> condition.accept(visitor: replacer)
                smt.append("(assert (forall ((s S) \(specification.inputs.map { "(\($0) Bool)" }.joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
            guard let outgoing = linearAutomaton.transitions[q] else {
                continue
            }

            for (qPrime, guardCondition) in outgoing {
                let transitionCondition = requireTransition(q: q, qPrime: qPrime, rejectingStates: linearAutomaton.rejectingStates)
                let assertion = (FunctionApplication(function: lambda(q), application: [Proposition("s")]) & guardCondition.accept(visitor: replacer)) --> transitionCondition
                smt.append("(assert (forall ((s S) \(specification.inputs.map { "(\($0) Bool)" }.joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
        }
    }

    func requireTransition(q: CoBüchiAutomaton.State, qPrime: CoBüchiAutomaton.State, rejectingStates: Set<CoBüchiAutomaton.State>) -> Logic {
        let lambdaNext = FunctionApplication(function: lambda(qPrime), application: [
            FunctionApplication(function: Proposition("tau_"), application: [
                Proposition("s"),
            ] + specification.inputs.map(Proposition.init) as [Proposition]),
        ])
        if linearAutomaton.isStateInNonRejectingSCC(q) || linearAutomaton.isStateInNonRejectingSCC(qPrime) || !linearAutomaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            return lambdaNext
        } else {
            return lambdaNext & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual,
                                                  lhs: FunctionApplication(function: lambdaSharp(qPrime), application: [
                                                      FunctionApplication(function: Proposition("tau_"), application: [
                                                          Proposition("s"),
                                                      ] + specification.inputs.map(Proposition.init) as [Proposition]),
                                                  ]),
                                                  rhs: FunctionApplication(function: lambdaSharp(q), application: [Proposition("s")]))
        }
    }

    func lambda(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        Proposition("lambda_\(automatonState)")
    }

    func lambdaSharp(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        Proposition("lambdaSharp_\(automatonState)")
    }

    func encodeHyperAutomaton(smt: inout String) {
        let hyperltl = specification.hyperPrenex
        let pathVariables = hyperltl.pathVariables
        guard pathVariables.count > 1 else {
            fatalError("HyperLTL specifications should have at least 2 path variables")
        }

        // lambdas
        for q in hyperAutomaton.states {
            smt.append("(declare-fun \(lambdaHyper(q)) (\(pathVariables.map { _ in "S" }.joined(separator: " "))) Bool)\n")
        }

        // lambda sharp
        for q in hyperAutomaton.states {
            smt.append("(declare-fun \(lambdaHyperSharp(q)) (\(pathVariables.map { _ in "S" }.joined(separator: " "))) Int)\n")
        }

        guard hyperAutomaton.initialStates.count == 1 else {
            fatalError()
        }
        guard let automatonInitial = hyperAutomaton.initialStates.first else {
            fatalError()
        }
        smt.append("(assert (\(lambdaHyper(automatonInitial)) \(pathVariables.map { _ in "s0" }.joined(separator: " "))))\n")

        let printer = SmtPrinter()

        var inputs: [LTLPathVariable: [Proposition]] = [:]
        for variable in pathVariables {
            inputs[variable] = specification.inputs.map { input in Proposition("\(input)_\(variable)_") }
        }
        // print(inputs)

        var outputs: [LTLPathVariable: [Proposition]] = [:]
        for variable in pathVariables {
            outputs[variable] = specification.outputs.map { output in Proposition(LTL.pathProposition(LTLAtomicProposition(name: output), variable).description) }
        }
        // print(outputs)

        let pstates: [Proposition] = pathVariables.map { variable in Proposition("s_\(variable)_") }
        // print(pstates)

        for q in hyperAutomaton.states {
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

            if let condition = hyperAutomaton.safetyConditions[q] {
                let assertion = FunctionApplication(function: lambdaHyper(q), application: pstates) --> condition.accept(visitor: replacer)
                smt.append("(assert (forall (\(pstates.map { "(\($0) S)" }.joined(separator: " ")) \(inputs.flatMap { $0.value }.map { "(\($0) Bool)" }.joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
            guard let outgoing = hyperAutomaton.transitions[q] else {
                continue
            }

            for (qPrime, guardCondition) in outgoing {
                let transitionCondition = requireHyperTransition(q: q, qPrime: qPrime, rejectingStates: hyperAutomaton.rejectingStates, variables: pathVariables, inputs: inputs)
                let assertion = (FunctionApplication(function: lambdaHyper(q), application: pstates) & guardCondition.accept(visitor: replacer)) --> transitionCondition
                smt.append("(assert (forall (\(pstates.map { "(\($0) S)" }.joined(separator: " ")) \(inputs.flatMap { $0.value }.map { "(\($0) Bool)" }.joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
        }
    }

    private func requireHyperTransition(q: CoBüchiAutomaton.State, qPrime: CoBüchiAutomaton.State, rejectingStates: Set<CoBüchiAutomaton.State>, variables: [LTLPathVariable], inputs: [LTLPathVariable: [Proposition]]) -> Logic {
        let lambdaNext = FunctionApplication(function: lambdaHyper(qPrime), application: variables.map {
            variable in
            FunctionApplication(function: Proposition("tau_"), application: [
                Proposition("s_\(variable)_"),
            ] + inputs[variable]!)
        })
        if hyperAutomaton.isStateInNonRejectingSCC(q) || hyperAutomaton.isStateInNonRejectingSCC(qPrime) || !hyperAutomaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            return lambdaNext
        } else {
            return lambdaNext & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual,
                                                  lhs: FunctionApplication(function: lambdaHyperSharp(qPrime), application: variables.map {
                                                      variable in
                                                      FunctionApplication(function: Proposition("tau_"), application: [
                                                          Proposition("s_\(variable)_"),
                                                      ] + inputs[variable]!)
                                                  }),
                                                  rhs: FunctionApplication(function: lambdaHyperSharp(q), application: variables.map { Proposition("s_\($0)_") }))
        }
    }

    private func lambdaHyper(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        Proposition("lambda_\(automatonState)")
    }

    private func lambdaHyperSharp(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        Proposition("lambdaSharp_\(automatonState)")
    }

    public func solve(forBound bound: Int) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")

        let constraintTimer = options.statistics?.startTimer(phase: .constraintGeneration)
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        constraintTimer?.stop()
        // print(instance)

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
            solutionBound = bound
        }

        return result == .sat
    }

    public func extractSolution() -> TransitionSystem? {
        guard let solver = solver else {
            return nil
        }

        let printer = SmtPrinter()

        let extractionTimer = options.statistics?.startTimer(phase: .solutionExtraction)
        let inputPropositions: [Proposition] = specification.inputs.map { Proposition($0) }

        var solution = ExplicitStateSolution(bound: solutionBound, specification: specification)

        // extract solution: transition relation
        for source in 0 ..< solutionBound {
            for i in allBooleanAssignments(variables: inputPropositions) {
                let parameters = inputPropositions.map { i[$0]! }
                let tauApplication = FunctionApplication(function: Proposition("tau_"), application: [Proposition("s\(source)")] as [Logic] + parameters)
                guard let value = solver.getValue(expression: tauApplication.accept(visitor: printer)) else {
                    return nil
                }
                guard let proposition = value as? Proposition else {
                    return nil
                }
                let transition = i.map { v, val in val == Literal.True ? v : !v }.reduce(Literal.True, &)
                guard let target = Int(proposition.name[proposition.name.index(after: proposition.name.startIndex)...], radix: 10) else {
                    return nil
                }
                solution.addTransition(from: source, to: target, withGuard: transition)
            }
        }

        // extract solution: outputs
        for output in specification.outputs {
            for source in 0 ..< solutionBound {
                let enabled: Logic
                switch specification.semantics {
                case .mealy:
                    var clauses: [Logic] = []
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        let parameters: [Logic] = inputPropositions.map { i[$0]! }
                        let inputProps: [Logic] = [Proposition("s\(source)")] + parameters
                        let outputApplication = FunctionApplication(function: Proposition(output), application: inputProps)
                        guard let value = solver.getValue(expression: outputApplication.accept(visitor: printer)) else {
                            return nil
                        }
                        guard let literal = value as? Literal else {
                            return nil
                        }
                        if literal == Literal.False {
                            let clause = i.map { v, val in val == Literal.True ? !v : v }
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
