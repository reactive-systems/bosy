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
public class HyperStateSymbolicEncoding: BoSyEncoding {
    let options: BoSyOptions
    let linearAutomaton: CoBüchiAutomaton
    let hyperAutomaton: CoBüchiAutomaton
    let specification: SynthesisSpecification

    public init(options: BoSyOptions, linearAutomaton: CoBüchiAutomaton, hyperAutomaton: CoBüchiAutomaton, specification: SynthesisSpecification) {
        self.options = options
        self.linearAutomaton = linearAutomaton
        self.hyperAutomaton = hyperAutomaton
        self.specification = specification
    }

    func getEncoding(forBound bound: Int) -> Logic? {
        let states = 0 ..< bound
        let numBits = numBitsNeeded(bound)

        var preconditions: [Logic] = []
        var matrix: [Logic] = []

        let statePropositions: [Proposition] = (0 ..< numBits).map { bit in Proposition("s\(bit)") }
        let nextStatePropositions: [Proposition] = (0 ..< numBits).map { bit in Proposition("sp\(bit)") }
        let tauPropositions: [Proposition] = (0 ..< numBits).map { bit in tau(bit: bit) }
        let inputPropositions: [Proposition] = specification.inputs.map(Proposition.init)
        let outputPropositions: [Proposition] = specification.outputs.map(Proposition.init)

        for i in bound ..< (1 << numBits) {
            preconditions.append(!explicitToSymbolic(base: "s", value: i, bits: numBits))
            preconditions.append(!explicitToSymbolic(base: "sp", value: i, bits: numBits))
            matrix.append(!explicitToSymbolic(base: "t_", value: i, bits: numBits, parameters: statePropositions + inputPropositions))
        }

        encodeLinearAutomaton(bound: bound, numBits: numBits, statePropositions: statePropositions, nextStatePropositions: nextStatePropositions, tauPropositions: tauPropositions, inputPropositions: inputPropositions, outputPropositions: outputPropositions, matrix: &matrix)
        let (hyperStates, hyperNextStates, hyperIns) = encodeHyperAutomaton(bound: bound, numBits: numBits, tauPropositions: tauPropositions, matrix: &matrix)

        for conjunct in matrix {
            print(conjunct)
        }

        let formula: Logic = preconditions.reduce(Literal.True, &) --> matrix.reduce(Literal.True, &)

        let universalQuantified: Logic = Quantifier(.Forall, variables: statePropositions + nextStatePropositions + inputPropositions + hyperStates.reduce([], +) + hyperNextStates.reduce([], +) + hyperIns.reduce([], +), scope: formula)
        let outputQuantification: Logic = Quantifier(.Exists, variables: outputPropositions, scope: universalQuantified, arity: specification.semantics == .mealy ? numBitsNeeded(states.count) + specification.inputs.count : numBitsNeeded(states.count))
        let tauQuantification: Logic = Quantifier(.Exists, variables: tauPropositions, scope: outputQuantification, arity: numBitsNeeded(states.count) + specification.inputs.count)

        let lambdaPropositions: [Proposition] = linearAutomaton.states.map { lambdaProposition($0) }
        let lambdaSharpPropositions: [Proposition] = linearAutomaton.states.map { lambdaSharpProposition($0) }
        let lambdaQuantification: Logic = Quantifier(.Exists, variables: lambdaPropositions + lambdaSharpPropositions, scope: tauQuantification, arity: numBitsNeeded(states.count))

        let lambdaHyperPropositions: [Proposition] = hyperAutomaton.states.map { lambdaHyperProposition($0) }
        let lambdaHyperSharpPropositions: [Proposition] = hyperAutomaton.states.map { lambdaHyperSharpProposition($0) }
        let lambdaHyperQuantification: Logic = Quantifier(.Exists, variables: lambdaHyperPropositions + lambdaHyperSharpPropositions, scope: lambdaQuantification, arity: numBitsNeeded(states.count) * specification.hyperPrenex.pathVariables.count)

        let boundednessCheck = BoundednessVisitor()
        assert(lambdaHyperQuantification.accept(visitor: boundednessCheck))

        let removeComparable = RemoveComparableVisitor(bound: bound)
        let result = lambdaHyperQuantification.accept(visitor: removeComparable)

        print(result)

        return result
    }

    func encodeLinearAutomaton(bound: Int, numBits: Int, statePropositions: [Proposition], nextStatePropositions: [Proposition], tauPropositions: [Proposition], inputPropositions: [Proposition], outputPropositions _: [Proposition], matrix: inout [Logic]) {
        let tauApplications: [FunctionApplication] = tauPropositions.map { FunctionApplication(function: $0, application: statePropositions + inputPropositions) }

        // initial states
        let premise = explicitToSymbolic(base: "s", value: 0, bits: numBits)
        for q in linearAutomaton.initialStates {
            matrix.append(premise --> lambda(q, states: statePropositions))
        }

        for q in linearAutomaton.states {
            var conjunct: [Logic] = []

            let replacer = ReplacingPropositionVisitor(replace: {
                proposition in
                if self.specification.outputs.contains(proposition.name) {
                    let dependencies = self.specification.semantics == .mealy ? statePropositions + inputPropositions : statePropositions
                    return FunctionApplication(function: proposition, application: dependencies)
                } else {
                    return nil
                }
            })

            if let condition = linearAutomaton.safetyConditions[q] {
                conjunct.append(condition.accept(visitor: replacer))
            }
            guard let outgoing = linearAutomaton.transitions[q] else {
                assert(conjunct.isEmpty)
                continue
            }

            for (qPrime, guardCondition) in outgoing {
                let transitionCondition = requireTransition(q: q, qPrime: qPrime, bound: bound, rejectingStates: linearAutomaton.rejectingStates, states: statePropositions, nextStates: nextStatePropositions, taus: tauApplications)
                if guardCondition as? Literal != nil, guardCondition as! Literal == Literal.True {
                    conjunct.append(transitionCondition)
                } else {
                    conjunct.append(guardCondition.accept(visitor: replacer) --> transitionCondition)
                }
            }
            matrix.append(lambda(q, states: statePropositions) --> conjunct.reduce(Literal.True, &))
        }
    }

    func requireTransition(q: CoBüchiAutomaton.State, qPrime: CoBüchiAutomaton.State, bound _: Int, rejectingStates: Set<CoBüchiAutomaton.State>, states: [Proposition], nextStates: [Proposition], taus: [FunctionApplication]) -> Logic {
        if linearAutomaton.isStateInNonRejectingSCC(q) || linearAutomaton.isStateInNonRejectingSCC(qPrime) || !linearAutomaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            return tauNextStateAssertion(states: nextStates, taus: taus) --> lambda(qPrime, states: nextStates)
        } else {
            return tauNextStateAssertion(states: nextStates, taus: taus) -->
                (lambda(qPrime, states: nextStates) & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual, lhs: lambdaSharp(qPrime, states: nextStates), rhs: lambdaSharp(q, states: states)))
        }
    }

    func explicitToSymbolic(base: String, value: Int, bits: Int, parameters: [Proposition]? = nil) -> Logic {
        var and: [Logic] = []
        for (i, bit) in binaryFrom(value, bits: bits).enumerated() {
            let prop: Logic
            if let parameters = parameters {
                prop = FunctionApplication(function: Proposition("\(base)\(i)"), application: parameters)
            } else {
                prop = Proposition("\(base)\(i)")
            }
            and.append(bit == "1" ? prop : !prop)
        }
        return and.reduce(Literal.True, &)
    }

    func tauNextStateAssertion(states: [Proposition], taus: [FunctionApplication]) -> Logic {
        assert(states.count == taus.count)
        var assertion: [Logic] = []
        for (state, tau) in zip(states, taus) {
            assertion.append(state <-> tau)
        }
        return assertion.reduce(Literal.True, &)
    }

    func lambdaProposition(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        Proposition("l_\(automatonState)")
    }

    func lambda(_ automatonState: CoBüchiAutomaton.State, states: [Proposition]) -> FunctionApplication {
        FunctionApplication(function: lambdaProposition(automatonState), application: states)
    }

    func lambdaSharpProposition(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        Proposition("ls_\(automatonState)")
    }

    func lambdaSharp(_ automatonState: CoBüchiAutomaton.State, states: [Proposition]) -> FunctionApplication {
        FunctionApplication(function: lambdaSharpProposition(automatonState), application: states)
    }

    func tau(bit: Int) -> Proposition {
        Proposition("t_\(bit)")
    }

    func output(_ name: String, forState state: Int) -> String {
        "\(name)_\(state)"
    }

    func encodeHyperAutomaton(bound: Int, numBits: Int, tauPropositions: [Proposition], matrix: inout [Logic]) -> (states: [[Proposition]], nextStates: [[Proposition]], inputs: [[Proposition]]) {
        let hyperltl = specification.hyperPrenex
        let pathVariables = hyperltl.pathVariables
        guard pathVariables.count > 1 else {
            fatalError("HyperLTL specifications should have at least 2 path variables")
        }

        assert(bound == 1 && numBits == 1 || bound == 1 << numBits, "\(bound) \(numBits)")

        guard hyperAutomaton.initialStates.count == 1 else {
            fatalError()
        }

        let statePropositions: [[Proposition]] = pathVariables.map { pvar in (0 ..< numBits).map { bit in Proposition("s_\(pvar)_\(bit)") } }
        let nextStatePropositions: [[Proposition]] = pathVariables.map { pvar in (0 ..< numBits).map { bit in Proposition("sp_\(pvar)_\(bit)") } }

        // initial states
        let premises = pathVariables.map { explicitToSymbolic(base: "s_\($0)_", value: 0, bits: numBits) }.reduce(Literal.True, &)
        for q in hyperAutomaton.initialStates {
            matrix.append(premises --> lambdaHyper(q, states: statePropositions))
        }

        var inputs: [[Proposition]] = []
        for variable in pathVariables {
            inputs.append(specification.inputs.map { input in Proposition(LTL.pathProposition(LTLAtomicProposition(name: input), variable).description) })
        }
        print(inputs)

        var outputs: [[Proposition]] = []
        for variable in pathVariables {
            outputs.append(specification.outputs.map { output in Proposition(LTL.pathProposition(LTLAtomicProposition(name: output), variable).description) })
        }
        print(outputs)

        let tauApplications: [[FunctionApplication]] = pathVariables.enumerated().map { i, _ in tauPropositions.map { FunctionApplication(function: $0, application: statePropositions[i] + inputs[i]) } }

        // let pstates: [Proposition] = pathVariables.map({ variable in Proposition("s_\(variable)_") })
        // print(pstates)

        for q in hyperAutomaton.states {
            var conjunct: [Logic] = []

            let replacer = ReplacingPropositionVisitor(replace: {
                proposition in
                for (i, variableOutputs) in outputs.enumerated() {
                    if variableOutputs.contains(proposition) {
                        let base = proposition.name.replacingOccurrences(of: "[\(pathVariables[i])]", with: "")
                        let dependencies = self.specification.semantics == .mealy ? statePropositions[i] + inputs[i] : statePropositions[i]
                        return FunctionApplication(function: Proposition(base), application: dependencies)
                    }
                }
                // has to be an input
                return nil
            })

            if let condition = hyperAutomaton.safetyConditions[q] {
                conjunct.append(condition.accept(visitor: replacer))
            }
            guard let outgoing = hyperAutomaton.transitions[q] else {
                assert(conjunct.isEmpty)
                continue
            }

            for (qPrime, guardCondition) in outgoing {
                let transitionCondition = requireHyperTransition(q: q, qPrime: qPrime, bound: bound, rejectingStates: hyperAutomaton.rejectingStates, states: statePropositions, nextStates: nextStatePropositions, taus: tauApplications)
                if guardCondition as? Literal != nil, guardCondition as! Literal == Literal.True {
                    conjunct.append(transitionCondition)
                } else {
                    conjunct.append(guardCondition.accept(visitor: replacer) --> transitionCondition)
                }
            }
            matrix.append(lambdaHyper(q, states: statePropositions) --> conjunct.reduce(Literal.True, &))
        }
        return (statePropositions, nextStatePropositions, inputs)
    }

    func requireHyperTransition(q: CoBüchiAutomaton.State, qPrime: CoBüchiAutomaton.State, bound _: Int, rejectingStates: Set<CoBüchiAutomaton.State>, states: [[Proposition]], nextStates: [[Proposition]], taus: [[FunctionApplication]]) -> Logic {
        if hyperAutomaton.isStateInNonRejectingSCC(q) || hyperAutomaton.isStateInNonRejectingSCC(qPrime) || !hyperAutomaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            return tauHyperNextStateAssertion(states: nextStates, taus: taus) --> lambdaHyper(qPrime, states: nextStates)
        } else {
            return tauHyperNextStateAssertion(states: nextStates, taus: taus) -->
                (lambdaHyper(qPrime, states: nextStates) & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual, lhs: lambdaHyperSharp(qPrime, states: nextStates), rhs: lambdaHyperSharp(q, states: states)))
        }
    }

    func tauHyperNextStateAssertion(states: [[Proposition]], taus: [[FunctionApplication]]) -> Logic {
        assert(states.count == taus.count)
        return zip(states, taus).map { states, taus in tauNextStateAssertion(states: states, taus: taus) }.reduce(Literal.True, &)
    }

    func lambdaHyperProposition(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        Proposition("l_H_\(automatonState)")
    }

    func lambdaHyper(_ automatonState: CoBüchiAutomaton.State, states: [[Proposition]]) -> FunctionApplication {
        FunctionApplication(function: lambdaHyperProposition(automatonState), application: states.reduce([], +))
    }

    func lambdaHyperSharpProposition(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        Proposition("ls_h_\(automatonState)")
    }

    func lambdaHyperSharp(_ automatonState: CoBüchiAutomaton.State, states: [[Proposition]]) -> FunctionApplication {
        FunctionApplication(function: lambdaHyperSharpProposition(automatonState), application: states.reduce([], +))
    }

    public func solve(forBound bound: Int) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")

        let constraintTimer = options.statistics?.startTimer(phase: .constraintGeneration)
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        constraintTimer?.stop()
        // print(instance)

        /* let dqdimacsVisitor = DQDIMACSVisitor(formula: instance)
         let encodedFormula = dqdimacsVisitor.description
         print(encodedFormula)
         exit(1) */

        guard let solver = options.solver?.instance as? DqbfSolver else {
            throw BoSyEncodingError.SolvingFailed("solver creation failed")
        }

        let solvingTimer = options.statistics?.startTimer(phase: .solving)
        let preprocessor: QbfPreprocessor? = options.qbfPreprocessor.map { $0.getInstance(preserveAssignments: false) }
        guard let result = solver.solve(formula: instance, preprocessor: preprocessor) else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        solvingTimer?.stop()

        return result == .sat
    }

    public func extractSolution() -> TransitionSystem? {
        nil
    }
}
