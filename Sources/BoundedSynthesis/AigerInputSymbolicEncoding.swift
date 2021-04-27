import Automata
import CAiger
import Logic
import Specification
import TransitionSystem
import Utils

/**
 * Bounded Synthesis encoding that encodes the existence of a ralizing
 * solution in AIGER file format used in the reactive synthesis competition.
 */
public class AigerInputSymbolicEncoding<A: Automaton>: SingleParamaterSearch where A: SafetyAcceptance {
    public typealias Parameter = NumberOfAndGatesInAIGER

    let options: BoSyOptions
    let automaton: A
    let specification: SynthesisSpecification
    let stateBits: Int

    // intermediate results
    var assignments: BooleanAssignment?
    var instance: Logic?
    var solutionBound: NumberOfAndGatesInAIGER?

    public init(options: BoSyOptions, automaton: A, specification: SynthesisSpecification, stateBits: Int) {
        precondition(stateBits > 0)
        self.options = options
        self.automaton = automaton
        self.specification = specification
        self.stateBits = stateBits

        solutionBound = nil
    }

    public func solve(forBound bound: NumberOfAndGatesInAIGER) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")

        let constraintTimer = options.statistics?.startTimer(phase: .constraintGeneration)
        let instance = try getEncoding(forBound: bound)
        constraintTimer?.stop()
        // print(instance)

        guard let solver = options.solver?.instance as? QbfSolver else {
            throw BoSyEncodingError.SolvingFailed("solver creation failed")
        }

        let preprocessor: QbfPreprocessor? = QBFPreprocessorInstance.bloqqer.getInstance(preserveAssignments: true)

        let solvingTimer = options.statistics?.startTimer(phase: .solving)
        guard let result = solver.solve(formula: instance, preprocessor: preprocessor) else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        solvingTimer?.stop()

        if case var .sat(assignments) = result {
            // keep top level valuations of solver
            let topLevel = instance as! Quantifier
            let remove = assignments.filter { key, _ in !topLevel.variables.contains(key) }
            for (proposition, _) in remove {
                assignments.removeValue(forKey: proposition)
            }
            self.instance = instance // .eval(assignment: assignments)
            self.assignments = assignments
            solutionBound = bound
            return true
        }

        return false
    }

    public func extractSolution() -> TransitionSystem? {
        let extractionTimer = options.statistics?.startTimer(phase: .solutionExtraction)
        guard let instance = self.instance, let assignments = self.assignments else {
            Logger.default().error("hasSolution() must be true before calling this function")
            return nil
        }
        // print(instance)

        guard let solver = options.solver?.instance as? QbfSolver else {
            return nil
        }

        // print(assignments)

        let reducedInstance = instance.eval(assignment: assignments)
        // have to solve it again without preprocessor to get assignments of remaining top-level variables
        guard let result = solver.solve(formula: reducedInstance, preprocessor: nil) else {
            Logger.default().error("solver failed on instance")
            return nil
        }
        guard case let .sat(additionalAssignments) = result else {
            Logger.default().error("solver gave unexpected result")
            return nil
        }
        let completeAssignment = assignments.merging(additionalAssignments, uniquingKeysWith: { _, _ in fatalError("unique") })

        let aiger = aiger_init()
        for (i, input) in specification.inputs.enumerated() {
            let aiger_var = UInt32(i + 1) << 1
            aiger_add_input(aiger, aiger_var, input)
            // print(aiger_var, input)
        }

        let numInputs = specification.inputs.count
        let numLatches = stateBits
        let numAndGates = solutionBound!.value
        // let maxVariable = numInputs + numLatches + numAndGates + 1

        for latch in 0 ..< numLatches {
            for variable in 0 ... (numInputs + numLatches + numAndGates) {
                let negated = completeAssignment[Proposition("neg_latch_\(latch)")]! == Literal.True
                let prop = Proposition("l_\(latch)_\(variable)")
                if let val = completeAssignment[prop], val == Literal.True {
                    let aiger_var = UInt32(latch + 1 + specification.inputs.count) << 1
                    let next = UInt32(variable << 1 + (negated ? 1 : 0))
                    aiger_add_latch(aiger, aiger_var, next, "l\(latch)")
                    // print("l", aiger_var, next)
                }
            }
        }

        for (_, output) in specification.outputs.enumerated() {
            for variable in 0 ... (numInputs + numLatches + numAndGates) {
                let negated = completeAssignment[Proposition("neg_\(output)")]! == Literal.True
                let prop = Proposition("\(output)_\(variable)")
                if let val = completeAssignment[prop], val == Literal.True {
                    let val = UInt32(variable << 1 + (negated ? 1 : 0))
                    aiger_add_output(aiger, val, output)
                    // print("o", val, output)
                }
            }
        }

        for and_gate in 0 ..< numAndGates {
            var neg_lhs = false
            var neg_rhs = false

            let neg_lhs_prop = Proposition("neg_lhs_\(and_gate)")
            if let val = completeAssignment[neg_lhs_prop], val == Literal.True {
                neg_lhs = true
            }

            let neg_rhs_prop = Proposition("neg_rhs_\(and_gate)")
            if let val = completeAssignment[neg_rhs_prop], val == Literal.True {
                neg_rhs = true
            }

            var lhs = 0
            var rhs = 0

            for variable in 0 ... (numInputs + numLatches + numAndGates) {
                let prop = Proposition("lhs_\(and_gate)_\(variable)")
                if let val = completeAssignment[prop], val == Literal.True {
                    lhs = variable
                    break
                }
            }

            for variable in 0 ... (numInputs + numLatches + numAndGates) {
                let prop = Proposition("rhs_\(and_gate)_\(variable)")
                if let val = completeAssignment[prop], val == Literal.True {
                    rhs = variable
                    break
                }
            }

            let aiger_var = UInt32(and_gate + 1 + specification.inputs.count + stateBits) << 1
            let aiger_lhs = UInt32(lhs << 1 + (neg_lhs ? 1 : 0))
            let aiger_rhs = UInt32(rhs << 1 + (neg_rhs ? 1 : 0))
            aiger_add_and(aiger, aiger_var, aiger_lhs, aiger_rhs)
            // print("\(aiger_var) \(aiger_lhs) \(aiger_rhs)");
        }

        extractionTimer?.stop()

        return AigerSolution(aiger: aiger)
    }

    /**
     * Returns an QBF query that is satisfiable iff there is an AIGER solution
     * with `bound` AND gates.
     */
    func getEncoding(forBound bound: NumberOfAndGatesInAIGER) throws -> Logic {
        // build structure of AIGER file
        // the encoding is as follows
        // AND gate x:
        // * two variables (neg_lhs and neg_rhs) for negation of lhs/rhs input
        // * lhs/rhs: x-1 variables for selecting input unary
        // latch:
        // * current value (universal)
        // * next value: N + I + L variables
        // output:
        // * N + I + L variables

        let numInputs = specification.inputs.count
        let numLatches = stateBits
        let numAndGates = bound.value
        let maxVariable = numInputs + numLatches + numAndGates + 1

        var matrix: [Logic] = []

        // inputs given by environment
        let qbfInputs = specification.inputs.map { Proposition($0) }

        // latches
        let currentLatchVariables = (0 ..< numLatches).map { Proposition("l_\($0)") }
        let nextLatchVariables: [Proposition] = (0 ..< numLatches).reduce([]) {
            val, latch in
            let variables = (0 ... (numInputs + numLatches + numAndGates)).map { other in Proposition("l_\(latch)_\(other)") }
            matrix.append(exactlyOneOf(variables))
            return val + variables + [Proposition("neg_latch_\(latch)")]
        }

        // outputs
        let outputVariables: [Proposition] = specification.outputs.reduce([]) {
            val, output in
            let variables = (0 ... (numInputs + numLatches + numAndGates)).map { other in Proposition("\(output)_\(other)") }
            matrix.append(exactlyOneOf(variables))
            return val + variables + [Proposition("neg_\(output)")]
        }

        // variables encoding and gates
        let andGatePropositions: [Proposition] = (0 ..< numAndGates).reduce([]) { val, and_gate in
            let negation = [Proposition("neg_lhs_\(and_gate)"), Proposition("neg_rhs_\(and_gate)")]
            let lhs = (0 ... (numInputs + numLatches + and_gate)).map {
                other_in in
                Proposition("lhs_\(and_gate)_\(other_in)")
            }
            matrix.append(exactlyOneOf(lhs))
            let rhs = (0 ... (numInputs + numLatches + and_gate)).map {
                other_in in
                Proposition("rhs_\(and_gate)_\(other_in)")
            }
            matrix.append(exactlyOneOf(rhs))
            return val + negation + lhs + rhs
        }

        // print("inputs \(numInputs), latches \(numLatches), Gates \(numAndGates), max \(maxVariable)")

        // print(qbfInputs)
        // print(currentLatchVariables)
        // print(nextLatchVariables)
        // print(outputVariables)
        // print(andGatePropositions)

        // print(matrix)

        // array that maps AIGER variables to the resulting functions
        // 0 -> False
        // 1 -> first input
        // ...

        let valuePropositions = (0 ..< maxVariable).map { i in Proposition("value_\(i)") }

        var values: [Logic] = [Literal.False]
        // inputs
        values += qbfInputs.map { $0 as Logic }
        // current latch values
        values += currentLatchVariables.map { $0 as Logic }
        // and gates
        for and_gate in 0 ..< numAndGates {
            let lhs: Logic = (1 ... (numInputs + numLatches + and_gate)).reduce(Literal.False as Logic) {
                val, variable in
                let prop = Proposition("lhs_\(and_gate)_\(variable)")
                return (prop --> valuePropositions[variable]) & (!prop --> val)
            }
            let rhs: Logic = (1 ... (numInputs + numLatches + and_gate)).reduce(Literal.False as Logic) {
                val, variable in
                let prop = Proposition("rhs_\(and_gate)_\(variable)")
                return (prop --> valuePropositions[variable]) & (!prop --> val)
            }
            let negate_lhs_prop = Proposition("neg_lhs_\(and_gate)")
            let negate_rhs_prop = Proposition("neg_rhs_\(and_gate)")
            values.append(
                (negate_lhs_prop --> !lhs) & (!negate_lhs_prop --> lhs) &
                    (negate_rhs_prop --> !rhs) & (!negate_rhs_prop --> rhs)
            )
        }
        assert(values.count == maxVariable)
        assert(values.count == valuePropositions.count)

        for (prop, val) in zip(valuePropositions, values) {
            matrix.append(prop <-> val)
        }

        let outputValues = specification.outputs.map {
            output -> Logic in
            let value: Logic = (1 ... (numInputs + numLatches + numAndGates)).reduce(Literal.False as Logic) {
                val, variable in
                let prop = Proposition("\(output)_\(variable)")
                return (prop --> valuePropositions[variable]) & (!prop --> val)
            }
            let neg_prop = Proposition("neg_\(output)")
            return (neg_prop --> !value) & (!neg_prop --> value)
        }

        let outputFunctions = specification.outputs.map { output in Proposition("out_func_\(output)") }
        for (prop, val) in zip(outputFunctions, outputValues) {
            matrix.append(prop <-> val)
        }
        let outputMapping = Dictionary(uniqueKeysWithValues: zip(specification.outputs, outputValues))

        let latchNextValues: [Logic] = (0 ..< numLatches).map {
            latch in
            let value: Logic = (1 ... (numInputs + numLatches + numAndGates)).reduce(Literal.False as Logic) {
                val, variable in
                let prop = Proposition("l_\(latch)_\(variable)")
                return (prop --> valuePropositions[variable]) & (!prop --> val)
            }
            let neg_prop = Proposition("neg_latch_\(latch)")
            return (neg_prop --> !value) & (!neg_prop --> value)
        }

        let latchFunctions = (0 ..< numLatches).map { l in Proposition("latch_func_\(l)") }
        for (prop, val) in zip(latchFunctions, latchNextValues) {
            matrix.append(prop <-> val)
        }

        // bounded synthesis encoding
        for state in automaton.initialStates {
            matrix.append(explicitToSymbolic(base: "l", value: 0, bits: stateBits) --> lambda(0, state))
        }

        for source in 0 ..< (1 << stateBits) {
            let precondition = explicitToSymbolic(base: "l", value: source, bits: stateBits)

            let replacer = ReplacingPropositionVisitor(replace: {
                prop in
                if self.specification.outputs.contains(prop.name) {
                    return outputMapping[prop.name]!
                }
                return nil
            })
            for q in automaton.states {
                var conjunct: [Logic] = []

                if let condition = automaton.safetyConditions[q] {
                    conjunct.append(condition.accept(visitor: replacer))
                }

                if let outgoing = automaton.transitions[q] {
                    for (qPrime, guardCondition) in outgoing {
                        let transitionCondition = requireTransition(from: source, q: q, qPrime: qPrime, bound: 1 << stateBits)
                        if guardCondition as? Literal != nil, guardCondition as! Literal == Literal.True {
                            conjunct.append(transitionCondition)
                        } else {
                            conjunct.append(guardCondition.accept(visitor: replacer) --> transitionCondition)
                        }
                    }
                }
                matrix.append(precondition --> (lambda(source, q) --> conjunct.reduce(Literal.True, &)))
            }
        }

        let formula = matrix.reduce(Literal.True, &)

        var lambdas: [Proposition] = []
        for s in 0 ..< (1 << stateBits) {
            for q in automaton.states {
                lambdas.append(lambda(s, q))
            }
        }

        var lambdaSharps: [Proposition] = []
        if automaton is CoBüchiAutomaton {
            for s in 0 ..< (1 << stateBits) {
                for q in automaton.states {
                    lambdaSharps.append(lambdaSharp(s, q))
                }
            }
        }

        var qbf: Logic = Quantifier(.Exists, variables: valuePropositions + outputFunctions + latchFunctions, scope: formula)
        qbf = Quantifier(.Forall, variables: qbfInputs + currentLatchVariables, scope: qbf)
        qbf = Quantifier(.Exists, variables: nextLatchVariables + outputVariables + andGatePropositions + lambdas + lambdaSharps, scope: qbf)

        let boundednessCheck = BoundednessVisitor()
        assert(qbf.accept(visitor: boundednessCheck))

        let removeComparable = RemoveComparableVisitor(bound: 1 << stateBits)
        qbf = qbf.accept(visitor: removeComparable)

        return qbf
    }

    func requireTransition(from s: Int, q: A.State, qPrime: A.State, bound: Int) -> Logic {
        let validTransition: [Logic]

        guard let coBüchi = automaton as? CoBüchiAutomaton else {
            // safety automaton
            validTransition = (0 ..< bound).map {
                sPrime in
                explicitToSymbolic(base: "latch_func", value: sPrime, bits: self.stateBits) --> lambda(sPrime, qPrime)
            }
            return validTransition.reduce(Literal.True, &)
        }
        if coBüchi.isStateInNonRejectingSCC(q as! CoBüchiAutomaton.State) || coBüchi.isStateInNonRejectingSCC(qPrime as! CoBüchiAutomaton.State) || !coBüchi.isInSameSCC(q as! CoBüchiAutomaton.State, qPrime as! CoBüchiAutomaton.State) {
            // no need for comparator constrain
            validTransition = (0 ..< bound).map {
                sPrime in
                explicitToSymbolic(base: "latch_func", value: sPrime, bits: self.stateBits) --> lambda(sPrime, qPrime)
            }
        } else {
            validTransition = (0 ..< bound).map {
                sPrime in
                explicitToSymbolic(base: "latch_func", value: sPrime, bits: self.stateBits) -->
                    (lambda(sPrime, qPrime) & BooleanComparator(coBüchi.rejectingStates.contains(qPrime as! CoBüchiAutomaton.State) ? .Less : .LessOrEqual, lhs: lambdaSharp(sPrime, qPrime), rhs: lambdaSharp(s, q)))
            }
        }
        return validTransition.reduce(Literal.True, &)
    }

    func lambda(_ state: Int, _ automatonState: A.State) -> Proposition {
        Proposition("λ_\(state)_\(automatonState)")
    }

    func lambdaSharp(_ state: Int, _ automatonState: A.State) -> Proposition {
        Proposition("λ#_\(state)_\(automatonState)")
    }

    /**
     * Encodes the constraint that exactly one proposition is true
     */
    func exactlyOneOf(_ propositions: [Proposition]) -> Logic {
        let atLeastOne: Logic = propositions.reduce(Literal.False) { disjunct, prop in
            disjunct | prop
        }
        let atMostOne: Logic = propositions.enumerated().reduce(Literal.True as Logic) {
            conjunct, tupl in
            let (i, prop) = tupl
            let disjunct: Logic = propositions[(i + 1)...].reduce(Literal.True) {
                val, other in
                val & (!prop | !other)
            }
            return conjunct & disjunct
        }
        return atLeastOne & atMostOne
    }

    func explicitToSymbolic(base: String, value: Int, bits: Int) -> Logic {
        var and: [Logic] = []
        for (i, bit) in binaryFrom(value, bits: bits).enumerated() {
            let prop = Proposition("\(base)_\(i)")
            and.append(bit == "1" ? prop : !prop)
        }
        return and.reduce(Literal.True, &)
    }
}
