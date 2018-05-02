import Utils
import CAiger
import Logic
import Automata
import Specification
import TransitionSystem

/**
 * Bounded Synthesis encoding that encodes the existence of a ralizing
 * solution in AIGER file format used in the reactive synthesis competition.
 */
public class AigerSmtEncoding<A: Automaton>: SingleParamaterSearch where A: SafetyAcceptance {

    public typealias Parameter = NumberOfAndGatesInAIGER

    let options: BoSyOptions
    let automaton: A
    let specification: SynthesisSpecification
    let stateBits: Int

    // intermediate results
    var solver: SmtSolver?
    var solutionBound: NumberOfAndGatesInAIGER?

    public init(options: BoSyOptions, automaton: A, specification: SynthesisSpecification, stateBits: Int) {
        precondition(stateBits > 0)
        self.options = options
        self.automaton = automaton
        self.specification = specification
        self.stateBits = stateBits

        solver = nil
        solutionBound = nil
    }

    public func solve(forBound bound: NumberOfAndGatesInAIGER) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")

        let constraintTimer = options.statistics?.startTimer(phase: .constraintGeneration)
        let instance = try getEncoding(forBound: bound)
        constraintTimer?.stop()
        //print(instance)

        guard let solver = SolverInstance.z3.instance as? SmtSolver else {
            throw BoSyEncodingError.SolvingFailed("solver creation failed")
        }
        self.solver = solver

        //print(instance)

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
        let aiger = aiger_init()
        for (i, input) in specification.inputs.enumerated() {
            let aiger_var = UInt32(i + 1) << 1
            aiger_add_input(aiger, aiger_var, input)
            //print(aiger_var, input)
        }
        for i in 0..<stateBits {
            guard let lNext = decodeValue(name: "l\(i)In") else {
                fatalError("could not get model from SMT solver")
            }
            let aiger_var = UInt32(i + 1 + specification.inputs.count) << 1
            aiger_add_latch(aiger, aiger_var, lNext, "l\(i)")
            //print(aiger_var, lNext, "l\(i)")
        }
        guard let bound = solutionBound?.value else {
            fatalError("solution bound is missing")
        }
        for i in 0..<bound {
            let aiger_var = UInt32(i + 1 + specification.inputs.count + stateBits) << 1
            guard let lhs = decodeValue(name: "and\(i)Lhs"),
                  let rhs = decodeValue(name: "and\(i)Rhs") else {
                    fatalError("could not get model from SMT solver")
            }
            aiger_add_and(aiger, aiger_var, lhs, rhs)
            //print(aiger_var, lhs, rhs)
        }
        for (i, output) in specification.outputs.enumerated() {
            guard let value = decodeValue(name: "o\(i)") else {
                fatalError("could not get model from SMT solver")
            }
            aiger_add_output(aiger, value, output)
            //print(value, "o\(i)")
        }

        return AigerSolution(aiger: aiger)
    }

    func decodeValue(name: String) -> UInt32? {
        guard let variable = solver?.getIntValue(name: name) else {
            return nil
        }
        guard let negation = solver?.getValue(expression: name + "Neg") else {
            return nil
        }
        if let literal = negation as? Literal, literal == Literal.True {
            return (UInt32(variable) << 1) + 1
        } else {
            return UInt32(variable) << 1
        }
    }

    /**
     * Returns an SMT query that is satisfiable iff there is an AIGER solution
     * with `bound` AND gates.
     */
    func getEncoding(forBound bound: NumberOfAndGatesInAIGER) throws -> String {
        precondition(specification.semantics == .mealy)

        let numInputs = specification.inputs.count

        // aiger max num = #inputs + #stateBits + #ands
        let aigerMaxNum = numInputs + stateBits + bound.value

        // encode aiger file, values are encoded binary
        let numAigerBits = numBitsNeeded(aigerMaxNum)

        Logger.default().debug("aiger max num is \(aigerMaxNum), numAigerBits \(numAigerBits)")


        var smt = ""//"(set-logic UFDTLIA)\n"

        // aiger variables are encoded as bounded natural numbers

        let smtInputs = specification.inputs.enumerated().map({ i, name in "i\(i)" })
        let smtLatches = (0..<stateBits).map({ "l\($0)" })

        let smtInputsParameter = smtInputs.map({ "(\($0) Bool)" }).joined(separator: " ")
        let smtLatchesParameter = smtLatches.map({ "(\($0) Bool)" }).joined(separator: " ")

        for smtVar in smtLatches {
            smt.append("(declare-const \(smtVar)In Int)\n")
            smt.append("(assert (<= 0 \(smtVar)In \(aigerMaxNum)))\n")
            smt.append("(declare-const \(smtVar)InNeg Bool)\n")
        }

        let smtOutputs = specification.outputs.enumerated().map({ i, name in "o\(i)" })
        for smtVar in smtOutputs {
            smt.append("(declare-const \(smtVar) Int)\n")
            smt.append("(assert (<= 0 \(smtVar) \(aigerMaxNum)))\n")
            smt.append("(declare-const \(smtVar)Neg Bool)\n")
        }

        let smtAnds = (0..<bound.value).map({ "and\($0)" })
        for (i, smtAnd) in smtAnds.enumerated() {
            smt.append("(declare-const \(smtAnd)Lhs Int)\n")
            smt.append("(declare-const \(smtAnd)LhsNeg Bool)\n")
            smt.append("(declare-const \(smtAnd)Rhs Int)\n")
            smt.append("(declare-const \(smtAnd)RhsNeg Bool)\n")

            let aiger_var = i + specification.inputs.count + stateBits
            smt.append("(assert (<= 0 \(smtAnd)Lhs \(aiger_var)))\n")
            smt.append("(assert (<= 0 \(smtAnd)Rhs \(aiger_var)))\n")

        }

        // build lookup for aiger variables

        smt.append("(define-fun cond_neg ((r Bool) (neg Bool)) Bool (ite neg (not r) r ) )\n")

        let decParameter = (smtLatches + smtInputs).joined(separator: " ")

        var dec = "false"
        for (i, smtAnd) in smtAnds.enumerated().reversed() {
            let aiger_var = i + 1 + specification.inputs.count + stateBits
            let and = "(and (cond_neg (dec \(smtAnd)Lhs \(decParameter)) \(smtAnd)LhsNeg) (cond_neg (dec \(smtAnd)Rhs \(decParameter)) \(smtAnd)RhsNeg) )"
            dec = "\n(ite (= v \(aiger_var)) \(and) \(dec) )"
        }
        for (i, smtLatch) in smtLatches.enumerated().reversed() {
            let aiger_var = i + 1 + specification.inputs.count
            dec = "\n(ite (= v \(aiger_var)) \(smtLatch) \(dec) )"
        }
        for (i, smtInput) in smtInputs.enumerated().reversed() {
            let aiger_var = i + 1
             dec = "\n(ite (= v \(aiger_var)) \(smtInput) \(dec) )"
        }
        dec = "(ite (<= v 0) false \(dec))"
        smt.append("(define-fun-rec dec ( (v Int) \(smtLatchesParameter) \(smtInputsParameter) ) Bool \(dec) )\n")

        // lambdas
        for q in automaton.states {
            smt.append("(declare-fun \(lambda(q)) (\(smtLatches.map({ _ in "Bool" }).joined(separator: " "))) Bool)\n")
        }

        // lambda sharp
        for q in automaton.states {
            smt.append("(declare-fun \(lambdaSharp(q)) (\(smtLatches.map({ _ in "Bool" }).joined(separator: " "))) Int)\n")
        }

        for state in automaton.initialStates {
            smt.append("(assert (\(lambda(state)) \(smtLatches.map({ _ in "false" }).joined(separator: " "))))\n")
        }

        let printer = SmtPrinter()

        for q in automaton.states {

            let replacer = ReplacingPropositionVisitor(replace: {
                proposition in
                if let index = self.specification.outputs.index(of: proposition.name) {
                    let smtOut = smtOutputs[index]
                    return FunctionApplication(function: Proposition("cond_neg"), application: [FunctionApplication(function: Proposition("dec"), application: [Proposition(smtOut)] + smtLatches.map(Proposition.init) + smtInputs.map(Proposition.init)), Proposition(smtOut + "Neg")])
                } else if let index = self.specification.inputs.index(of: proposition.name) {
                    let smtIn = smtInputs[index]
                    return Proposition(smtIn)
                } else {
                    fatalError()
                }
            })

            if let condition = automaton.safetyConditions[q] {
                let assertion = FunctionApplication(function: lambda(q), application: smtLatches.map(Proposition.init)) --> condition.accept(visitor: replacer)
                smt.append("(assert (forall (\(smtLatchesParameter) \(smtInputsParameter)) \(assertion.accept(visitor: printer))))\n")
            }
            guard let outgoing = automaton.transitions[q] else {
                continue
            }

            for (qPrime, guardCondition) in outgoing {
                let transitionCondition = requireTransition(q: q, qPrime: qPrime)
                let assertion = (FunctionApplication(function: lambda(q), application: smtLatches.map(Proposition.init)) & guardCondition.accept(visitor: replacer)) --> transitionCondition
                smt.append("(assert (forall (\(smtLatchesParameter) \(smtInputsParameter)) \(assertion.accept(visitor: printer))))\n")
            }
        }

        return smt
    }

    func requireTransition(q: A.State, qPrime: A.State) -> Logic {
        let smtLatches = (0..<stateBits).map({ "l\($0)" })
        let smtInputs = specification.inputs.enumerated().map({ i, name in "i\(i)" })

        let lambdaNext = FunctionApplication(function: lambda(qPrime), application: smtLatches.map({
            latch in FunctionApplication(function: Proposition("cond_neg"), application: [FunctionApplication(function: Proposition("dec"), application: [Proposition(latch + "In")] + smtLatches.map(Proposition.init) + smtInputs.map(Proposition.init)), Proposition(latch + "InNeg")])
        }))

        guard let coBüchi = automaton as? CoBüchiAutomaton else {
            // safety automaton
            return lambdaNext
        }

        if coBüchi.isStateInNonRejectingSCC(q as! CoBüchiAutomaton.State) || coBüchi.isStateInNonRejectingSCC(qPrime as! CoBüchiAutomaton.State) || !coBüchi.isInSameSCC(q as! CoBüchiAutomaton.State, qPrime as! CoBüchiAutomaton.State) {
            // no need for comparator constrain
            return lambdaNext
        } else {
            let lambdaSharpCurrent = FunctionApplication(function: lambdaSharp(q), application: smtLatches.map(Proposition.init))
            let lambdaSharpNext = FunctionApplication(function: lambdaSharp(qPrime), application: smtLatches.map({
                latch in FunctionApplication(function: Proposition("cond_neg"), application: [FunctionApplication(function: Proposition("dec"), application: [Proposition(latch + "In")] + smtLatches.map(Proposition.init) + smtInputs.map(Proposition.init)), Proposition(latch + "InNeg")])
            }))
            return lambdaNext & BooleanComparator(coBüchi.rejectingStates.contains(qPrime as! CoBüchiAutomaton.State) ? .Less : .LessOrEqual,
                                                  lhs: lambdaSharpNext,
                                                  rhs: lambdaSharpCurrent)
        }
    }

    func lambda(_ automatonState: A.State) -> Proposition {
        return Proposition("lambda_\(automatonState)".replacingOccurrences(of: "[", with: "").replacingOccurrences(of: "]", with: "").replacingOccurrences(of: ",", with: ""))
    }

    func lambdaSharp(_ automatonState: A.State) -> Proposition {
        return Proposition("lambdaSharp_\(automatonState)".replacingOccurrences(of: "[", with: "").replacingOccurrences(of: "]", with: "").replacingOccurrences(of: ",", with: ""))
    }

}
