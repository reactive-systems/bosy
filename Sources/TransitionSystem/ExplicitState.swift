import CAiger
import Logic
import LTL
import Specification
import Utils

/**
 * Implementations with an explicit representation of states while the
 * transition- and output-functions are represented symbolically.
 *
 * Can encode both, mealy and moore, transition systems.
 */
public struct ExplicitStateSolution: TransitionSystem {
    public typealias State = Int

    let specification: SynthesisSpecification

    var states: [State]
    var initial: State
    var outputGuards: [State: [String: Logic]]
    var transitions: [State: [State: Logic]]

    public init(bound: Int, specification: SynthesisSpecification) {
        self.specification = specification
        states = Array(0 ..< bound)
        initial = 0
        outputGuards = [:]
        transitions = [:]
    }

    public mutating func addTransition(from: State, to: State, withGuard newGuard: Logic) {
        var outgoing: [State: Logic] = transitions[from] ?? [:]
        outgoing[to] = (outgoing[to] ?? Literal.False) | newGuard
        transitions[from] = outgoing
    }

    public mutating func add(output: String, inState: State, withGuard: Logic) {
        assert(specification.outputs.contains(output))
        var outputInState = outputGuards[inState] ?? [:]
        outputInState[output] = (outputInState[output] ?? Literal.False) | withGuard
        outputGuards[inState] = outputInState
    }
}

extension ExplicitStateSolution: AigerRepresentable {
    private func _toAiger() -> UnsafeMutablePointer<aiger>? {
        let latches = (0 ..< numBitsNeeded(states.count)).map { bit in Proposition("__latch_s\(bit)") }
        let aigerVisitor = AigerVisitor(inputs: specification.inputs.map(Proposition.init), latches: latches)

        // indicates when output must be enabled (formula over state bits and inputs)
        var outputFunction: [String: Logic] = [:]

        // build the circuit for outputs
        for (state, outputs) in outputGuards {
            for (output, condition) in outputs {
                let mustBeEnabled = stateToBits(state, withLatches: latches).reduce(Literal.True, &) & condition
                outputFunction[output] = (outputFunction[output] ?? Literal.False) | mustBeEnabled
            }
        }
        for output in specification.outputs {
            if let condition = outputFunction[output] {
                let aigLiteral = condition.accept(visitor: aigerVisitor)
                aigerVisitor.addOutput(literal: aigLiteral, name: output)
            } else {
                fatalError("Output \(output) is not defined")
            }
        }

        var latchFunction: [Proposition: Logic] = [:]

        // build the transition function
        for (source, outgoing) in transitions {
            for (target, condition) in outgoing {
                let enabled = stateToBits(source, withLatches: latches).reduce(Literal.True, &) & condition
                let targetEncoding = binaryFrom(target, bits: numBitsNeeded(states.count))
                for (bit, latch) in zip(targetEncoding, latches) {
                    assert(["0", "1"].contains(bit))
                    if bit == "0" {
                        continue
                    }
                    latchFunction[latch] = (latchFunction[latch] ?? Literal.False) | enabled
                }
            }
        }
        for (latch, condition) in latchFunction {
            let aigLiteral = condition.accept(visitor: aigerVisitor)
            aigerVisitor.defineLatch(latch: latch, next: aigLiteral)
        }

        return aigerVisitor.aig
    }

    private func stateToBits(_ state: Int, withLatches latches: [Proposition]) -> [Logic] {
        var bits: [Logic] = []
        for (value, proposition) in zip(binaryFrom(state, bits: numBitsNeeded(states.count)), latches) {
            assert(["0", "1"].contains(value))
            if value == "0" {
                bits.append(!proposition)
            } else {
                bits.append(proposition)
            }
        }
        return bits
    }

    public var aiger: UnsafeMutablePointer<aiger>? {
        _toAiger()
    }
}

extension ExplicitStateSolution: DotRepresentable {
    /**
     * We have one set of functions encoding the transition function
     * and one set of functions encoding the outputs.
     * This function combines them such that we can print edges containing both.
     */
    private func matchOutputsAndTransitions() -> [State: [State: [(transitionGuard: Logic, outputs: [String])]]] {
        precondition(specification.semantics == .mealy)
        var outputTransitions: [State: [State: [(transitionGuard: Logic, outputs: [String])]]] = [:]

        for (source, outputs) in outputGuards {
            var valuations: [([String], Logic)] = [([], Literal.True)] // maps valuations of outputs to their guards
            for (output, outputGuard) in outputs {
                valuations = valuations.map { valuation, valuationGuard in
                    if outputGuard as? Literal != nil, outputGuard as! Literal == Literal.False {
                        // output is always false, do nothing
                        return [(valuation, valuationGuard)]
                    }
                    // output is not false
                    return [(valuation + [output], (valuationGuard & outputGuard).simplify()), (valuation, (valuationGuard & !outputGuard).simplify())]
                }.reduce([], +)
            }
            guard let outgoing = transitions[source] else {
                fatalError()
            }
            for (target, transitionGuard) in outgoing {
                for (valuation, valuationGuard) in valuations {
                    let newGuard = (transitionGuard & valuationGuard).simplify()
                    if newGuard as? Literal != nil, newGuard as! Literal == Literal.False {
                        continue
                    }
                    var sourceOut: [State: [(transitionGuard: Logic, outputs: [String])]] = outputTransitions[source] ?? [:]
                    sourceOut[target] = (sourceOut[target] ?? []) + [(newGuard, valuation)]
                    outputTransitions[source] = sourceOut
                }
            }
        }
        return outputTransitions
    }

    private func _toDot(labelEdges: Bool = true) -> String {
        var dot: [String] = []

        // initial state
        dot += ["\t_init [style=\"invis\"];", "\t_init -> s\(initial)[label=\"\"];"]

        switch specification.semantics {
        case .mealy:
            for state in states {
                dot.append("\ts\(state)[shape=rectangle,label=\"s\(state)\"];")
            }

            if labelEdges {
                let transitionOutputs = matchOutputsAndTransitions()
                for (source, outgoing) in transitionOutputs {
                    for (target, iterator) in outgoing {
                        for (transitionGuard: transitionGuard, outputs: outputs) in iterator {
                            dot.append("\ts\(source) -> s\(target) [label=\"\(transitionGuard) / \(outputs.joined(separator: " "))\"];")
                        }
                    }
                }
            } else {
                for (source, outgoing) in transitions {
                    for (target, transitionGuard) in outgoing {
                        if transitionGuard as? Literal != nil, transitionGuard as! Literal == Literal.False {
                            continue
                        }
                        dot.append("\ts\(source) -> s\(target);")
                    }
                }
            }

        case .moore:
            for state in states {
                var outputs: [String] = []
                if let outputGuards = self.outputGuards[state] {
                    for (output, outputGuard) in outputGuards {
                        guard let literal = outputGuard as? Literal else {
                            fatalError()
                        }
                        if literal == Literal.True {
                            outputs.append(output)
                        }
                    }
                }

                if labelEdges {
                    dot.append("\ts\(state)[shape=rectangle,label=\"s\(state)\n\(outputs.joined(separator: " "))\"];")
                } else {
                    dot.append("\ts\(state)[shape=rectangle,label=\"s\(state)\"];")
                }
            }

            for (source, outgoing) in transitions {
                for (target, constraint) in outgoing {
                    if labelEdges {
                        dot.append("\ts\(source) -> s\(target) [label=\"\(constraint)\"];")
                    } else {
                        dot.append("\ts\(source) -> s\(target);")
                    }
                }
            }
        }

        return "digraph graphname {\n\(dot.joined(separator: "\n"))\n}"
    }

    public var dot: String {
        _toDot()
    }

    public var dotTopology: String {
        _toDot(labelEdges: false)
    }
}

extension ExplicitStateSolution: SmvRepresentable {
    private func _toSMV() -> String {
        var smv: [String] = ["MODULE main"]

        // variable: states and inputs
        smv.append("\tVAR")
        smv.append("\t\tstate: {\(states.map { "s\($0)" }.joined(separator: ", "))};")
        for input in specification.inputs {
            smv.append("\t\t\(input) : boolean;")
        }

        // transitions
        smv.append("\tASSIGN")
        smv.append("\t\tinit(state) := s\(initial);")

        let smvPrinter = SmvPrinter()
        var nextState: [String] = []
        for (source, outgoing) in transitions {
            for (target, transitionGuard) in outgoing {
                let smvGuard = transitionGuard.accept(visitor: smvPrinter)
                nextState.append("state = s\(source) & \(smvGuard) : s\(target);")
            }
        }
        smv.append("\t\tnext(state) := case\n\t\t\t\(nextState.joined(separator: "\n\t\t\t"))\n\t\tesac;")

        // outputs
        smv.append("\tDEFINE")
        for output in specification.outputs {
            var smvGuard: [String] = []
            for (source, outputDefinitions) in outputGuards {
                guard let outputGuard = outputDefinitions[output] else {
                    continue
                }
                if outputGuard as? Literal != nil, outputGuard as! Literal == Literal.False {
                    continue
                }
                smvGuard.append("state = s\(source) & \(outputGuard.accept(visitor: smvPrinter))")
            }
            if smvGuard.isEmpty {
                smvGuard.append("FALSE")
            }
            smv.append("\t\t\(output) := (\(smvGuard.joined(separator: " | ")));")
        }

        // LTL specification for model checking
        let ltlspec = specification.ltl.normalized
        guard let smvLtlSpec = ltlspec.smv else {
            Logger.default().warning("could not transform LTL specification to SMV format, omit `LTLSPEC` in SMV")
            return smv.joined(separator: "\n")
        }
        smv.append("\tLTLSPEC \(smvLtlSpec)")

        return smv.joined(separator: "\n")
    }

    public var smv: String {
        _toSMV()
    }
}

extension ExplicitStateSolution: VerilogRepresentable {
    private func _toVerilog() -> String {
        let signature: [String] = specification.inputs + specification.outputs
        var verilog: [String] = ["module fsm(\(signature.joined(separator: ", ")));"]
        verilog += specification.inputs.map { "  input \($0);" }
        verilog += specification.outputs.map { "  output \($0);" }

        // state definitions
        let numBits = numBitsNeeded(states.count)
        assert(numBits > 0)
        verilog += ["  reg [\(numBits - 1):0] state;\n"]

        let verilogPrinter = VerilogPrinter()

        // output definitions
        for output in specification.outputs {
            var verilogGuard: [String] = []
            for (source, outputDefinitions) in outputGuards {
                guard let outputGuard = outputDefinitions[output] else {
                    continue
                }
                if outputGuard as? Literal != nil, outputGuard as! Literal == Literal.False {
                    continue
                }
                verilogGuard.append("(state == \(source)) && \(outputGuard.accept(visitor: verilogPrinter))")
            }
            if verilogGuard.isEmpty {
                verilogGuard.append("0")
            }
            verilog.append("  assign \(output) = (\(verilogGuard.joined(separator: " || "))) ? 1 : 0;")
        }

        verilog += ["",
                    "  initial",
                    "  begin",
                    "    state = 0;",
                    "  end",
                    "  always @($global_clock)",
                    "  begin"]

        var nextState: [String] = []
        for (source, outgoing) in transitions {
            var guardes: [String] = []
            var targets: [String] = []
            for (target, transitionGuard) in outgoing {
                let verilogGuard = transitionGuard.accept(visitor: verilogPrinter)
                guardes.append("if (\(verilogGuard))\n")
                targets.append("           state = \(target);\n")
            }
            guardes[guardes.count - 1] = "\n"
            nextState.append("\(source): " + zip(guardes, targets).map { $0 + $1 }.joined(separator: "         else "))
        }
        verilog.append("    case(state)\n      \(nextState.joined(separator: "\n      "))\n    endcase")

        verilog += ["  end"]

        verilog += ["endmodule"]
        return verilog.joined(separator: "\n")
    }

    public var verilog: String {
        _toVerilog()
    }
}
