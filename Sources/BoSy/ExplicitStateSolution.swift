import CAiger
import Utils

protocol AigerRepresentable {
    var aiger: UnsafeMutablePointer<aiger>? { get }
}

protocol DotRepresentable {
    var dot: String { get }
}

protocol BoSySolution {}

struct ExplicitStateSolution: BoSySolution {
    typealias State = Int
    
    let semantics: TransitionSystemType
    var states: [State]
    var initial: State
    var outputGuards: [State: [String: Logic]]
    var transitions: [State: [State: Logic]]
    
    let inputs: [String]
    let outputs: [String]
    
    init(bound: Int, inputs: [String], outputs: [String], semantics: TransitionSystemType) {
        self.inputs = inputs
        self.outputs = outputs
        self.semantics = semantics
        states = Array(0..<bound)
        initial = 0
        outputGuards = [:]
        transitions = [:]
    }
    
    mutating func addTransition(from: State, to: State, withGuard newGuard: Logic) {
        var outgoing: [State:Logic] = transitions[from] ?? [:]
        outgoing[to] = (outgoing[to] ?? Literal.False) | newGuard
        transitions[from] = outgoing
    }
    
    mutating func add(output: String, inState: State, withGuard: Logic) {
        assert(outputs.contains(output))
        var outputInState = outputGuards[inState] ?? [:]
        outputInState[output] = (outputInState[output] ?? Literal.False) | withGuard
        outputGuards[inState] = outputInState
    }
}

extension ExplicitStateSolution: AigerRepresentable {
    private func _toAiger() -> UnsafeMutablePointer<aiger>? {
        let latches = (0..<numBitsNeeded(states.count)).map({ bit in Proposition("s\(bit)") })
        let aigerVisitor = AigerVisitor(inputs: inputs.map(Proposition.init), latches: latches)
        
        // indicates when output must be enabled (formula over state bits and inputs)
        var outputFunction: [String:Logic] = [:]
        
        // build the circuit for outputs
        for (state, outputs) in outputGuards {
            for (output, condition) in outputs {
                let mustBeEnabled = stateToBits(state, withLatches: latches).reduce(Literal.True, &) & condition
                outputFunction[output] = (outputFunction[output] ?? Literal.False) | mustBeEnabled
            }
        }
        // Check that all outputs are defined
        for output in outputs {
            assert(outputFunction[output] != nil)
        }
        for (output, condition) in outputFunction {
            let aigLiteral = condition.accept(visitor: aigerVisitor)
            aigerVisitor.addOutput(literal: aigLiteral, name: output)
        }
        
        var latchFunction: [Proposition:Logic] = [:]
        
        // build the transition function
        for (source, outgoing) in transitions {
            for (target, condition) in outgoing {
                let enabled = stateToBits(source, withLatches: latches).reduce(Literal.True, &) & condition
                let targetEncoding = binaryFrom(target, bits: numBitsNeeded(states.count)).characters
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
        for (value, proposition) in zip(binaryFrom(state, bits: numBitsNeeded(states.count)).characters, latches) {
            assert(["0", "1"].contains(value))
            if value == "0" {
                bits.append(!proposition)
            } else {
                bits.append(proposition)
            }
        }
        return bits
    }
    
    var aiger: UnsafeMutablePointer<aiger>? {
        return _toAiger()
    }
}

extension ExplicitStateSolution: DotRepresentable {
    
    private func matchOutputsAndTransitions() -> [State: [State: (String, Logic)]] {
        precondition(semantics == .mealy)
        var outputTransitions: [State: [State: (String, Logic)]] = [:]
        
        for (source, outputs) in outputGuards {
            for (target, transitionGuard) in transitions[source]! {
                for (output, outputGuard) in outputs {
                    let newGuard = transitionGuard & outputGuard
                    if newGuard as? Literal != nil && newGuard as! Literal == Literal.False {
                        continue
                    }
                    var sourceOut: [State: (String, Logic)] = outputTransitions[source] ?? [:]
                    sourceOut[target] = (output, newGuard)
                    outputTransitions[source] = sourceOut
                }
            }
            
        }
        return outputTransitions
    }
    
    private func _toDot() -> String {
        var dot: [String] = []
        
        // initial state
        dot += ["\t_init [style=\"invis\"];", "\t_init -> s\(initial)[label=\"\"];"]
        
        switch semantics {
        case .mealy:
            for state in states {
                dot.append("\ts\(state)[shape=rectangle,label=\"s\(state)\"];")
            }
            
            let transitionOutputs = matchOutputsAndTransitions()
            for (source, outgoing) in transitionOutputs {
                for (target, (output, transitionGuard)) in outgoing {
                    dot.append("\ts\(source) -> s\(target) [label=\"\(transitionGuard) / \(output)\"];")
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
                        if (literal == Literal.True) {
                            outputs.append(output)
                        }
                    }
                }
                
                
                dot.append("\ts\(state)[shape=rectangle,label=\"s\(state)\n\(outputs.joined())\"];")
            }
            
            for (source, outgoing) in transitions {
                for (target, constraint) in outgoing {
                    dot.append("\ts\(source) -> s\(target) [label=\"\(constraint)\"];")
                }
            }
        }
        
        
        return "digraph graphname {\n\(dot.joined(separator: "\n"))\n}"
    }
    
    var dot: String {
        return _toDot()
    }
}
