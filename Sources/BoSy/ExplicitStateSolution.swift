import CAiger
import Utils

protocol BoSySolution {
    func toAiger() -> UnsafeMutablePointer<aiger>?
}

struct ExplicitStateSolution: BoSySolution {
    typealias State = Int
    
    var states: [State]
    var initial: State
    var outputGuards: [State: [String: Boolean]]
    var transitions: [State: [State: Boolean]]
    
    let inputs: [String]
    let outputs: [String]
    
    init(bound: Int, inputs: [String], outputs: [String]) {
        self.inputs = inputs
        self.outputs = outputs
        states = Array(0..<bound)
        initial = 0
        outputGuards = [:]
        transitions = [:]
    }
    
    mutating func addTransition(from: State, to: State, withGuard newGuard: Boolean) {
        var outgoing: [State:Boolean] = transitions[from] ?? [:]
        outgoing[to] = (outgoing[to] ?? Literal.False) | newGuard
        transitions[from] = outgoing
    }
    
    mutating func add(output: String, inState: State, withGuard: Boolean) {
        assert(outputs.contains(output))
        var outputInState = outputGuards[inState] ?? [:]
        outputInState[output] = (outputInState[output] ?? Literal.False) | withGuard
        outputGuards[inState] = outputInState
    }
    
    func toAiger() -> UnsafeMutablePointer<aiger>? {
        let latches = (0..<numBitsNeeded(states.count)).map({ bit in Proposition("s\(bit)") })
        let aigerVisitor = AigerVisitor(inputs: inputs.map(Proposition.init), latches: latches)
        
        // indicates when output must be enabled (formula over state bits and inputs)
        var outputFunction: [String:Boolean] = [:]
        
        // build the circuit for outputs
        for (state, outputs) in outputGuards {
            for (output, condition) in outputs {
                let mustBeEnabled = stateToBits(state, withLatches: latches).reduce(Literal.True, combine: &) & condition
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
        
        var latchFunction: [Proposition:Boolean] = [:]
        
        // build the transition function
        for (source, outgoing) in transitions {
            for (target, condition) in outgoing {
                let enabled = stateToBits(source, withLatches: latches).reduce(Literal.True, combine: &) & condition
                let targetEncoding = binaryFrom(target).characters
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
    
    func stateToBits(_ state: Int, withLatches latches: [Proposition]) -> [Boolean] {
        var bits: [Boolean] = []
        for (value, proposition) in zip(binaryFrom(state).characters, latches) {
            assert(["0", "1"].contains(value))
            if value == "0" {
                bits.append(!proposition)
            } else {
                bits.append(proposition)
            }
        }
        return bits
    }
    
    func binaryFrom(_ n: Int) -> String {
        let binary = String(n, radix: 2)
        // padding on left
        assert(binary.characters.count <= numBitsNeeded(states.count))
        if binary.characters.count == numBitsNeeded(states.count) {
            return binary
        }
        let zero: Character = "0"
        let padding = String(repeating: zero, count: numBitsNeeded(states.count) - binary.characters.count)
        return padding + binary
    }
}
