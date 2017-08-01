import CUDD
import CAiger
import SafetyGameSolver

import Specification

/**
 * Symbolic representation of transition systems.
 * The boolean functions are represented by BDDs using the CUDD library.
 *
 * Can encode both, mealy and moore, transition systems.
 */
public class SymbolicStateSolution: TransitionSystem {
    let manager: CUDDManager
    
    let inputs: [String]
    let outputs: [String]
    let semantics: TransitionSystemType
    
    let latches: [CUDDNode]
    let inputNodes: [CUDDNode]
    let outputFunctions: [CUDDNode]
    let latchFunctions: [CUDDNode]
    
    public init(manager: CUDDManager, inputs: [String], outputs: [String], semantics: TransitionSystemType, latches: [CUDDNode], inputNodes: [CUDDNode], outputFunctions: [CUDDNode], latchFunctions: [CUDDNode]) {
        self.manager = manager
        
        self.inputs = inputs
        self.outputs = outputs
        self.semantics = semantics
        
        self.latches = latches
        self.inputNodes = inputNodes
        self.outputFunctions = outputFunctions
        self.latchFunctions = latchFunctions
    }
    
}

extension SymbolicStateSolution: AigerRepresentable {
  
    private func _toAiger() -> UnsafeMutablePointer<aiger>? {
        let encoder = BDD2AigerEncoder(manager: manager)
        
        for (input, inputName) in zip(inputNodes, inputs) {
            encoder.addInput(node: input, name: inputName)
        }
        
        for latch in latches {
            encoder.addLatchVariable(node: latch)
        }
        for (latch, latchNext) in zip(latches, latchFunctions) {
            encoder.defineLatch(node: latch, nextNode: latchNext)
        }
        
        for (output, outputName) in zip(outputFunctions, outputs) {
            encoder.addOutput(node: output, name: outputName)
        }
        
        return encoder.aiger
    }
    
    public var aiger: UnsafeMutablePointer<aiger>? {
        return _toAiger()
    }
    
}
