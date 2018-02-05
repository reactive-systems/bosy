
import CAiger

import Specification

/**
 * Symbolic representation of transition systems.
 * The boolean functions are represented by and-inverter-graphs using the AIGER library.
 *
 * Can encode both, mealy and moore, transition systems.
 */
public class AigerSolution: TransitionSystem, AigerRepresentable {
    public let aiger: UnsafeMutablePointer<aiger>?

    public init(aiger: UnsafeMutablePointer<aiger>?) {
        self.aiger = aiger
    }

    deinit {
        aiger_reset(aiger)
    }
}

