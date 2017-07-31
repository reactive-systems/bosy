import CAiger

/**
 * Solutions that implement this protocol can be represented as AIGER files
 */
public protocol AigerRepresentable {
    var aiger: UnsafeMutablePointer<aiger>? { get }
}

/**
 * Solutions that implement this protocol can be represented as DOT files
 */
public protocol DotRepresentable {
    var dot: String { get }
    var dotTopology: String { get }
}

/**
 * Solutions that implement this protocol can be represented as SMV files
 */
public protocol SmvRepresentable {
    var smv: String { get }
}

/**
 * Solutions that implement this protocol can be represented as Verilog files
 */
public protocol VerilogRepresentable {
    var verilog: String { get }
}

public protocol TransitionSystem {}
