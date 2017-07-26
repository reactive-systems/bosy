import CAiger

/**
 * Solutions that implement this protocol can be represented as AIGER files
 */
protocol AigerRepresentable {
    var aiger: UnsafeMutablePointer<aiger>? { get }
}

/**
 * Solutions that implement this protocol can be represented as DOT files
 */
protocol DotRepresentable {
    var dot: String { get }
    var dotTopology: String { get }
}

/**
 * Solutions that implement this protocol can be represented as SMV files
 */
protocol SmvRepresentable {
    var smv: String { get }
}

/**
 * Solutions that implement this protocol can be represented as Verilog files
 */
protocol VerilogRepresentable {
    var verilog: String { get }
}

protocol BoSySolution {}
