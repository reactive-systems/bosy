
import TransitionSystem

enum BoSyEncodingError: Error {
    case EncodingFailed(String)
    case SolvingFailed(String)
}

public protocol BoSyEncoding {
    
    mutating func solve(forBound bound: Int) throws -> Bool
    func extractSolution() -> TransitionSystem?
    
}

public protocol SingleParamaterSearch: class {
    associatedtype Parameter: SynthesisParameter

    /**
     * Returns true when the synthesis problem has a solution for the given bound.
     */
    func solve(forBound bound: Parameter) throws -> Bool
}

extension SingleParamaterSearch {

    /**
     * Linear search for the smallest bound such that the synthesis problem has a solution.
     */
    public func searchMinimalLinear() throws -> Parameter? {
        for i in Parameter.min..<Parameter.max {
            let parameter = Parameter(value: i)
            if try solve(forBound: parameter) {
                return parameter
            }
        }
        return nil
    }
}
