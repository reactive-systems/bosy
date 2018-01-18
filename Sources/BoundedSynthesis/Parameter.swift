/**
 * A synthesis parameter is a property about a synthesized system.
 *
 * Parameters can be bounded/minimized, different synthesis methods bound/minimize
 * different parameters.
 */
public protocol SynthesisParameter {
    associatedtype Value: Strideable where Value.Stride: SignedInteger

    var value: Value { get set }

    static var min: Value { get }
    static var max: Value { get }

    init(value: Value)
}

/**
 * The number of states that the solution should have/has.
 */
public struct NumberOfStates: SynthesisParameter {
    public var value: Int

    public static var min = 1
    public static var max = Int.max

    public init(value: Int) {
        self.value = value
    }
}

/**
 * The number of visits of rejecting states in any run in the run graph.
 */
public struct RejectingCounter: SynthesisParameter {
    public var value: Int

    public static var min = 1
    public static var max = Int.max

    public init(value: Int) {
        self.value = value
    }
}

/**
 * SyntComp measurement for quality of synthesized solution.
 */
public struct NumberOfAndGatesInAIGER: SynthesisParameter {
    public var value: Int

    public static var min = 0
    public static var max = Int.max

    public init(value: Int) {
        self.value = value
    }
}
