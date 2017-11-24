
// We define operators to make working with LTL easier

// FIXME: check which precedence is correct
infix operator =>

extension LTL {

    public static func && (lhs: LTL, rhs: LTL) -> LTL {
        return .application(.and, parameters: [lhs, rhs])
    }

    public static func || (lhs: LTL, rhs: LTL) -> LTL {
        return .application(.or, parameters: [lhs, rhs])
    }

    public static prefix func ! (ltl: LTL) -> LTL {
        return .application(.negation, parameters: [ltl])
    }

    public static func => (lhs: LTL, rhs: LTL) -> LTL {
        return .application(.implies, parameters: [lhs, rhs])
    }

    public static func until(_ lhs: LTL, _ rhs: LTL) -> LTL {
        return .application(.until, parameters: [lhs, rhs])
    }

}
