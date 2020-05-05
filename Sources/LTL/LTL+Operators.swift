
// We define operators to make working with LTL easier

// FIXME: check which precedence is correct
infix operator =>
infix operator <=>

extension LTL {
    public static func && (lhs: LTL, rhs: LTL) -> LTL {
        .application(.and, parameters: [lhs, rhs])
    }

    public static func &= (lhs: inout LTL, rhs: LTL) {
        lhs = lhs && rhs
    }

    public static func || (lhs: LTL, rhs: LTL) -> LTL {
        .application(.or, parameters: [lhs, rhs])
    }

    public static prefix func ! (ltl: LTL) -> LTL {
        .application(.negation, parameters: [ltl])
    }

    public static func => (lhs: LTL, rhs: LTL) -> LTL {
        .application(.implies, parameters: [lhs, rhs])
    }

    public static func <=> (lhs: LTL, rhs: LTL) -> LTL {
        .application(.equivalent, parameters: [lhs, rhs])
    }

    public static func until(_ lhs: LTL, _ rhs: LTL) -> LTL {
        .application(.until, parameters: [lhs, rhs])
    }

    public static func weakUntil(_ lhs: LTL, _ rhs: LTL) -> LTL {
        .application(.weakUntil, parameters: [lhs, rhs])
    }

    public static func release(_ lhs: LTL, _ rhs: LTL) -> LTL {
        .application(.release, parameters: [lhs, rhs])
    }
}
