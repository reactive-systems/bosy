
extension LTLFunction: Hashable {
    public func hash(into hasher: inout Hasher) {
        hasher.combine(symbol)
        hasher.combine(arity)
    }

    public static func == (lhs: LTLFunction, rhs: LTLFunction) -> Bool {
        lhs.symbol == rhs.symbol && lhs.arity == rhs.arity
    }
}

extension LTLAtomicProposition: Equatable {
    public static func == (lhs: LTLAtomicProposition, rhs: LTLAtomicProposition) -> Bool {
        lhs.name == rhs.name
    }
}

extension LTLPathVariable: Hashable {
    public static func == (lhs: LTLPathVariable, rhs: LTLPathVariable) -> Bool {
        lhs.name == rhs.name
    }

    public func hash(into hasher: inout Hasher) {
        hasher.combine(name)
    }
}

extension LTL: Equatable {
    public static func == (lhs: LTL, rhs: LTL) -> Bool {
        switch (lhs, rhs) {
        case let (.atomicProposition(lhs), .atomicProposition(rhs)):
            return lhs == rhs
        case let (.pathProposition(lhs, lhsPath), .pathProposition(rhs, rhsPath)):
            return lhs == rhs && lhsPath == rhsPath
        case let (.application(lhsFun, lhsParameters), .application(rhsFun, parameters: rhsParameters)):
            return lhsFun == rhsFun && lhsParameters == rhsParameters
        case let (.pathQuantifier(lhsQuant, lhsParamaters, lhsBody), .pathQuantifier(rhsQuant, parameters: rhsParameters, body: rhsBody)):
            return lhsQuant == rhsQuant && lhsParamaters == rhsParameters && lhsBody == rhsBody
        default:
            return false
        }
    }
}
