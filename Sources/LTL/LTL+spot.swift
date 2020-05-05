

extension LTL {
    /**
     * Allows printing of LTL formula in ltl3ba compatible format
     */
    public var spot: String? {
        var ltl3baOperatorMapping: [LTLFunction: String] = [:]
        ltl3baOperatorMapping[.tt] = "true"
        ltl3baOperatorMapping[.ff] = "false"
        ltl3baOperatorMapping[.negation] = "!"
        ltl3baOperatorMapping[.or] = "||"
        ltl3baOperatorMapping[.and] = "&&"
        ltl3baOperatorMapping[.implies] = "->"
        ltl3baOperatorMapping[.equivalent] = "<->"
        ltl3baOperatorMapping[.next] = "X"
        ltl3baOperatorMapping[.until] = "U"
        ltl3baOperatorMapping[.weakUntil] = "W"
        ltl3baOperatorMapping[.release] = "R"
        ltl3baOperatorMapping[.finally] = "F"
        ltl3baOperatorMapping[.globally] = "G"

        switch self {
        case let .atomicProposition(ap):
            return "\"\(ap.name)\""
        case let .pathProposition(proposition, path):
            return "\"\(proposition.name)[\(path.name)]\""
        case let .application(function, parameters: parameters):
            switch function.arity {
            case 0:
                // true and false
                guard let translated = ltl3baOperatorMapping[function] else {
                    return nil
                }
                return translated
            case 1:
                // unary operators
                assert(parameters.count == 1)
                guard let translatedOp = ltl3baOperatorMapping[function] else {
                    return nil
                }
                guard let smvScope = parameters[0].spot else {
                    return nil
                }
                return "\(translatedOp) (\(smvScope))"
            case 2:
                assert(parameters.count == 2)
                guard let translatedOp = ltl3baOperatorMapping[function] else {
                    return nil
                }
                guard let translatedLhs = parameters[0].spot else {
                    return nil
                }
                guard let translatedRhs = parameters[1].spot else {
                    return nil
                }

                return "(\(translatedLhs)) \(translatedOp) (\(translatedRhs))"
            default:
                return nil
            }
        default:
            return nil
        }
    }
}
