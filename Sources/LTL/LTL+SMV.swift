
extension LTL {
    
    /**
     * Allows printing of LTL formula in SMV compatible format
     */
    public var smv: String? {

        var smvOperatorMapping: [LTLFunction:String] = [:]
        smvOperatorMapping[.tt] = "TRUE"
        smvOperatorMapping[.ff] = "FALSE"
        smvOperatorMapping[.negation] = "!"
        smvOperatorMapping[.or] = "|"
        smvOperatorMapping[.and] = "&"
        smvOperatorMapping[.implies] = "->"
        smvOperatorMapping[.equivalent] = "<->"
        smvOperatorMapping[.next] = "X"
        smvOperatorMapping[.until] = "U"
        smvOperatorMapping[.release] = "V"
        smvOperatorMapping[.finally] = "F"
        smvOperatorMapping[.globally] = "G"

        switch self {
        case .atomicProposition(let ap):
            return ap.name
        case .application(let function, parameters: let parameters):
            switch (function.arity) {
            case 0:
                // true and false
                guard let smvName = smvOperatorMapping[function] else {
                    return nil
                }
                return smvName
            case 1:
                // unary operators
                assert(parameters.count == 1)
                guard let smvOp = smvOperatorMapping[function] else {
                    return nil
                }
                guard let smvScope = parameters[0].smv else {
                    return nil
                }
                return "(\(smvOp) \(smvScope))"
            case 2:
                assert(parameters.count == 2)
                guard let smvOp = smvOperatorMapping[function] else {
                    return nil
                }
                guard let smvLhs = parameters[0].smv else {
                    return nil
                }
                guard let smvRhs = parameters[1].smv else {
                    return nil
                }

                return "(\(smvLhs) \(smvOp) \(smvRhs))"
            default:
                return nil
            }
        default:
            return nil
        }
    }
}

