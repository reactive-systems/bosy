
extension LTL: CustomStringConvertible {
    public var description: String {
        switch self {
        case let .atomicProposition(ap):
            return ap.description
        case let .pathProposition(ap, path):
            return "\(ap)[\(path)]"
        case let .application(function, parameters: parameters):
            switch function.arity {
            case 0:
                return "\(function)"
            case 1:
                return "\(function) (\(parameters[0]))"
            case 2:
                return "(\(parameters[0])) \(function) (\(parameters[1]))"
            default:
                fatalError()
            }
        case let .pathQuantifier(quant, parameters: parameters, body: body):
            return "\(quant) \(parameters.map(String.init(describing:)).joined(separator: " ")). \(body)"
        }
    }
}

extension LTLPathVariable: CustomStringConvertible {
    public var description: String {
        name
    }
}

extension LTLAtomicProposition: CustomStringConvertible {
    public var description: String {
        name
    }
}

extension LTLFunction: CustomStringConvertible {
    public var description: String {
        symbol
    }
}
