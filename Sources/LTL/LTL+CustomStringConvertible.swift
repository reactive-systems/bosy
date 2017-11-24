
extension LTL: CustomStringConvertible {

    public var description: String {
        switch self {
        case .atomicProposition(let ap):
            return ap.description
        case .pathProposition(let ap, let path):
            return "\(ap)[\(path)]"
        case .application(let function, parameters: let parameters):
            switch function.arity {
            case 0:
                return "\(function)"
            case 1:
                return "\(function) \(parameters[0])"
            case 2:
                return "\(parameters[0]) \(function) \(parameters[1])"
            default:
                fatalError()
            }
        case .pathQuantifier(let quant, parameters: let parameters, body: let body):
            return "\(quant) \(parameters.map(String.init(describing:)).joined(separator: " ")). \(body)"
        }
    }
}

extension LTLPathVariable: CustomStringConvertible {
    public var description: String {
        return name
    }
}

extension LTLAtomicProposition: CustomStringConvertible {
    public var description: String {
        return name
    }
}

extension LTLFunction: CustomStringConvertible {
    public var description: String {
        return symbol
    }
}
