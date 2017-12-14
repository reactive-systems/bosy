
public struct LTLFunction: Codable {
    let symbol: String
    let arity: Int

    // boolean
    public static let tt = LTLFunction(symbol: "⊤", arity: 0)
    public static let ff = LTLFunction(symbol: "⊥", arity: 0)
    public static let negation = LTLFunction(symbol: "¬", arity: 1)
    public static let and = LTLFunction(symbol: "∧", arity: 2)
    public static let or = LTLFunction(symbol: "∨", arity: 2)
    public static let implies = LTLFunction(symbol: "->", arity: 2)
    public static let equivalent = LTLFunction(symbol: "<->", arity: 2)

    // temporal
    public static let next = LTLFunction(symbol: "X", arity: 1)
    public static let until = LTLFunction(symbol: "U", arity: 2)
    public static let weakUntil = LTLFunction(symbol: "W", arity: 2)
    public static let release = LTLFunction(symbol: "R", arity: 2)
    public static let finally = LTLFunction(symbol: "F", arity: 1)
    public static let globally = LTLFunction(symbol: "G", arity: 1)

    var negated: LTLFunction {
        switch self {
        case .tt:
            return .ff
        case .ff:
            return .tt
        case .or:
            return .and
        case .and:
            return .or
        case .next:
            return .next
        case .until:
            return .release
        case .release:
            return .until
        case .finally:
            return .globally
        case .globally:
            return .finally
        default:
            fatalError("negation of \(self) is not defined")
        }
    }
}

public struct LTLAtomicProposition: Codable {
    let name: String
}

public struct LTLPathVariable: Codable {
    let name: String
}

public enum LTLQuantifier: String, Codable {
    case forall
    case exists

    var negated: LTLQuantifier {
        switch self {
        case .exists:
            return .forall
        case .forall:
            return .exists
        }
    }
}

public enum LTL {
    case atomicProposition(LTLAtomicProposition)
    case pathProposition(LTLAtomicProposition, LTLPathVariable)
    indirect case application(LTLFunction, parameters: [LTL])
    indirect case pathQuantifier(LTLQuantifier, parameters: [LTLPathVariable], body: LTL)

    public static let tt: LTL = .application(.tt, parameters: [])
    public static let ff: LTL = .application(.ff, parameters: [])

    /**
     * Checks if the number of parameters matches the arity of function
     */
    var isWellFormed: Bool {
        switch self {
        case .atomicProposition(_):
            return true
        case .pathProposition(_, _):
            return true
        case .application(let function, parameters: let parameters):
            guard parameters.reduce(true, { val, parameter in val && parameter.isWellFormed }) else {
                return false
            }
            return function.arity == parameters.count
        case .pathQuantifier(_, parameters: _, body: let body):
            return body.isWellFormed
        }
    }
}

extension LTL {
    
    public static func parse(fromString string: String) throws -> LTL {
        let scanner = ScalarScanner(scalars: string.unicodeScalars)
        let lexer = LTLLexer(scanner: scanner)
        var parser = LTLParser(lexer: lexer)
        return try parser.parse()
    }

    private func toNegationNormalForm(negated: Bool) -> LTL {
        switch self {
        case .atomicProposition(_):
            return negated ? !self : self
        case .pathProposition(_, _):
            return negated ? !self : self
        case .application(let function, parameters: let parameters):
            if function == .negation {
                return parameters[0].toNegationNormalForm(negated: !negated)
            }
            return .application(
                negated ? function.negated : function,
                parameters: parameters.map({ $0.toNegationNormalForm(negated: negated) })
            )
        case .pathQuantifier(let quantifier, parameters: let parameters, body: let body):
            return .pathQuantifier(
                negated ? quantifier.negated : quantifier,
                parameters: parameters,
                body: body.toNegationNormalForm(negated: negated)
            )
        }
    }

    /**
     * Returns an equivalent LTL formula in negation normal form.
     */
    public var nnf: LTL {
        return toNegationNormalForm(negated: false)
    }

    /**
     * Returns an equivalent LTL formula without derived operators such as
     * implication, equivalence, finally, and globally
     */
    public var normalized: LTL {
        switch self {
        case .atomicProposition(_):
            return self
        case .pathProposition(_, _):
            return self
        case .pathQuantifier(let quantifier, parameters: let parameters, body: let body):
            return .pathQuantifier(quantifier, parameters: parameters, body: body.normalized)
        case .application(let function, parameters: var parameters):
            parameters = parameters.map({ $0.normalized })
            switch function {
            case .implies:
                return !parameters[0] || parameters[1]
            case .equivalent:
                return (parameters[0] && parameters[1]) || (!parameters[0] && !parameters[1])
            case .finally:
                return .application(.until, parameters: [LTL.tt, parameters[0]])
            case .globally:
                return .application(.release, parameters: [LTL.ff, parameters[0]])
            case .weakUntil:
                // 𝞅 W 𝞇  = 𝞅 U 𝞇 ∨ G 𝞅
                return .application(.until, parameters: parameters) || .application(.release, parameters: [LTL.ff, parameters[0]])
            default:
                return .application(function, parameters: parameters)
            }
        }
    }
}
