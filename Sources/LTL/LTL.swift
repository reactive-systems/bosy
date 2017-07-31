public enum LTL: CustomStringConvertible, Equatable {
    case Proposition(String)
    case Literal(Bool)
    indirect case UnaryOperator(LTLToken, LTL)
    indirect case BinaryOperator(LTLToken, LTL, LTL)
    
    // CustomStringConvertible
    public var description: String {
        switch self {
        case .Proposition(let name):
            return name
        case .Literal(let val):
            return val ? "true" : "false"
        case .UnaryOperator(let op, let operand):
            return "\(op) \(operand)"
        case .BinaryOperator(let op, let lhs, let rhs):
            return "(\(lhs) \(op) \(rhs))"
        }
    }
    
    // Equatable
    public static func == (lhs: LTL, rhs: LTL) -> Bool {
        switch (lhs, rhs) {
        case (.Proposition(let lhsName), .Proposition(let rhsName)):
            return lhsName == rhsName
        case (.Literal(let lhsVal), .Literal(let rhsVal)):
            return lhsVal == rhsVal
        case (.UnaryOperator(let lhsOp, let lhsOperand), .UnaryOperator(let rhsOp, let rhsOperand)):
            return lhsOp == rhsOp && lhsOperand == rhsOperand
        case (.BinaryOperator(let lhsOp, let lhsLhs, let lhsRhs), .BinaryOperator(let rhsOp, let rhsLhs, let rhsRhs)):
            return lhsOp == rhsOp && lhsLhs == rhsLhs && lhsRhs == rhsRhs
        default:
            return false
        }
    }
    
    public static func parse(fromString string: String) throws -> LTL {
        let scanner = ScalarScanner(scalars: string.unicodeScalars)
        let lexer = LTLLexer(scanner: scanner)
        var parser = LTLParser(lexer: lexer)
        return try parser.parse()
    }
    
    fileprivate func _toNegationNormalForm(negated: Bool) -> LTL {
        switch self {
        case .Proposition(_):
            return negated ? .UnaryOperator(.Not, self) : self
        case .Literal(let val):
            return negated ? .Literal(!val) : self
        case .UnaryOperator(.Not, let scope):
            return scope._toNegationNormalForm(negated: !negated)
        case .UnaryOperator(let op, let scope):
            return .UnaryOperator(negated ? op.negated : op, scope._toNegationNormalForm(negated: negated))
        case .BinaryOperator(let op, let lhs, let rhs):
            return .BinaryOperator(negated ? op.negated : op, lhs._toNegationNormalForm(negated: negated), rhs._toNegationNormalForm(negated: negated))
        }
    }
    
    public var nnf: LTL {
        return self._toNegationNormalForm(negated: false)
    }
    
    fileprivate func _normalize() -> LTL {
        switch self {
        case .BinaryOperator(.Implies, let lhs, let rhs):
            return .BinaryOperator(.Or,
                                   .UnaryOperator(.Not, lhs._normalize()),
                                   rhs._normalize())
        case .BinaryOperator(.Equivalent, let lhs, let rhs):
            let normalizedLhs = lhs._normalize()
            let normalizedRhs = rhs._normalize()
            return .BinaryOperator(.Or,
                                   .BinaryOperator(.And, normalizedLhs, normalizedRhs),
                                   .BinaryOperator(.And, .UnaryOperator(.Not, normalizedLhs), .UnaryOperator(.Not, normalizedRhs) )
            )
        case .UnaryOperator(.Eventually, let scope):
            return .BinaryOperator(.Until, .Literal(true), scope._normalize())
        case .UnaryOperator(.Globally, let scope):
            return .BinaryOperator(.Release, .Literal(false), scope._normalize())
        case .Proposition(_):
            return self
        case .Literal(_):
            return self
        case .UnaryOperator(let token, let scope):
            return .UnaryOperator(token, scope._normalize())
        case .BinaryOperator(let token, let lhs, let rhs):
            return .BinaryOperator(token, lhs._normalize(), rhs._normalize())
        }
    }
    
    public var normalized: LTL {
        return self._normalize()
    }
}
