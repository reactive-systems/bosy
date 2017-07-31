struct LTLParser {
    var lexer: LTLLexer
    var current: LTLToken
    
    init(lexer: LTLLexer) {
        self.lexer = lexer
        self.current = .Proposition("dummy")
    }
    
    mutating func parse() throws -> LTL {
        current = try self.lexer.next()
        return try parseExpression(minPrecedence: LTLOperatorPrecedence.min)
    }
    
    mutating func parseExpression(minPrecedence: LTLOperatorPrecedence) throws -> LTL {
        var lhs = try parseUnaryExpression()
        
        while current.isBinaryOperator && current.precedence >= minPrecedence {
            let op = current
            current = try lexer.next()
            let rhs = try parseExpression(minPrecedence: op.precedence.next())
            lhs = LTL.BinaryOperator(op, lhs, rhs)
        }
        
        return lhs
    }
    
    mutating func parseUnaryExpression() throws -> LTL {
        if current.isUnaryOperator {
            let op = current
            current = try lexer.next()
            return .UnaryOperator(op, try parseUnaryExpression())
        }
        else {
            return try parsePrimaryExpression()
        }
    }
    
    mutating func parsePrimaryExpression() throws -> LTL {
        switch current {
        case .Proposition(let name):
            current = try lexer.next()
            return .Proposition(name)
        case .True:
            current = try lexer.next()
            return .Literal(true)
        case .False:
            current = try lexer.next()
            return .Literal(false)
        case .LParen:
            current = try lexer.next()
            let expr = try parseExpression(minPrecedence: LTLOperatorPrecedence.min)
            switch current {
            case .RParen:
                current = try lexer.next()
                return expr
            default:
                throw ParserError.ExpectToken(LTLToken.RParen)
            }
        default:
            throw ParserError.UnexpectedToken(current)
        }
    }
}

enum ParserError: Error {
    case ExpectToken(LTLToken)
    case UnexpectedToken(LTLToken)
}
