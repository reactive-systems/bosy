struct LTLParser {
    var lexer: LTLLexer
    var current: LTLToken
    var symbolTable: [String:LTLAtomicProposition]
    var paths: [String:LTLPathVariable]
    
    init(lexer: LTLLexer) {
        self.lexer = lexer
        self.current = .Proposition("dummy")
        self.symbolTable = [:]
        self.paths = [:]
    }
    
    mutating func parse() throws -> LTL {
        current = try self.lexer.next()
        return try parseQuantifiedExpression()
    }

    /**
     * Quantified expressions have the following syntax:
     *
     *     quantifier parameter_list . body
     *
     * e.g.,
     *
     *     exists pi1 pi2 . a[pi1] || b[pi2]
     */
    mutating func parseQuantifiedExpression() throws -> LTL {
        guard current.isQuantifier else {
            return try parseBinaryExpression(minPrecedence: LTLOperatorPrecedence.min)
        }
        let quant = current
        current = try lexer.next()
        let parameters = try parseParameterList()
        assert(current == .dot)
        current = try lexer.next()


        guard let ltlQuant = quant.ltlQuant else {
            fatalError()
        }
        var boundPathVariables: [LTLPathVariable] = []
        for element in parameters {
            guard case .Proposition(let name) = element else {
                fatalError()
            }
            let pathVariable = LTLPathVariable(name: name)
            if paths[name] != nil {
                fatalError("path variable \(pathVariable) already bound")
            }
            paths[name] = pathVariable
            boundPathVariables.append(pathVariable)
        }

        let body = try parseQuantifiedExpression()

        // remove bound path variables
        paths = paths.filter({ (key, value) in !boundPathVariables.contains(value) })

        return .pathQuantifier(ltlQuant, parameters: boundPathVariables, body: body)
    }

    mutating func parseParameterList() throws -> [LTLToken] {
        var list: [LTLToken] = []
        while current != .dot {
            guard case .Proposition(_) = current else {
                throw ParserError.ExpectToken(LTLToken.Proposition(""))
            }
            list.append(current)
            current = try lexer.next()
        }
        return list
    }
    
    mutating func parseBinaryExpression(minPrecedence: LTLOperatorPrecedence) throws -> LTL {
        var lhs = try parseUnaryExpression()
        
        while current.isBinaryOperator && current.precedence >= minPrecedence {
            let op = current
            current = try lexer.next()
            let rhs = try parseBinaryExpression(minPrecedence: op.precedence.next())
            guard let fun = op.ltlFunc else {
                fatalError()
            }
            lhs = .application(fun, parameters: [lhs, rhs])
        }
        
        return lhs
    }
    
    mutating func parseUnaryExpression() throws -> LTL {
        if current.isUnaryOperator {
            let op = current
            current = try lexer.next()
            guard let fun = op.ltlFunc else {
                fatalError()
            }
            return .application(fun, parameters: [try parseUnaryExpression()])
        }
        else {
            return try parsePrimaryExpression()
        }
    }
    
    mutating func parsePrimaryExpression() throws -> LTL {
        switch current {
        case .Proposition(let name):
            current = try lexer.next()
            let proposition = symbolTable[name, default: LTLAtomicProposition(name: name)]
            if current == .LBracket {
                // path variable
                current = try lexer.next()
                guard case .Proposition(let path) = current else {
                    throw ParserError.ExpectToken(LTLToken.Proposition(""))
                }
                guard let pathVariable = paths[path] else {
                    fatalError("path variable \(path) is not bound by a quantifier")
                }
                current = try lexer.next()
                guard current == .RBracket else {
                    throw ParserError.ExpectToken(LTLToken.RBracket)
                }
                current = try lexer.next()
                return .pathProposition(proposition, pathVariable)
            }
            return .atomicProposition(proposition)
        case .True:
            current = try lexer.next()
            return .application(LTLFunction.tt, parameters: [])
        case .False:
            current = try lexer.next()
            return .application(LTLFunction.ff, parameters: [])
        case .LParen:
            current = try lexer.next()
            let expr = try parseQuantifiedExpression()
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
