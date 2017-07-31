
extension LTL {
    
    /**
     * Allows printing of LTL formula in SMV compatible format
     */
    public var smv: String? {
        return toSMV()
    }
    
    private func toSMV() -> String? {
        
        var smvOperatorMapping: [LTLToken:String] = [:]
        smvOperatorMapping[.Or] = "|"
        smvOperatorMapping[.And] = "&"
        smvOperatorMapping[.Implies] = "->"
        smvOperatorMapping[.Equivalent] = "<->"
        smvOperatorMapping[.Next] = "X"
        smvOperatorMapping[.Until] = "U"
        smvOperatorMapping[.Release] = "V"
        smvOperatorMapping[.Eventually] = "F"
        smvOperatorMapping[.Globally] = "G"
        
        switch self {
        case .Proposition(let name):
            return name
        case .Literal(let val):
            return val ? "TRUE" : "FALSE"
        case .UnaryOperator(.Not, let scope):
            guard let smvScope = scope.toSMV() else {
                return nil
            }
            return "!(\(smvScope))"
        case .UnaryOperator(let op, let scope):
            guard let smvOp = smvOperatorMapping[op] else {
                return nil
            }
            guard let smvScope = scope.toSMV() else {
                return nil
            }
            return "\(smvOp) (\(smvScope))"
        case .BinaryOperator(let op, let lhs, let rhs):
            guard let smvOp = smvOperatorMapping[op] else {
                fatalError()
            }
            guard let smvLhs = lhs.toSMV() else {
                return nil
            }
            guard let smvRhs = rhs.toSMV() else {
                return nil
            }
            
            return "(\(smvLhs) \(smvOp) \(smvRhs))"
        }
    }
    
}

