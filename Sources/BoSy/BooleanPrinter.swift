
class TPTP3Printer: ReturnConstantVisitor<String> {
    
    init() {
        super.init(constant: "")
    }
    
    override func visit(proposition: Proposition) -> T {
        return "p(\(proposition.name.uppercased()))"
    }
    override func visit(unaryOperator: UnaryOperator) -> T {
        assert(unaryOperator.type == .Negation)
        return "~" + unaryOperator.operand.accept(visitor: self)
    }
    override func visit(binaryOperator: BinaryOperator) -> T {
        assert(binaryOperator.type == .Or)
        let clause = binaryOperator.operands.map({ $0.accept(visitor: self) }).joined(separator: " | ")
        return "(\(clause))"
    }
    override func visit(application: FunctionApplication) -> T {
        let parameter: [Proposition] = application.application as! [Proposition]
        let parameters = parameter.map({ $0.name.uppercased() }).joined(separator: ",")
        return "\(application.function)(\(parameters))"
    }
    
}


class SmtPrinter: ReturnConstantVisitor<String> {
    init() {
        super.init(constant: "")
    }
    
    override func visit(proposition: Proposition) -> T {
        return proposition.name
    }
    override func visit(unaryOperator: UnaryOperator) -> T {
        return "(not " + unaryOperator.operand.accept(visitor: self) + ")"
    }
    override func visit(binaryOperator: BinaryOperator) -> T {
        let operands = binaryOperator.operands.map({ $0.accept(visitor: self) }).joined(separator: " ")
        let type: String
        switch binaryOperator.type {
        case .And:
            type = "and"
        case .Or:
            type = "or"
        case .Xnor:
            type = "iff"
        case .Xor:
            type = "xor"
        }
        return "(\(type) \(operands))"
    }
    override func visit(application: FunctionApplication) -> T {
        let parameter: [Logic] = application.application
        let parameters = parameter.map({ $0.accept(visitor: self) }).joined(separator: " ")
        return "(\(application.function) \(parameters))"
    }
    override func visit(comparator: BooleanComparator) -> T {
        let comp: String
        switch comparator.type {
        case .Less:
            comp = "<"
        case .LessOrEqual:
            comp = "<="
        }
        let lhs = comparator.lhs.accept(visitor: self)
        let rhs = comparator.rhs.accept(visitor: self)
        return "(\(comp) \(lhs) \(rhs))"
    }
}
