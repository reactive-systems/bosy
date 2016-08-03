
class TPTP3Printer: ReturnConstantVisitor<String> {
    
    init() {
        super.init(constant: "")
    }
    
    override func visit(proposition: Proposition) -> T {
        return "p(\(proposition.name.uppercased()))"
    }
    override func visit(unaryOperator: UnaryOperator) -> T {
        return "~" + unaryOperator.operand.accept(visitor: self)
    }
    override func visit(binaryOperator: BinaryOperator) -> T {
        assert(binaryOperator.type == .Or)
        let clause = binaryOperator.operands.map({ $0.accept(visitor: self) }).joined(separator: " | ")
        return "(\(clause))"
    }
    override func visit(application: FunctionApplication) -> T {
        let parameters = application.application.map({ $0.name.uppercased() }).joined(separator: ",")
        return "\(application.function)(\(parameters))"
    }
    
}