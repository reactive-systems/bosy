
public class TPTP3Printer: ReturnConstantVisitor<String> {
    public init() {
        super.init(constant: "")
    }

    override public func visit(proposition: Proposition) -> T {
        "p(\(proposition.name.uppercased()))"
    }

    override public func visit(unaryOperator: UnaryOperator) -> T {
        assert(unaryOperator.type == .Negation)
        return "~" + unaryOperator.operand.accept(visitor: self)
    }

    override public func visit(binaryOperator: BinaryOperator) -> T {
        assert(binaryOperator.type == .Or)
        let clause = binaryOperator.operands.map { $0.accept(visitor: self) }.joined(separator: " | ")
        return "(\(clause))"
    }

    override public func visit(application: FunctionApplication) -> T {
        let parameter: [Proposition] = application.application as! [Proposition]
        let parameters = parameter.map { $0.name.uppercased() }.joined(separator: ",")
        return "\(application.function)(\(parameters))"
    }
}

public class SmtPrinter: ReturnConstantVisitor<String> {
    public init() {
        super.init(constant: "")
    }

    override public func visit(literal: Literal) -> T {
        if literal == Literal.True {
            return "true"
        } else {
            return "false"
        }
    }

    override public func visit(proposition: Proposition) -> T {
        proposition.name
    }

    override public func visit(unaryOperator: UnaryOperator) -> T {
        "(not " + unaryOperator.operand.accept(visitor: self) + ")"
    }

    override public func visit(binaryOperator: BinaryOperator) -> T {
        let operands = binaryOperator.operands.map { $0.accept(visitor: self) }.joined(separator: " ")
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

    override public func visit(application: FunctionApplication) -> T {
        let parameter: [Logic] = application.application
        let parameters = parameter.map { $0.accept(visitor: self) }.joined(separator: " ")
        return "(\(application.function) \(parameters))"
    }

    override public func visit(comparator: BooleanComparator) -> T {
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

public class SmvPrinter: ReturnConstantVisitor<String> {
    public init() {
        super.init(constant: "")
    }

    override public func visit(literal: Literal) -> T {
        if literal == Literal.True {
            return "TRUE"
        } else {
            return "FALSE"
        }
    }

    override public func visit(proposition: Proposition) -> T {
        proposition.name
    }

    override public func visit(unaryOperator: UnaryOperator) -> T {
        "!" + unaryOperator.operand.accept(visitor: self)
    }

    override public func visit(binaryOperator: BinaryOperator) -> T {
        let operands = binaryOperator.operands.map { $0.accept(visitor: self) }
        let type: String
        switch binaryOperator.type {
        case .And:
            type = " & "
        case .Or:
            type = " | "
        default:
            fatalError()
        }
        return "(\(operands.joined(separator: type)))"
    }
}

public class VerilogPrinter: ReturnConstantVisitor<String> {
    public init() {
        super.init(constant: "")
    }

    override public func visit(literal: Literal) -> T {
        if literal == Literal.True {
            return "1"
        } else {
            return "0"
        }
    }

    override public func visit(proposition: Proposition) -> T {
        proposition.name
    }

    override public func visit(unaryOperator: UnaryOperator) -> T {
        "!" + unaryOperator.operand.accept(visitor: self)
    }

    override public func visit(binaryOperator: BinaryOperator) -> T {
        let operands = binaryOperator.operands.map { $0.accept(visitor: self) }
        let type: String
        switch binaryOperator.type {
        case .And:
            type = " && "
        case .Or:
            type = " || "
        default:
            fatalError()
        }
        return "(\(operands.joined(separator: type)))"
    }
}
