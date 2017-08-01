import Foundation

import Utils

public typealias BooleanAssignment = [Proposition: Literal]

public protocol Logic: CustomStringConvertible {
    func accept<T>(visitor: T) -> T.T where T: BooleanVisitor
    
    func eval(assignment: BooleanAssignment) -> Logic
    
    func simplify() -> Logic
    
    var hashValue: Int { get }
}

public func ==(lhs: Logic, rhs: Logic) -> Bool {
    switch (lhs, rhs) {
    case let (lhs as Proposition, rhs as Proposition):
        return lhs == rhs
    case let (lhs as UnaryOperator, rhs as UnaryOperator):
        return lhs.operand == rhs.operand
    default:
        //assert(type(of: lhs) != type(of: rhs))
        return false
    }
}

public func ==(lhs: [Logic], rhs: [Logic]) -> Bool {
    if lhs.count != rhs.count {
        return false
    }
    return zip(lhs, rhs).reduce(true, { res, pair in res && pair.0 == pair.1 })
}

public func & (lhs: Logic, rhs: Logic) -> Logic {
    switch (lhs, rhs) {
    case (let element as Literal, _):
        if element == Literal.True {
            return rhs
        } else if element == Literal.False {
            return Literal.False
        }
    case (_, let element as Literal):
        if element == Literal.True {
            return lhs
        } else if element == Literal.False {
            return Literal.False
        }
    case (let element_lhs as BinaryOperator, let element_rhs as BinaryOperator):
        if element_lhs.type == .And && element_rhs.type == .And {
            return BinaryOperator(.And, operands: element_lhs.operands + element_rhs.operands)
        }
    case (let element as BinaryOperator, _):
        if element.type == .And {
            return BinaryOperator(.And, operands: element.operands + [rhs])
        }
    case (_, let element as BinaryOperator):
        if element.type == .And {
            return BinaryOperator(.And, operands: [lhs] + element.operands)
        }
    default:
        break
    }
    return BinaryOperator(.And, operands: [lhs, rhs])
}

public func | (lhs: Logic, rhs: Logic) -> Logic {
    switch (lhs, rhs) {
    case (let element as Literal, _):
        if element == Literal.True {
            return Literal.True
        } else {
            assert(element == Literal.False)
            return rhs
        }
    case (_, let element as Literal):
        if element == Literal.True {
            return Literal.True
        } else {
            assert(element == Literal.False)
            return lhs
        }
    case (let element_lhs as BinaryOperator, let element_rhs as BinaryOperator):
        if element_lhs.type == .Or && element_rhs.type == .Or {
            return BinaryOperator(.Or, operands: element_lhs.operands + element_rhs.operands)
        }
    case (let element as BinaryOperator, _):
        if element.type == .Or {
            return BinaryOperator(.Or, operands: element.operands + [rhs])
        }
    case (_, let element as BinaryOperator):
        if element.type == .Or {
            return BinaryOperator(.Or, operands: [lhs] + element.operands)
        }
    default:
        break
    }
    return BinaryOperator(.Or, operands: [lhs, rhs])
}

infix operator -->

public func --> (lhs: Logic, rhs: Logic) -> Logic {
    switch (lhs, rhs) {
    case (let element as Literal, _):
        if element == Literal.False {
            return Literal.True
        } else {
            assert(element == Literal.True)
            return rhs
        }
    case (_, let element as Literal):
        if element == Literal.True {
            return Literal.True
        } else {
            assert(element == Literal.False)
            return !lhs
        }
    default:
        break
    }
    return BinaryOperator(.Or, operands: [!lhs, rhs])
}

infix operator <->

public func <-> (lhs: Logic, rhs: Logic) -> Logic {
    switch (lhs, rhs) {
    case (let lhsLiteral as Literal, let rhsLiteral as Literal):
        return lhsLiteral == rhsLiteral ? Literal.True : Literal.False
    case (let element as Literal, _):
        if element == Literal.True {
            return rhs
        } else if element == Literal.False {
            return !rhs
        }
    case (_, let element as Literal):
        if element == Literal.True {
            return lhs
        } else if element == Literal.False {
            return !lhs
        }
    default:
        break
    }
    return BinaryOperator(.Xnor, operands: [lhs, rhs])
}

public func ^ (lhs: Logic, rhs: Logic) -> Logic {
    switch (lhs, rhs) {
    case (let lhsLiteral as Literal, let rhsLiteral as Literal):
        return lhsLiteral != rhsLiteral ? Literal.True : Literal.False
    case (let element as Literal, _):
        if element == Literal.True {
            return !rhs
        } else if element == Literal.False {
            return rhs
        }
    case (_, let element as Literal):
        if element == Literal.True {
            return !lhs
        } else if element == Literal.False {
            return lhs
        }
    default:
        break
    }
    return BinaryOperator(.Xor, operands: [lhs, rhs])
}

public prefix func ! (op: Logic) -> Logic {
    switch op {
    case let element as UnaryOperator:
        if element.type == .Negation {
            return element.operand
        }
    case let element as Literal:
        return element == Literal.True ? Literal.False: Literal.True
    default:
        break
    }
    return UnaryOperator(.Negation, operand: op)
}

public struct UnaryOperator: Logic, Equatable {
    public enum OperatorType: CustomStringConvertible {
        case Negation
        
        public var description: String {
            switch self {
            case .Negation:
                return "¬"
            }
        }
    }
    
    public let type: OperatorType
    public var operand: Logic
    
    init(_ type: OperatorType, operand: Logic) {
        self.type = type
        self.operand = operand
    }
    
    public func accept<T>(visitor: T) -> T.T where T: BooleanVisitor {
        return visitor.visit(unaryOperator: self)
    }
    
    public var description: String {
        return "\(type)\(operand)"
    }
    
    public var hashValue: Int {
        return 1 ^ operand.hashValue
    }
    
    public func eval(assignment: BooleanAssignment) -> Logic {
        return !operand.eval(assignment: assignment)
    }
    
    public func simplify() -> Logic {
        return self
    }
}

public func ==(_ lhs: UnaryOperator, _ rhs: UnaryOperator) -> Bool {
    return lhs.type == rhs.type
        && lhs.operand == rhs.operand
}

public struct BinaryOperator: Logic, Hashable {
    public enum OperatorType: CustomStringConvertible {
        case And
        case Or
        case Xnor
        case Xor
        
        public var description: String {
            switch self {
            case .And:
                return "∧"
            case .Or:
                return "∨"
            case .Xnor:
                return "↔︎"
            case .Xor:
                return "⊕"
            }
        }
        
        public var negated: OperatorType {
            switch self {
            case .And:
                return .Or
            case .Or:
                return .And
            case .Xnor:
                return .Xor
            case .Xor:
                return .Xnor
            }
        }
    }
    
    public let type: OperatorType
    public var operands: [Logic]
    
    public init(_ type: OperatorType, operands: [Logic]) {
        self.type = type
        self.operands = operands
    }
    
    public func accept<T>(visitor: T) -> T.T where T: BooleanVisitor {
        return visitor.visit(binaryOperator: self)
    }
    
    public var description: String {
        let expression = operands.map({ op in "\(op)" }).joined(separator: " \(type) ")
        return "(\(expression))"
    }
    
    // Conformance Hashable
    public var hashValue: Int {
        return type.hashValue ^ operands.reduce(0, { hash, op in hash ^ op.hashValue })
    }
    
    public func eval(assignment: BooleanAssignment) -> Logic {
        let evaluatedOperands = operands.map({ $0.eval(assignment: assignment) })
        switch type {
        case .And:
            return evaluatedOperands.reduce(Literal.True, &)
        case .Or:
            return evaluatedOperands.reduce(Literal.False, |)
        case .Xnor:
            assert(evaluatedOperands.count == 2)
            return evaluatedOperands[0] <-> evaluatedOperands[1]
        case .Xor:
            assert(evaluatedOperands.count == 2)
            return evaluatedOperands[0] ^ evaluatedOperands[1]
        }
    }
    
    public func simplify() -> Logic {
        let newOperands = operands.map({ $0.simplify() })
        switch type {
        case .And:
            // check for duplication
            var reducedOperands = newOperands
            for operand in newOperands {
                if operand as? Literal != nil && operand as! Literal == Literal.False {
                    return Literal.False
                }
                reducedOperands = newOperands.filter({ !($0 == operand) })
                if operand as? Literal == nil {
                    reducedOperands.append(operand)
                } else {
                    assert(operand as! Literal == Literal.True)
                }
            }
            
            // simple conflict check
            for operand in reducedOperands {
                guard let op = operand as? Proposition else {
                    continue
                }
                if reducedOperands.contains(where: { $0 == !op }) {
                    return Literal.False
                }
            }
            return BinaryOperator(type, operands: reducedOperands)
        case .Or:
            // check for duplication
            var reducedOperands = newOperands
            for operand in newOperands {
                if operand as? Literal != nil && operand as! Literal == Literal.True {
                    return Literal.True
                }
                reducedOperands = newOperands.filter({ !($0 == operand) })
                if operand as? Literal == nil {
                    reducedOperands.append(operand)
                } else {
                    assert(operand as! Literal == Literal.False)
                }
            }
            
            // simple conflict check
            for operand in reducedOperands {
                guard let op = operand as? Proposition else {
                    continue
                }
                if reducedOperands.contains(where: { $0 == !op }) {
                    return Literal.True
                }
            }
            return BinaryOperator(type, operands: reducedOperands)
        case .Xnor:
            assert(newOperands.count == 2)
            return BinaryOperator(type, operands: newOperands)
        case .Xor:
            assert(newOperands.count == 2)
            return BinaryOperator(type, operands: newOperands)
        }
    }
}

public func ==(_ lhs: BinaryOperator, _ rhs: BinaryOperator) -> Bool {
    return lhs.type == rhs.type
        && lhs.operands.count == rhs.operands.count
        && zip(lhs.operands, rhs.operands).map(==).reduce(true, { $0 && $1 })
}

public struct Quantifier: Logic {
    public enum QuantifierType: CustomStringConvertible {
        case Exists
        case Forall
        
        public var description: String {
            switch self {
            case .Exists:
                return "∃"
            case .Forall:
                return "∀"
            }
        }
    }
    
    public let type: QuantifierType
    public var variables: [Proposition]
    public var scope: Logic
    public let arity: Int
    
    public init(_ type: QuantifierType, variables: [Proposition], scope: Logic, arity: Int = 0) {
        self.type = type
        self.variables = variables
        self.scope = scope
        self.arity = arity
    }
    
    public func accept<T>(visitor: T) -> T.T where T : BooleanVisitor {
        return visitor.visit(quantifier: self)
    }
    
    public var description: String {
        let variables = self.variables.map({ variable in "\(variable)" }).joined(separator: ", ")
        return "\(type) \(variables): \(scope)"
    }
    
    public var hashValue: Int {
        return type.hashValue ^ variables.reduce(0, { hash, prop in hash ^ prop.hashValue })
    }
    
    public func eval(assignment: BooleanAssignment) -> Logic {
        var copy = self
        copy.scope = scope.eval(assignment: assignment)
        copy.variables = variables.filter({ assignment[$0] == nil })
        if copy.variables.count == 0 {
            return copy.scope
        }
        return copy
    }
    
    public func simplify() -> Logic {
        return self
    }
}

public func ==(lhs: Quantifier, rhs: Quantifier) -> Bool {
    return lhs.type == rhs.type
        && lhs.variables.count == rhs.variables.count
        && zip(lhs.variables, rhs.variables).map(==).reduce(true, { $0 && $1 })
        && lhs.scope == rhs.scope
}

public struct Literal: Logic, Equatable {
    public enum LiteralType: CustomStringConvertible {
        case True
        case False
        
        public var description: String {
            switch self {
            case .True:
                return "⊤"
            case .False:
                return "⊥"
            }
        }
    }
    
    public let type: LiteralType
    
    public static let True = Literal(.True)
    public static let False = Literal(.False)
    
    internal init(_ type: LiteralType) {
        self.type = type
    }
    
    public func accept<T>(visitor: T) -> T.T where T : BooleanVisitor {
        return visitor.visit(literal: self)
    }
    
    public var description: String {
        return "\(type)"
    }
    
    public var hashValue: Int {
        return type.hashValue
    }
    
    public func eval(assignment: BooleanAssignment) -> Logic {
        return self
    }
    
    public func simplify() -> Logic {
        return self
    }
}

public func ==(lhs: Literal, rhs: Literal) -> Bool {
    return lhs.type == rhs.type
}

public struct Proposition: Logic, Equatable, Hashable {
    public var name: String
    
    public init(_ name: String) {
        precondition(!name.isEmpty)
        self.name = name
    }
    
    public func accept<T>(visitor: T) -> T.T where T: BooleanVisitor {
        return visitor.visit(proposition: self)
    }
    
    public var description: String {
        return "\(name)"
    }
    
    public var hashValue: Int {
        return name.hashValue
    }
    
    public func eval(assignment: BooleanAssignment) -> Logic {
        guard let value = assignment[self] else {
            return self
        }
        return value
    }
    
    public func simplify() -> Logic {
        return self
    }
}

public func ==(lhs: Proposition, rhs: Proposition) -> Bool {
    return lhs.name == rhs.name
}

public struct BooleanComparator: Logic {
    public enum ComparatorType: CustomStringConvertible {
        case LessOrEqual
        case Less
        
        public var description: String {
            switch self {
            case .LessOrEqual:
                return "≤"
            case .Less:
                return "<"
            }
        }
    }
    
    public let type: ComparatorType
    public var lhs: Logic
    public var rhs: Logic
    
    public init(_ type: ComparatorType, lhs: Logic, rhs: Logic) {
        self.type = type
        self.lhs = lhs
        self.rhs = rhs
    }
    
    public func accept<T>(visitor: T) -> T.T where T: BooleanVisitor {
        return visitor.visit(comparator: self)
    }
    
    public var description: String {
        return "\(lhs) \(type) \(rhs)"
    }
    
    public var hashValue: Int {
        return type.hashValue ^ lhs.hashValue ^ rhs.hashValue
    }
    
    public func eval(assignment: BooleanAssignment) -> Logic {
        //assert(assignment[lhs] == nil)
        //assert(assignment[rhs] == nil)
        return self
    }
    
    public func simplify() -> Logic {
        return self
    }
}

public struct FunctionApplication: Logic, Hashable {
    public var function: Proposition
    public var application: [Logic]
    
    public init(function: Proposition, application: [Logic]) {
        self.function = function
        self.application = application
    }
    
    public func accept<T>(visitor: T) -> T.T where T: BooleanVisitor {
        return visitor.visit(application: self)
    }
    
    public var description: String {
        let appl = application.map({ "\($0)" }).joined(separator: ", ")
        return "\(function)(\(appl))"
    }
    
    public var hashValue: Int {
        return function.hashValue ^ application.reduce(0, { val, prop in val ^ prop.hashValue })
    }
    
    public func eval(assignment: BooleanAssignment) -> Logic {
        assert(false)
        return self
    }
    
    public func simplify() -> Logic {
        return self
    }
    
    public static func == (lhs: FunctionApplication, rhs: FunctionApplication) -> Bool {
        return lhs.function == rhs.function
            && lhs.application == rhs.application
    }
}

public protocol BooleanVisitor {
    associatedtype T
    func visit(literal: Literal) -> T
    func visit(proposition: Proposition) -> T
    func visit(unaryOperator: UnaryOperator) -> T
    func visit(binaryOperator: BinaryOperator) -> T
    func visit(quantifier: Quantifier) -> T
    func visit(comparator: BooleanComparator) -> T
    func visit(application: FunctionApplication) -> T
}

/**
 * Recursively traverses syntax tree and returns a modified tree (standard modification is identity function)
 *
 * Subclassing: override methods that perform the actual modification
 */
public class TransformingVisitor: BooleanVisitor {
    public typealias T = Logic
    
    public func visit(literal: Literal) -> T {
        return literal
    }
    public func visit(proposition: Proposition) -> T {
        return proposition
    }
    public func visit(unaryOperator: UnaryOperator) -> T {
        var copy = unaryOperator
        copy.operand = unaryOperator.operand.accept(visitor: self)
        return copy
    }
    public func visit(binaryOperator: BinaryOperator) -> T {
        var copy = binaryOperator
        copy.operands = binaryOperator.operands.map({ $0.accept(visitor: self) })
        return copy
    }
    public func visit(quantifier: Quantifier) -> T {
        var copy = quantifier
        copy.scope = quantifier.scope.accept(visitor: self)
        return copy
    }
    public func visit(comparator: BooleanComparator) -> T {
        var copy = comparator
        copy.lhs = comparator.lhs.accept(visitor: self) as! Proposition
        copy.rhs = comparator.rhs.accept(visitor: self) as! Proposition
        return copy
    }
    public func visit(application: FunctionApplication) -> T {
        var copy = application
        copy.function = application.function.accept(visitor: self) as! Proposition
        copy.application = application.application.map({ $0.accept(visitor: self) as! Proposition })
        return copy
    }
}

public class RenamingBooleanVisitor: TransformingVisitor {
    public typealias T = Logic
    
    var rename: (String) -> String
    
    public init(rename: @escaping (String) -> String) {
        self.rename = rename
    }
    
    public override func visit(proposition: Proposition) -> T {
        var copy = proposition
        copy.name = rename(proposition.name)
        return copy
    }
}

public class ReplacingPropositionVisitor: TransformingVisitor {
    public typealias T = Logic
    
    var replace: (Proposition) -> Logic?
    
    public init(replace: @escaping (Proposition) -> Logic?) {
        self.replace = replace
    }
    
    public override func visit(proposition: Proposition) -> T {
        guard let replaced = replace(proposition) else {
            return proposition
        }
        return replaced
    }
}

/**
 * Recursively traverses syntax tree and returns whether formula satisfies a property (default property is constant true)
 *
 * Subclassing: override methods that perform the actual checking
 */
public class CheckingVisitor: BooleanVisitor {
    public typealias T = Bool
    
    public func visit(literal: Literal) -> T {
        return true
    }
    public func visit(proposition: Proposition) -> T {
        return true
    }
    public func visit(unaryOperator: UnaryOperator) -> T {
        return unaryOperator.operand.accept(visitor: self)
    }
    public func visit(binaryOperator: BinaryOperator) -> T {
        return binaryOperator.operands.map({ $0.accept(visitor: self) }).reduce(true, { $0 && $1 })
    }
    public func visit(quantifier: Quantifier) -> T {
        return quantifier.scope.accept(visitor: self)
    }
    public func visit(comparator: BooleanComparator) -> T {
        return comparator.lhs.accept(visitor: self) && comparator.rhs.accept(visitor: self)
    }
    public func visit(application: FunctionApplication) -> T {
        return application.function.accept(visitor: self) && application.application.map({ $0.accept(visitor: self) }).reduce(true, { $0 && $1 })
    }
}

public class BoundednessVisitor: CheckingVisitor {
    
    var bounded: Set<Proposition>
    
    public override init() {
        bounded = Set()
    }
    
    public override func visit(proposition: Proposition) -> T {
        if !bounded.contains(proposition) {
            Logger.default().error("\(proposition) is not bound\n(\(bounded))")
        }
        return bounded.contains(proposition)
    }
    public override func visit(quantifier: Quantifier) -> T {
        bounded = bounded.union(quantifier.variables)
        defer {
            bounded = bounded.subtracting(quantifier.variables)
        }
        return quantifier.scope.accept(visitor: self)
    }
    public override func visit(application: FunctionApplication) -> T {
        if !bounded.contains(application.function) {
            Logger.default().error("\(application.function) is not bound\n(\(bounded))")
            return false
        }
        return application.application.map({ $0.accept(visitor: self) }).reduce(true, { $0 && $1 })
    }
}

public class ReturnConstantVisitor<R>: BooleanVisitor {
    public typealias T = R
    
    let constant: R
    
    init(constant: R) {
        self.constant = constant
    }
    
    public func visit(literal: Literal) -> T {
        assert(false)
        return constant
    }
    public func visit(proposition: Proposition) -> T {
        assert(false)
        return constant
    }
    public func visit(unaryOperator: UnaryOperator) -> T {
        assert(false)
        return constant
    }
    public func visit(binaryOperator: BinaryOperator) -> T {
        assert(false)
        return constant
    }
    public func visit(quantifier: Quantifier) -> T {
        assert(false)
        return constant
    }
    public func visit(comparator: BooleanComparator) -> T {
        assert(false)
        return constant
    }
    public func visit(application: FunctionApplication) -> T {
        assert(false)
        return constant
    }
}

public func order(binaryLhs: [Logic], binaryRhs: [Logic], strict: Bool) -> Logic {
    precondition(binaryLhs.count == binaryRhs.count)
    precondition(binaryLhs.count >= 1)
    var binaryLhs = binaryLhs
    var binaryRhs = binaryRhs
    
    
    let lhs = binaryLhs.removeFirst()
    let rhs = binaryRhs.removeFirst()
    
    let greater = lhs & !rhs
    let equiv = BinaryOperator(.Xnor, operands: [lhs, rhs])
    if binaryLhs.count > 0 {
        let recursive = equiv & order(binaryLhs: binaryLhs, binaryRhs: binaryRhs, strict: strict)
        return greater | recursive
    } else if strict {
        return greater
    } else {
        return equiv
    }
}

public func allBooleanAssignments(variables: [Proposition]) -> [BooleanAssignment] {
    var zeroAssignment: BooleanAssignment = [:]
    variables.forEach({ v in zeroAssignment[v] = Literal.False })
    var assignments: [BooleanAssignment] = [zeroAssignment]
    for v in variables {
        assignments = assignments.reduce([], {
            newAssignments, element in
            var copy = element
            copy[v] = Literal.True
            return newAssignments + [ element, copy ]
        })
    }
    return assignments
}

public func bitStringFromAssignment(_ assignment: BooleanAssignment) -> String {
    var bitstring = ""
    for key in assignment.keys.sorted(by: { $0.name < $1.name }) {
        let value = assignment[key]!
        if value == Literal.True {
            bitstring += "1"
        } else {
            bitstring += "0"
        }
    }
    return bitstring
}

/*struct PrettifyBoolean: BooleanVisitor {
    typealias T = String
    
    func visit(literal: Literal) -> String {
        return "\(literal.type)"
    }
    
    func visit(proposition: Proposition) -> String {
        return proposition.name
    }
    
    func visit(unaryOperator: UnaryOperator) -> String {
        return "\(unaryOperator.type)\(unaryOperator.operand.accept(visitor: self))"
    }
    
    func visit(binaryOperator: BinaryOperator) -> String {
        let subExpression = binaryOperator.operands.map({ op in op.accept(visitor: self) }).joined(separator: " \(binaryOperator.type) ")
        return "(\(subExpression))"
    }
    
    func visit(quantifier: Quantifier) -> String {
        let variables = quantifier.variables.map({ variable in variable.accept(visitor: self) }).joined(separator: ", ")
        return "\(quantifier.type) \(variables): \(quantifier.operand.accept(visitor: self))"
    }
}*/

enum BooleanToken {
    typealias Precedence = Int
    
    case Literal(Bool)
    case Proposition(String)
    case Conjunction
    case Disjunction
    case Negation
    case LParen
    case RParen
    case EOF
    
    var isUnaryOperator: Bool {
        switch self {
        case .Negation:
            return true
        default:
            return false
        }
    }
    
    var isBinaryOperator: Bool {
        switch self {
        case .Conjunction:
            return true
        case .Disjunction:
            return true
        default:
            return false
        }
    }
    
    var precedence: Precedence {
        precondition(isBinaryOperator)
        switch self {
        case .Conjunction:
            return 3
        case .Disjunction:
            return 2
        default:
            assert(false)
            return 0
        }
    }
}

enum BooleanError: Error {
    case EndOfInput
    case Unexpected
    case Expect(BooleanToken)
}

struct BooleanLexer {
    let scanner: ScalarScanner
    
    func next() throws -> BooleanToken {
        if scanner.isAtEnd() {
            return .EOF
        }
        switch scanner {
        case "(":
            return .LParen
        case ")":
            return .RParen
        case ["~", "!"]:
            return .Negation
        case ["||", "|", "\\/", "+"]:
            return .Disjunction
        case ["&&", "&", "/\\", "*"]:
            return .Conjunction
        case "0":
            return .Literal(false)
        case "1":
            return .Literal(true)
        case "false":
            return .Literal(false)
        case "true":
            return .Literal(true)
        case "a"..."z":
            return .Proposition(scanner.getIdentifier())
        default:
            throw BooleanError.Unexpected
        }
    }
}

/**
 * Recursive decent parser
 */
struct BooleanParser {
    let lexer: BooleanLexer
    var current: BooleanToken = .EOF
    init(lexer: BooleanLexer) {
        self.lexer = lexer
    }
    
    mutating func parse() throws -> Logic {
        current = try lexer.next()
        return try parseExpression(minPrecedence: 0)
    }
    
    mutating func parseExpression(minPrecedence: BooleanToken.Precedence) throws -> Logic {
        var lhs = try parseUnaryExpression()
        
        while current.isBinaryOperator && current.precedence >= minPrecedence {
            let op = current
            current = try lexer.next()
            let rhs = try parseExpression(minPrecedence: op.precedence + 1)
            switch op {
            case .Disjunction:
                lhs = lhs | rhs
            case .Conjunction:
                lhs = lhs & rhs
            default:
                assert(false)
            }
        }
        
        return lhs
    }
    
    mutating func parseUnaryExpression() throws -> Logic {
        if current.isUnaryOperator {
            current = try lexer.next()
            return !(try parseUnaryExpression())
        }
        else {
            return try parsePrimaryExpression()
        }
    }
    
    mutating func parsePrimaryExpression() throws -> Logic {
        switch current {
        case .Literal(let value):
            current = try lexer.next()
            return value ? Literal.True : Literal.False
        case .Proposition(let name):
            current = try lexer.next()
            return Proposition(name)
        case .LParen:
            current = try lexer.next()
            let expr = try parseExpression(minPrecedence: 0)
            switch current {
            case .RParen:
                current = try lexer.next()
                return expr
            default:
                throw BooleanError.Expect(BooleanToken.RParen)
            }
        default:
            throw BooleanError.Unexpected
        }
    }
}

func ~=(pattern: String, prefix: ScalarScanner) -> Bool {
    return prefix.matchAndProceed(pattern: pattern)
}

func ~=(patterns: [String], prefix: ScalarScanner) -> Bool {
    for pattern in patterns {
        if prefix.matchAndProceed(pattern: pattern) {
            return true
        }
    }
    return false
}

func ~=(range: ClosedRange<UnicodeScalar>, prefix: ScalarScanner) -> Bool {
    return prefix.firstScalarContained(inRange: range)
}

class ScalarScanner {
    let scalars: String.UnicodeScalarView
    var index: String.UnicodeScalarView.Index
    
    init(scalars: String.UnicodeScalarView) {
        self.scalars = scalars
        self.index = scalars.startIndex
    }
    
    func advance(by offset: String.UnicodeScalarView.IndexDistance, skipWhitespace: Bool = true) {
        index = scalars.index(index, offsetBy: offset)
        if !skipWhitespace {
            return
        }
        while (index < scalars.endIndex && NSCharacterSet.whitespacesAndNewlines.contains(scalars[index])) {
            index = scalars.index(after: index)
        }
    }
    
    func matchAndProceed(pattern: String) -> Bool {
        if scalars[self.index..<scalars.endIndex].starts(with: pattern.unicodeScalars) {
            advance(by: pattern.unicodeScalars.count)
            return true
        }
        return false
    }
    
    func firstScalarContained(inRange range: ClosedRange<UnicodeScalar>) -> Bool {
        return range.contains(scalars[index])
    }
    
    func isAtEnd() -> Bool {
        return index >= scalars.endIndex
    }
    
    func getIdentifier() -> String {
        var end = index
        while end < scalars.endIndex && (
            ("a"..."z").contains(scalars[end])
            || ("A"..."Z").contains(scalars[end])
            || ("0"..."9").contains(scalars[end])
            || scalars[end] == "_"
            ) {
            end = scalars.index(after: end)
        }
        let literal = scalars[index..<end]
        index = end
        advance(by: 0)
        return String(literal)
    }
}

public enum BooleanUtils {
    public static func parse(string: String) -> Logic? {
        let lexer = BooleanLexer(scanner: ScalarScanner(scalars: string.unicodeScalars))
        var parser = BooleanParser(lexer: lexer)
        return try? parser.parse()
    }
}
