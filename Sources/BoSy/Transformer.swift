import Utils
import CAiger
import CAigerHelper

class RemoveComparableVisitor: TransformingVisitor {
    
    var reverseMapping: [Proposition: [Proposition]] = [:]
    var counterBits: Int
    
    init(bound: Int) {
        precondition(bound >= 1)
        counterBits = numBitsNeeded(bound)
    }
    
    override func visit(quantifier: Quantifier) -> T {
        var copy = quantifier
        copy.scope = quantifier.scope.accept(visitor: self)
        copy.variables = copy.variables.reduce([], combine: {
            variables, variable in variables + (reverseMapping[variable] ?? [variable])
        })
        return copy
    }
    override func visit(comparator: BooleanComparator) -> T {
        var lhs = reverseMapping[comparator.lhs as! Proposition]
        if lhs == nil {
            lhs = (0..<counterBits).map({ i in Proposition("\(comparator.lhs)_\(i)")})
            reverseMapping[comparator.lhs as! Proposition] = lhs!
        }
        var rhs = reverseMapping[comparator.rhs as! Proposition]
        if rhs == nil {
            rhs = (0..<counterBits).map({ i in Proposition("\(comparator.rhs)_\(i)")})
            reverseMapping[comparator.rhs as! Proposition] = rhs!
        }
        return order(binaryLhs: lhs!, binaryRhs: rhs!, strict: comparator.type == .Less)
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

public class DIMACSVisitor: ReturnConstantVisitor<Int>, CustomStringConvertible {
    
    var propositions: [Proposition:Int] = [:]
    var currentId = 1
    var dimacs: [String] = []
    var output: Int? = nil
    
    public init() {
        super.init(constant: 0)
    }
    
    public var description: String {
        let symboltable = propositions.map({
            (proposition, literal) in
            "c \(proposition) \(literal)\n"
        }).joined(separator: "")
        let header = "p cnf \(currentId) \(self.dimacs.count + 1)\n"
        let dimacs = self.dimacs.map({ $0 + " 0\n" }).joined(separator: "")
        assert(output != nil)
        return symboltable + header + dimacs + "\(output!) 0\n"
    }
    
    func newId() -> Int {
        defer {
            currentId += 1
        }
        return currentId
    }
    
    public override func visit(proposition: Proposition) -> T {
        return propositions[proposition]!
    }
    public override func visit(unaryOperator: UnaryOperator) -> T {
        return -unaryOperator.operand.accept(visitor: self)
    }
    public override func visit(binaryOperator: BinaryOperator) -> T {
        let subformulas: [Int] = binaryOperator.operands.map({ $0.accept(visitor: self) })
        let formulaId = newId()
        
        switch binaryOperator.type {
        case .And:
            dimacs += subformulas.map({ subformula in "-\(formulaId) \(subformula)" })
            dimacs.append("\(formulaId) " + subformulas.map(-).map(String.init).joined(separator: " "))
        case .Or:
            dimacs += subformulas.map({ subformula in "\(-subformula) \(formulaId)" })
            dimacs.append("-\(formulaId) " + subformulas.map(String.init).joined(separator: " "))
        case .Xnor:
            assert(subformulas.count == 2)
            let lhs = subformulas[0]
            let rhs = subformulas[1]
            dimacs.append("-\(formulaId) \(lhs) \(-rhs)")
            dimacs.append("-\(formulaId) \(-lhs) \(rhs)")
            dimacs.append("\(formulaId) \(lhs) \(rhs)")
            dimacs.append("\(formulaId) \(-lhs) \(-rhs)")
        case .Implication:
            assert(subformulas.count == 2)
            let lhs = subformulas[0]
            let rhs = subformulas[1]
            dimacs.append("\(lhs) \(formulaId)")
            dimacs.append("\(-rhs) \(formulaId)")
            dimacs.append("-\(formulaId) \(-lhs) \(rhs)")
        }
        return formulaId
    }
    public override func visit(quantifier: Quantifier) -> T {
        quantifier.variables.forEach({ variable in propositions[variable] = newId() })
        let result = quantifier.scope.accept(visitor: self)
        assert(result != 0)  // there is only one existential quantifier
        assert(output == nil)
        // top level scope
        output = result
        return 0
    }
    
    public func getAssignment(fromAssignment: [Int]) -> [Proposition:Literal] {
        var assignment: [Proposition:Literal] = [:]
        
        for (proposition, literal) in propositions {
            if fromAssignment.contains(literal) {
                assignment[proposition] = Literal.True
            } else if fromAssignment.contains(-literal) {
                assignment[proposition] = Literal.False
            }
        }
        
        return assignment
    }
}

public class QDIMACSVisitor: DIMACSVisitor {
    public typealias T = Int
    
    var quantifiers: [String] = []
    
    override public var description: String {
        let symboltable = propositions.map({
            (proposition, literal) in
            "c \(proposition) \(literal)\n"
        }).joined(separator: "")
        let header = "p cnf \(currentId) \(self.dimacs.count + 1)\n"
        let maxVar = propositions.values.reduce(Int.min, combine: max) + 1
        let dimacs = self.dimacs.map({ $0 + " 0\n" }).joined(separator: "")
        var quants = quantifiers
        quants.append("e " + (maxVar..<currentId).map(String.init).joined(separator: " ") + " 0")
        assert(output != nil)
        return symboltable + header + quants.joined(separator: "\n") + "\n" + dimacs + "\(output!) 0\n"
    }

    override public func visit(quantifier: Quantifier) -> T {
        quantifier.variables.forEach({ variable in propositions[variable] = newId() })
        let variables = quantifier.variables.flatMap({ variable in propositions[variable] })
        quantifiers.append((quantifier.type == .Exists ? "e " : "a ") + variables.map(String.init).joined(separator: " ") + " 0")
        let result = quantifier.scope.accept(visitor: self)
        if result != 0 {
            assert(output == nil)
            // top level scope
            output = result
        }
        return 0
    }
}

public class QCIRVisitor: ReturnConstantVisitor<Int>, CustomStringConvertible {
    
    var propositions: [Proposition:Int] = [:]
    var currentId = 1
    var circuit: [String] = []
    var quantifiers: [String] = []
    var output: Int? = nil
    
    public init() {
        super.init(constant: 0)
    }
    
    public var description: String {
        let symboltable = propositions.map({
            (proposition, literal) in
            "# \(proposition) \(literal)\n"
        }).joined(separator: "")
        let header = "#QCIR-G14 \(currentId)\n"
        let circuit = self.circuit.joined(separator: "\n")
        assert(output != nil)
        return symboltable + header + quantifiers.joined(separator: "\n") + "\noutput(\(output!))\n" + circuit + "\n"
    }
    
    func newId() -> Int {
        defer {
            currentId += 1
        }
        return currentId
    }
    
    public override func visit(proposition: Proposition) -> T {
        return propositions[proposition]!
    }
    public override func visit(unaryOperator: UnaryOperator) -> T {
        return -unaryOperator.operand.accept(visitor: self)
    }
    public override func visit(binaryOperator: BinaryOperator) -> T {
        let subformulas: [Int] = binaryOperator.operands.map({ $0.accept(visitor: self) })
        let formulaId = newId()
        
        switch binaryOperator.type {
        case .And:
            let subf = subformulas.map(String.init).joined(separator: ", ")
            circuit.append("\(formulaId) = and(\(subf))")
        case .Or:
            let subf = subformulas.map(String.init).joined(separator: ", ")
            circuit.append("\(formulaId) = or(\(subf))")
        case .Xnor:
            // a <--> b <=> (!a | b) & (a | !b)
            assert(subformulas.count == 2)
            let lhs = subformulas[0]
            let rhs = subformulas[1]
            let lhsOr = newId()
            let rhsOr = newId()
            circuit.append("\(formulaId) = and(\(lhsOr), \(rhsOr))")
            circuit.append("\(lhsOr) = or(\(-lhs), \(rhs))")
            circuit.append("\(rhsOr) = or(\(lhs), \(-rhs))")
        case .Implication:
            assert(subformulas.count == 2)
            let lhs = subformulas[0]
            let rhs = subformulas[1]
            circuit.append("\(formulaId) = or(\(-lhs), \(rhs))")
        }
        return formulaId
    }
    public override func visit(quantifier: Quantifier) -> T {
        quantifier.variables.forEach({ variable in propositions[variable] = newId() })
        let variables = quantifier.variables.flatMap({ variable in propositions[variable] })
        quantifiers.append((quantifier.type == .Exists ? "exists(" : "forall(") + variables.map(String.init).joined(separator: ", ") + ")")
        let result = quantifier.scope.accept(visitor: self)
        if result != 0 {
            assert(output == nil)
            // top level scope
            if propositions.values.contains(result) {
                // special case if output is a proposition, add a dummy gate instead
                let formulaId = newId()
                circuit.append("\(formulaId) = and(\(result))")
                output = formulaId
            } else {
                output = result
            }
        }
        return 0
    }
    
    public func translate(certificate: UnsafeMutablePointer<aiger>) -> [Proposition:Boolean] {
        var translated: [Proposition:Boolean] = [:]
        var reversed: [Int:Proposition] = [:]
        for (proposition, literal) in propositions {
            reversed[literal] = proposition
        }
        
        for (proposition, literal) in propositions {
            guard let outputSymbol = aiger_contains_output(aig: certificate, withName: String(literal)) else {
                continue
            }
            translated[proposition] = buildFunctionRecursively(aig: certificate, mapping: reversed, literal: outputSymbol.pointee.lit)
        }
        
        return translated
    }
    
    func buildFunctionRecursively(aig: UnsafeMutablePointer<aiger>, mapping: [Int:Proposition], literal: UInt32) -> Boolean {
        switch (aiger_lit2tag(aig, literal)) {
        case 0:
            // constant
            assert(literal <= 1)
            return literal == 1 ? Literal.True : Literal.False
        case 1:
            // input
            let (negated, normalized) = aiger_normalize(literal)
            let symbol = aiger_is_input(aig, normalized)!
            let translatedLit = Int(String(cString: symbol.pointee.name))!
            let proposition = mapping[translatedLit]!
            return negated ? !proposition : proposition
        case 3:
            // and
            let (negated, normalized) = aiger_normalize(literal)
            let and = aiger_is_and(aig, normalized)!
            let lhs = buildFunctionRecursively(aig: aig, mapping: mapping, literal: and.pointee.rhs0)
            let rhs = buildFunctionRecursively(aig: aig, mapping: mapping, literal: and.pointee.rhs1)
            let result = lhs & rhs
            return negated ? !result : result
        default:
            assert(false)
        }
        return Literal.True
    }
}

/**
 * Transforms Boolean functions to aiger circuit
 */
public class AigerVisitor: ReturnConstantVisitor<UInt32> {
    
    var propositions: [Proposition:UInt32] = [:]
    let aig = aiger_init()!
    let inputs: [Proposition]
    let latches: [Proposition]
    
    public init(inputs: [Proposition], latches: [Proposition]) {
        self.inputs = inputs
        for proposition in inputs {
            let literal = aiger_next_lit(aig)
            self.propositions[proposition] = literal
            aiger_add_input(aig, literal, proposition.name)
        }
        self.latches = latches
        for latch in latches {
            let literal = aiger_next_lit(aig)
            self.propositions[latch] = literal
            aiger_add_latch(aig, literal, 0, latch.name)
        }
        super.init(constant: 0)
    }
    
    public override func visit(literal: Literal) -> T {
        return literal == Literal.False ? 0 : 1
    }
    public override func visit(proposition: Proposition) -> T {
        assert(propositions[proposition] != nil)
        return propositions[proposition]!
    }
    public override func visit(unaryOperator: UnaryOperator) -> T {
        return aiger_not(unaryOperator.operand.accept(visitor: self))
    }
    public override func visit(binaryOperator: BinaryOperator) -> T {
        assert(binaryOperator.type == .And || binaryOperator.type == .Or)
        let operands: [UInt32] = binaryOperator.operands.map({ $0.accept(visitor: self) })
        let formula = binaryOperator.type == .And ? encodeAnd(operands) : encodeOr(operands)
        return formula
    }
    
    func encodeAnd(_ operands: [UInt32]) -> UInt32 {
        var operands = operands
        if operands.count == 0 {
            return 1
        } else if operands.count == 1 {
            return operands[0]
        }
        assert(operands.count >= 2)
        while operands.count > 1 {
            let lhs = operands.removeFirst()
            let rhs = operands.removeFirst()
            let and = aiger_next_lit(aig)
            aiger_add_and(aig, and, lhs, rhs)
            operands.append(and)
        }
        assert(operands.count == 1)
        return operands[0]
    }
    
    func encodeOr(_ operands: [UInt32]) -> UInt32 {
        return aiger_not(encodeAnd(operands.map(aiger_not)))
    }
    
    public func addOutput(literal: UInt32, name: String) {
        aiger_add_output(aig, literal, name)
    }
    
    public func defineLatch(latch: Proposition, next: UInt32) {
        guard let index = latches.index(where: { $0 == latch}) else {
            assert(false)
            return
        }
        let symbolPtr: UnsafeMutablePointer<aiger_symbol> = aig.pointee.latches.advanced(by: index)
        symbolPtr.pointee.next = next
    }
}
