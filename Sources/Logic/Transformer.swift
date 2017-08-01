import Utils
import CAiger
import CAigerHelper
import CUDD

public class RemoveComparableVisitor: TransformingVisitor {
    
    var reverseMapping: [Proposition: [Proposition]] = [:]
    var counterBits: Int
    
    public init(bound: Int) {
        precondition(bound >= 1)
        counterBits = numBitsNeeded(bound)
    }
    
    public override func visit(quantifier: Quantifier) -> T {
        var copy = quantifier
        copy.scope = quantifier.scope.accept(visitor: self)
        copy.variables = copy.variables.reduce([], {
            variables, variable in variables + (reverseMapping[variable] ?? [variable])
        })
        return copy
    }
    public override func visit(comparator: BooleanComparator) -> T {
        func translateToBitRepresentation(_ atom: Logic, bit: Int) -> Logic {
            if let atom = atom as? Proposition {
                return Proposition("\(atom)_\(bit)")
            }
            if let atom = atom as? FunctionApplication {
                return FunctionApplication(function: Proposition("\(atom.function)_\(bit)"), application: atom.application)
            }
            assert(false)
            return Literal.False
        }
        func getProposition(_ atom: Logic) -> Proposition {
            if let proposition = atom as? Proposition {
                return proposition
            }
            if let application = atom as? FunctionApplication {
                return application.function
            }
            assert(false)
            return Proposition("error")
        }
        
        let lhsProp = getProposition(comparator.lhs)
        if reverseMapping[lhsProp] == nil {
            reverseMapping[lhsProp] = (0..<counterBits).map({ i in Proposition("\(lhsProp)_\(i)")})
        }
        
        let rhsProp = getProposition(comparator.rhs)
        if reverseMapping[rhsProp] == nil {
            reverseMapping[rhsProp] = (0..<counterBits).map({ i in Proposition("\(rhsProp)_\(i)")})
        }
        
        let lhs = (0..<counterBits).map({ bit in translateToBitRepresentation(comparator.lhs, bit: bit) })
        let rhs = (0..<counterBits).map({ bit in translateToBitRepresentation(comparator.rhs, bit: bit) })
        return order(binaryLhs: lhs, binaryRhs: rhs, strict: comparator.type == .Less)
    }
}

public class NegationNormalFormVisitor: TransformingVisitor {
    
    var result: Logic = Literal.False
    var negate: Bool = false
    
    public init(formula: Logic) {
        super.init()
        result = formula.accept(visitor: self)
    }
    
    public override func visit(literal: Literal) -> Logic {
        defer {
            negate = false
        }
        return negate ? !literal : literal
    }
    
    public override func visit(proposition: Proposition) -> Logic {
        defer {
            negate = false
        }
        return negate ? !proposition : proposition
    }
    
    public override func visit(unaryOperator: UnaryOperator) -> Logic {
        assert(unaryOperator.type == .Negation)
        assert(negate == false)
        negate = true
        return unaryOperator.operand.accept(visitor: self)
    }
    
    public override func visit(binaryOperator: BinaryOperator) -> Logic {
        var copy = binaryOperator
        if negate {
            negate = false
            copy = BinaryOperator(binaryOperator.type.negated, operands: binaryOperator.operands.map(!))
        }
        copy.operands = copy.operands.map({ $0.accept(visitor: self) })
        
        // The & and | operators triggers simplifications that are not available elsewhere
        switch copy.type {
        case .And:
            return copy.operands.reduce(Literal.True, &)
        case .Or:
            return copy.operands.reduce(Literal.False, |)
        default:
            return copy
        }
    }
    
    public override func visit(application: FunctionApplication) -> T {
        defer {
            negate = false
        }
        return negate ? !application : application
    }
}

public class DIMACSVisitor: ReturnConstantVisitor<Int>, CustomStringConvertible {
    
    var propositions: [Proposition:Int] = [:]
    var currentId = 1
    var dimacs: [String] = []
    var output: Int? = nil
    var tseitinVariables: [Int] = []
    
    public init(formula: Logic) {
        super.init(constant: 0)
        let _ = formula.accept(visitor: self)
        // let nnf = NegationNormalFormVisitor(formula: qbf).result
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
        tseitinVariables.append(formulaId)
        
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
        case .Xor:
            assert(subformulas.count == 2)
            let lhs = subformulas[0]
            let rhs = subformulas[1]
            dimacs.append("-\(formulaId) \(-lhs) \(-rhs)")
            dimacs.append("-\(formulaId) \(lhs) \(rhs)")
            dimacs.append("\(formulaId) \(-lhs) \(rhs)")
            dimacs.append("\(formulaId) \(lhs) \(-rhs)")
        }
        return formulaId
    }
    public override func visit(quantifier: Quantifier) -> T {
        quantifier.variables.forEach({ variable in propositions[variable] = newId() })
        let result = quantifier.scope.accept(visitor: self)
        /*assert(result != 0)  // there is only one existential quantifier
        assert(output == nil)*/
        // top level scope
        if output == nil {
            output = result
        }
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
    
    public override var description: String {
        let symboltable = propositions.map({
            (proposition, literal) in
            "c \(proposition) \(literal)\n"
        }).joined(separator: "")
        let header = "p cnf \(currentId) \(self.dimacs.count + 1)\n"
        let dimacs = self.dimacs.map({ $0 + " 0\n" }).joined(separator: "")
        var quants = quantifiers
        quants.append("e " + tseitinVariables.map(String.init).joined(separator: " ") + " 0")
        assert(output != nil)
        return symboltable + header + quants.joined(separator: "\n") + "\n" + dimacs + "\(output!) 0\n"
    }

    public override func visit(quantifier: Quantifier) -> T {
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
    
    public func translate(certificate: UnsafeMutablePointer<aiger>) -> [Proposition:Logic] {
        var translated: [Proposition:Logic] = [:]
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
}

public class DQDIMACSVisitor: QDIMACSVisitor {
    public typealias T = Int
    
    var contexts: [FunctionApplication:Int] = [:]
    var functionConstraints: Int? = nil
    
    public override var description: String {
        let symboltable = propositions.map({
            (proposition, literal) in
            "c \(proposition) \(literal)\n"
        }).joined(separator: "")
        let header = "p cnf \(currentId) \(self.dimacs.count + 2)\n"
        let dimacs = self.dimacs.map({ $0 + " 0\n" }).joined(separator: "")
        var quants = quantifiers
        quants.append("e " + tseitinVariables.map(String.init).joined(separator: " ") + " 0")
        assert(output != nil)
        assert(functionConstraints != nil)
        return symboltable + header + quants.joined(separator: "\n") + "\n" + dimacs + "\(output!) 0\n\(functionConstraints!) 0\n"
    }
    
    public override func visit(application: FunctionApplication) -> T {
        if let variable = contexts[application] {
            return variable
        } else {
            let variable = newId()
            contexts[application] = variable
            return variable
        }
    }
    
    public override func visit(quantifier: Quantifier) -> T {
        if quantifier.type == .Forall {
            quantifier.variables.forEach({ variable in propositions[variable] = newId() })
            let variables = quantifier.variables.flatMap({ variable in propositions[variable] })
            quantifiers.append("a " + variables.map(String.init).joined(separator: " ") + " 0")
        }
        let result = quantifier.scope.accept(visitor: self)
        if result != 0 {
            assert(output == nil)
            // top level scope
            output = result
            
            // TODO: have to build an additional constraint that maps different application to the same function
            
            var functionConstraints: [Logic] = []
            var contexts = self.contexts.map({ key, val in key })
            for i in 0..<contexts.count {
                for j in i+1..<contexts.count {
                    let context1 = contexts[i]
                    let context2 = contexts[j]
                    if context1.function != context2.function {
                        continue
                    }
                    assert(context1 != context2)
                    var precondition: [Logic] = []
                    for (var1, var2) in zip(context1.application, context2.application) {
                        precondition.append(var1 <-> var2)
                    }
                    functionConstraints.append(
                        precondition.reduce(Literal.True, &) --> (context1 <-> context2)
                    )
                }
            }
            let constraints = functionConstraints.reduce(Literal.True, &)
            self.functionConstraints = constraints.accept(visitor: self)
        }
        if quantifier.type == .Exists {
            for (application, function) in contexts {
                if !quantifier.variables.contains(application.function) {
                    continue
                }
                let parameter: [Proposition] = application.application as! [Proposition]
                let dependencies = parameter.flatMap({ variable in propositions[variable] })
                quantifiers.append("d \(function) " + dependencies.map(String.init).joined(separator: " ") + " 0")
            }
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
    
    public init(formula: Logic) {
        super.init(constant: 0)
        let _ = formula.accept(visitor: self)
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
        case .Xor:
            // a ^ b <=> (!a | !b) & (a | b)
            assert(subformulas.count == 2)
            let lhs = subformulas[0]
            let rhs = subformulas[1]
            let lhsOr = newId()
            let rhsOr = newId()
            circuit.append("\(formulaId) = and(\(lhsOr), \(rhsOr))")
            circuit.append("\(lhsOr) = or(\(-lhs), \(-rhs))")
            circuit.append("\(rhsOr) = or(\(lhs), \(rhs))")
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
    
    public func translate(certificate: UnsafeMutablePointer<aiger>) -> [Proposition:Logic] {
        var translated: [Proposition:Logic] = [:]
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
}

private func buildFunctionRecursively(aig: UnsafeMutablePointer<aiger>, mapping: [Int:Proposition], literal: UInt32) -> Logic {
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

/**
 * Transforms Boolean functions to aiger circuit
 */
public class AigerVisitor: ReturnConstantVisitor<UInt32> {
    
    var propositions: [Proposition:UInt32] = [:]
    public let aig = aiger_init()!
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

public class TPTP3Visitor: TransformingVisitor, CustomStringConvertible {
    
    var cnf: [String] = [
        // Define Boolean predicate
        "cnf(rule_true,axiom, p(1)).",
        "cnf(rule_false,axiom, ~p(0))."
    ]
    var universalVariables: [Proposition]? = nil
    var numClauses: Int = 0
    var auxVar: Int = 0
    
    let clausePrinter = TPTP3Printer()
    
    public var description: String {
        return cnf.joined(separator: "\n")
    }
    
    public init(formula: Logic) {
        super.init()
        //let nnf = NegationNormalFormVisitor(formula: formula).result
        let _ = formula.accept(visitor: self)
    }
    
    func nextClauseId() -> Int {
        defer {
            numClauses += 1
        }
        return numClauses
    }
    func nextAuxId() -> Int {
        defer {
            auxVar += 1
        }
        return auxVar
    }
    func auxVarFrom(id: Int) -> FunctionApplication {
        return FunctionApplication(function: Proposition("aux\(id)"), application: universalVariables!)
    }
    func addClause(_ clause: Logic) {
        let clauseId = nextClauseId()
        cnf.append("cnf(clause\(clauseId),plain,\(clause.accept(visitor: clausePrinter))).")
    }
    func addClause(_ clause: [Logic]) {
        assert(clause.count > 0)
        addClause(clause.reduce(Literal.False, |))
    }
    
    public override func visit(binaryOperator: BinaryOperator) -> Logic {
        let subformulas: [Logic] = binaryOperator.operands.map({ $0.accept(visitor: self) })
        let auxId = nextAuxId()
        let auxVar = auxVarFrom(id: auxId)
        
        switch binaryOperator.type {
        case .And:
            subformulas.forEach({ subformula in addClause([!auxVar, subformula]) })
            addClause([auxVar] + subformulas.map({ subformula in !subformula }))
        case .Or:
            subformulas.forEach({ subformula in addClause([auxVar, !subformula]) })
            addClause([!auxVar] + subformulas)
        case .Xnor:
            assert(subformulas.count == 2)
            let lhs = subformulas[0]
            let rhs = subformulas[1]
            addClause([!auxVar, lhs, !rhs])
            addClause([!auxVar, !lhs, rhs])
            addClause([auxVar, lhs, rhs])
            addClause([auxVar, !lhs, !rhs])
        case .Xor:
            assert(subformulas.count == 2)
            let lhs = subformulas[0]
            let rhs = subformulas[1]
            addClause([!auxVar, !lhs, !rhs])
            addClause([!auxVar, lhs, rhs])
            addClause([auxVar, !lhs, rhs])
            addClause([auxVar, lhs, !rhs])
        }
        return auxVar
    }
    public override func visit(quantifier: Quantifier) -> Logic {
        if quantifier.type == .Forall {
            assert(universalVariables == nil)
            universalVariables = quantifier.variables
        }
        let result = quantifier.scope.accept(visitor: self)
        if !(result is Quantifier) {
            addClause(result)
        }
        return quantifier
    }
}

public class CUDDVisitor: ReturnConstantVisitor<CUDDNode> {
    
    let manager: CUDDManager
    
    // lookup propositions
    let lookupTable: [String:CUDDNode]
    
    public init(manager: CUDDManager, lookupTable: [String:CUDDNode]) {
        self.manager = manager
        self.lookupTable = lookupTable
        super.init(constant: manager.zero())
    }
    
    public override func visit(literal: Literal) -> CUDDNode {
        if literal == .False {
            return manager.zero()
        } else {
            return manager.one()
        }
    }
    
    public override func visit(proposition: Proposition) -> CUDDNode {
        guard let node = lookupTable[proposition.name] else {
            fatalError()
        }
        return node
    }
    
    public override func visit(unaryOperator: UnaryOperator) -> CUDDNode {
        assert(unaryOperator.type == .Negation)
        return !unaryOperator.operand.accept(visitor: self)
    }
    
    public override func visit(binaryOperator: BinaryOperator) -> CUDDNode {
        let application = binaryOperator.operands.map({ $0.accept(visitor: self) })
        switch binaryOperator.type {
        case .And:
            return application.reduce(manager.one(), &)
        case .Or:
            return application.reduce(manager.zero(), |)
        case .Xnor:
            return application[0] <-> application[1]
        case .Xor:
            return application[0] ^ application[1]
        }
    }
}
