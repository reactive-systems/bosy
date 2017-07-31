import XCTest

@testable import Logic

class BooleanTest: XCTestCase {
    
    func testXnorTseitin() {
        let x = Proposition("x")
        let y = Proposition("y")
        
        let equiv = BinaryOperator(.Xnor, operands:[x, y])
        let sat_qbf = Quantifier(.Forall, variables: [x], scope: Quantifier(.Exists, variables: [y], scope: equiv))
        let unsat_qbf = Quantifier(.Exists, variables: [x], scope: Quantifier(.Forall, variables: [y], scope: equiv))
        
        guard let sat = RAReQS().solve(formula: sat_qbf, preprocessor: nil) else {
            XCTFail("solver failed on instance")
            return
        }
        guard case .sat(_) = sat else {
            XCTFail("\(sat_qbf) === SAT")
            return
        }
        
        guard let unsat = RAReQS().solve(formula: unsat_qbf, preprocessor: nil) else {
            XCTFail("solver failed on instance")
            return
        }
        guard case .unsat = unsat else {
            XCTFail("\(unsat_qbf) === UNSAT")
            return
        }
    }
    
    func testAndTseitin() {
        let x = Proposition("x")
        let y = Proposition("y")
        
        let and = BinaryOperator(.And, operands:[x, y])
        let sat_qbf = Quantifier(.Exists, variables: [x, y], scope: and)
        let unsat_qbf = Quantifier(.Exists, variables: [x], scope: Quantifier(.Forall, variables: [y], scope: and))
        
        guard let sat = RAReQS().solve(formula: sat_qbf, preprocessor: nil) else {
            XCTFail("solver failed on instance")
            return
        }
        guard case .sat(_) = sat else {
            XCTFail("\(sat_qbf) === SAT")
            return
        }
        
        guard let unsat = RAReQS().solve(formula: unsat_qbf, preprocessor: nil) else {
            XCTFail("solver failed on instance")
            return
        }
        guard case .unsat = unsat else {
            XCTFail("\(unsat_qbf) === UNSAT")
            return
        }
    }
    
    func testOrTseitin() {
        let x = Proposition("x")
        let y = Proposition("y")
        
        let or = BinaryOperator(.Or, operands:[x, y])
        let sat_qbf = Quantifier(.Exists, variables: [x], scope: Quantifier(.Forall, variables: [y], scope: or))
        let unsat_qbf = Quantifier(.Forall, variables: [x, y], scope: or)
        
        guard let sat = RAReQS().solve(formula: sat_qbf, preprocessor: nil) else {
            XCTFail("solver failed on instance")
            return
        }
        guard case .sat(_) = sat else {
            XCTFail("\(sat_qbf) === SAT")
            return
        }
        
        guard let unsat = RAReQS().solve(formula: unsat_qbf, preprocessor: nil) else {
            XCTFail("solver failed on instance")
            return
        }
        guard case .unsat = unsat else {
            XCTFail("\(unsat_qbf) === UNSAT")
            return
        }
    }
    
    
    func testImplicationTseitin() {
        let x = Proposition("x")
        let y = Proposition("y")
        
        let implication = BinaryOperator(.Or, operands: [!x, y])
        let sat_qbf = Quantifier(.Exists, variables: [x], scope: Quantifier(.Forall, variables: [y], scope: implication))
        let unsat_qbf = Quantifier(.Forall, variables: [x, y], scope: implication)
        
        guard let sat = RAReQS().solve(formula: sat_qbf, preprocessor: nil) else {
            XCTFail("solver failed on instance")
            return
        }
        guard case .sat(_) = sat else {
            XCTFail("\(sat_qbf) === SAT")
            return
        }
        
        guard let unsat = RAReQS().solve(formula: unsat_qbf, preprocessor: nil) else {
            XCTFail("solver failed on instance")
            return
        }
        guard case .unsat = unsat else {
            XCTFail("\(unsat_qbf) === UNSAT")
            return
        }
    }
    
    static var allTests : [(String, (BooleanTest) -> () throws -> Void)] {
        return [
            ("testXnorTseitin", testXnorTseitin),
            ("testAndTseitin", testAndTseitin),
            ("testOrTseitin", testOrTseitin),
            ("testImplicationTseitin", testImplicationTseitin),
        ]
    }
}
