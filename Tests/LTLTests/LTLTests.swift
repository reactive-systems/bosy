import XCTest
@testable import LTL

class LTLTests: XCTestCase {

    let a = LTLAtomicProposition(name: "a")
    let b = LTLAtomicProposition(name: "b")

    func testSimple() throws {
        let ltlString = "GFa"
        let parsed = try LTL.parse(fromString: ltlString)

        let expected = LTL.application(.globally, parameters: [.application(.finally, parameters: [.atomicProposition(a)])])
        XCTAssertEqual(parsed, expected)
    }
    
    func testSimpleParenthesis() throws {
        let parsed = try LTL.parse(fromString: "(a)")
        let expected = LTL.atomicProposition(a)
        XCTAssertEqual(parsed, expected)
    }
    
    func testBinaryOperator() throws {
        let parsed = try LTL.parse(fromString: "(a && b)")
        let expected = LTL.application(.and, parameters: [.atomicProposition(a), .atomicProposition(b)])
        XCTAssertEqual(parsed, expected)
        
        let alternative1 = try LTL.parse(fromString: "(a & b)")
        XCTAssertEqual(parsed, alternative1)
        let alternative2 = try LTL.parse(fromString: "(a /\\ b)")
        XCTAssertEqual(parsed, alternative2)
        
        XCTAssertThrowsError(try LTL.parse(fromString: "(a &&& b)"))
    }
    
    func testMissingParenthesis() throws {
        XCTAssertThrowsError(try LTL.parse(fromString: "(a"))
    }
    
    func testPropositionsWithUnderscore() throws {
        let parsed = try LTL.parse(fromString: "(a_1)")
        let expected = LTL.atomicProposition(LTLAtomicProposition(name: "a_1"))
        XCTAssertEqual(parsed, expected)
    }

    func testQuantified() throws {
        let parsed = try LTL.parse(fromString: "exists pi1 pi2. a[pi1] && a[pi2]")
        let a = LTLAtomicProposition(name: "a")
        let pi1 = LTLPathVariable(name: "pi1")
        let pi2 = LTLPathVariable(name: "pi2")
        let expected = LTL.pathQuantifier(.exists,
                                          parameters: [pi1, pi2],
                                          body: .application(.and, parameters: [
                                            .pathProposition(a, pi1),
                                            .pathProposition(a, pi2)
                                          ]))
        XCTAssertEqual(parsed, expected)
    }
    
    func testNNF() {
        let parsed = try! LTL.parse(fromString: "!(a & b)")
        let expected = try! LTL.parse(fromString: "!a | !b")
        XCTAssertEqual(parsed.nnf, expected)
    }

    func testNormalizeEventually() {
        let parsed = try! LTL.parse(fromString: "F a")
        let expected = try! LTL.parse(fromString: "true U a")
        XCTAssertEqual(parsed.normalized, expected)
    }
    
    func testNormalizeGlobally() {
        let parsed = try! LTL.parse(fromString: "G a")
        let expected = try! LTL.parse(fromString: "false R a")
        XCTAssertEqual(parsed.normalized, expected)
    }
    
    func testNormalizeEquality() {
        let parsed = try! LTL.parse(fromString: "a <-> b")
        let expected = try! LTL.parse(fromString: "(a & b) | (!a & !b)")
        XCTAssertEqual(parsed.normalized, expected)
    }
    
    static var allTests : [(String, (LTLTests) -> () throws -> Void)] {
        return [
            ("testSimple", testSimple),
            ("testSimpleParenthesis", testSimpleParenthesis),
            ("testBinaryOperator", testBinaryOperator),
            ("testMissingParenthesis", testMissingParenthesis),
            ("testPropositionsWithUnderscore", testPropositionsWithUnderscore),
            ("testNNF", testNNF),
            ("testNormalizeEventually", testNormalizeEventually),
            ("testNormalizeGlobally", testNormalizeGlobally),
            ("testNormalizeEquality", testNormalizeEquality)
        ]
    }
}
