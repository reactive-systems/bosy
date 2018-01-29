import XCTest
@testable import LTL

class HyperLTLTests: XCTestCase {

    let pi1 = LTLPathVariable(name: "pi1")
    let pi2 = LTLPathVariable(name: "pi2")

    func testHyperLTLDetectionTrue() throws {
        let ltlString = "forall pi1 pi2. a[pi1] && b[pi2]"
        let parsed = try LTL.parse(fromString: ltlString)

        XCTAssertTrue(parsed.isHyperLTL)

        XCTAssert(parsed.pathVariables.contains(pi1))
        XCTAssert(parsed.pathVariables.contains(pi2))
        XCTAssertEqual(parsed.pathVariables.count, 2)
    }

    func testHyperLTLDetectionTrueAlternation() throws {
        let ltlString = "forall pi1. exists pi2. a[pi1] && b[pi2]"
        let parsed = try LTL.parse(fromString: ltlString)

        XCTAssertTrue(parsed.isHyperLTL)
    }

    func testHyperLTLDetectionFalseLTL() throws {
        let ltlString = "a && b"
        let parsed = try LTL.parse(fromString: ltlString)

        XCTAssertFalse(parsed.isHyperLTL)
    }

    func testHyperLTLDetectionFalseHyperCTL() throws {
        let ltlString = "forall pi1. G (exists pi2. (b[pi1] || a [pi2]))"
        let parsed = try LTL.parse(fromString: ltlString)

        XCTAssertFalse(parsed.isHyperLTL)
    }

    func testHyperLTLBody() throws {
        let ltlString = "forall pi1. exists pi2. a[pi1] && b[pi2]"
        let parsed = try LTL.parse(fromString: ltlString)

        let a = LTLAtomicProposition(name: "a")
        let b = LTLAtomicProposition(name: "b")

        let api1: LTL = .pathProposition(a, pi1)
        let bpi2: LTL = .pathProposition(b, pi2)
        let body = api1 && bpi2


        XCTAssertEqual(parsed.ltlBody, body)
    }

    func testPrenex() throws {
        let ltlString = "(forall pi1. forall pi2. a[pi1]) && (forall pi2. b[pi2])"
        let parsed = try LTL.parse(fromString: ltlString)
        let prenex = parsed.prenex
        XCTAssert(prenex.pathVariables.contains(pi1))
        XCTAssert(prenex.pathVariables.contains(pi2))
        XCTAssertEqual(prenex.pathVariables.count, 2)
    }
}

