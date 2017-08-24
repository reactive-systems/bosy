import XCTest

@testable import Automata
import Logic

class AutomatonTest: XCTestCase {

    func testSafetyReduction() {
        let a = Proposition("a")
        let b = Proposition("b")
        let transitions = ["init" : ["init" : a, "reject": !a], "reject": ["reject": Literal.True]]
        let safetyConditions: [String : Logic] = ["init" : b]
        let coBüchi = CoBüchiAutomaton(initialStates: ["init"], states: ["init", "reject"], transitions: transitions, safetyConditions: safetyConditions, rejectingStates: ["reject"])

        let safety0 = coBüchi.reduceToSafety(bound: 0)
        XCTAssertEqual(safety0.states.count, 1)
        XCTAssertEqual(safety0.safetyConditions.count, 1)

        let safety1 = coBüchi.reduceToSafety(bound: 1)
        XCTAssertEqual(safety1.states.count, 2)
        XCTAssertEqual(safety1.safetyConditions.count, 2)
    }


    static var allTests : [(String, (AutomatonTest) -> () throws -> Void)] {
        return [
            ("testSafetyReduction", testSafetyReduction),

        ]
    }
}
