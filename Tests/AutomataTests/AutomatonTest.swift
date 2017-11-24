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
    
    func testCoBüchiDot() {
        let expected = [
            "digraph graphname {",
            "\t_init [style=\"invis\"];",
            "\t_init -> \"sq_0\"[label=\"\"];",
            "\t\"sq_0\"[shape=rectangle,label=\"q_0\"];",
            "\t\"sq_1\"[shape=rectangle,label=\"q_1\"];",
            "\t\"sq_0\"[shape=rectangle,label=\"rejecting:q_0\"];",
            "\t\"sq_0\" -> \"sq_0\" [label=\"a\"];",
            "\t\"sq_0\" -> \"sq_1\" [label=\"b\"];",
            "\t\"sq_1\" -> \"sq_0\" [label=\"a\"];",
            "\t\"sq_1\" -> \"sq_1\" [label=\"b\"];",
            "\tbad[shape=rectangle,label=\"bad\"];",
            "\t\"sq_0\" -> bad [label=\"¬b\"];",
            "}"
        ].joined(separator: "\n")
        let actual = CoBüchiAutomaton(
                         initialStates: ["q_0"],
                         states: ["q_0", "q_1"],
                         transitions: ["q_0": ["q_0" : Proposition("a"), "q_1" : Proposition("b")],
                                       "q_1": ["q_0" : Proposition("a"), "q_1" : Proposition("b")]],
                         safetyConditions: ["q_0" : Proposition("b")],
                         rejectingStates: ["q_0"])
        
        XCTAssertEqual(expected, actual.dot)
    }

    func testSafetyDot() {
        let expected = [
            "digraph graphname {",
            "\t_init [style=\"invis\"];",
            "\t_init -> \"sq_0\"[label=\"\"];",
            "\t\"sq_0\"[shape=rectangle,label=\"q_0\"];",
            "\t\"sq_1\"[shape=rectangle,label=\"q_1\"];",
            "\t\"sq_0\" -> \"sq_0\" [label=\"a\"];",
            "\t\"sq_0\" -> \"sq_1\" [label=\"b\"];",
            "\t\"sq_1\" -> \"sq_0\" [label=\"a\"];",
            "\t\"sq_1\" -> \"sq_1\" [label=\"b\"];",
            "\tbad[shape=rectangle,label=\"bad\"];",
            "\t\"sq_0\" -> bad [label=\"¬b\"];",
            "}"
            ].joined(separator: "\n")
        let actual = SafetyAutomaton(
            initialStates: ["q_0"],
            states: ["q_0", "q_1"],
            transitions: ["q_0": ["q_0" : Proposition("a"), "q_1" : Proposition("b")],
                          "q_1": ["q_0" : Proposition("a"), "q_1" : Proposition("b")]],
            safetyConditions: ["q_0" : Proposition("b")]
        )
        
        XCTAssertEqual(expected, actual.dot)
    }

    static var allTests : [(String, (AutomatonTest) -> () throws -> Void)] {
        return [
            ("testSafetyReduction", testSafetyReduction),

        ]
    }
}
