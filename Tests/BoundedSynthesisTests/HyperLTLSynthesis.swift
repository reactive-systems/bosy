
import XCTest

import Automata
import LTL
import Specification
import TransitionSystem
import TSCBasic
import Utils

import CAiger

@testable import BoundedSynthesis

/**
 * Test of HyperLTL synthesis backend.
 * The specification is partitioned into `high` and `low` inputs/outputs with the
 * non-interference requirement (`high` input does not influence `low` output):
 *
 *     forall pi1 pi2.( (o_l[pi1] <-> o_l[pi2]) W !(i_l[pi1] <-> i_l[pi2]) )
 *
 * Further, we have two disjunctive requirements:
 *
 *     (o_l[pi1] <-> i_h[pi1]) || (X o_l[pi1] <-> i_l[pi1])
 *
 * The first one can be satisfied with a system of size 1, but that violates
 * the non-interference condition. Thus, a solution has to satisfy the second
 * constraint that can be only satisfied with a system if size 2.
 */
class HyperLTLSynthesisTest: XCTestCase {
    let jsonSpec = "{\"semantics\": \"mealy\", \"inputs\": [\"i_l\", \"i_h\"], \"outputs\": [\"o_l\"], \"assumptions\": [], \"guarantees\": [\"G (o_l || !o_l)\"], \"hyper\": [\"forall pi1 pi2. ( (o_l[pi1] <-> i_h[pi1]) || (X o_l[pi1] <-> i_l[pi1]) ) && ( (o_l[pi1] <-> o_l[pi2]) W !(i_l[pi1] <-> i_l[pi2]) )\"] }"

    var options = BoSyOptions()

    // Realizability

    func testRealizabilitySmt() {
        options.solver = .z3
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            return
        }
        XCTAssertEqual(specification.assumptions.count, 0)
        XCTAssertEqual(specification.guarantees.count, 1)
        XCTAssertEqual(specification.hyper!.count, 1)
        let linear = specification.ltl
        let hyperltl = specification.hyperPrenex

        guard let linearAutomaton = try? CoBüchiAutomaton.from(ltl: !linear, using: .spot("")) else {
            XCTFail("could not create linear automaton")
            return
        }

        guard let automaton = try? CoBüchiAutomaton.from(ltl: !hyperltl.ltlBody, using: .spot("")) else {
            XCTFail()
            return
        }

        let encoding = HyperSmtEncoding(options: options, linearAutomaton: linearAutomaton, hyperAutomaton: automaton, specification: specification)
        XCTAssertFalse(try encoding.solve(forBound: 1))
        XCTAssertTrue(try encoding.solve(forBound: 2))
        XCTAssertTrue(try encoding.solve(forBound: 3))
    }

    static var allTests: [(String, (HyperLTLSynthesisTest) -> () throws -> Void)] {
        [
            ("testRealizabilitySmt", testRealizabilitySmt),
        ]
    }
}
