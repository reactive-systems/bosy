
import XCTest

import Basic
//import Utility

import Specification
import LTL
import Utils
import TransitionSystem
import Automata

import CAiger

@testable import BoundedSynthesis


/**
 * The instance was solved incorrectly because the intermediate LTL printing had a bug.
 * Tests that the instance is realizable and model checks solution.
 *
 * Reported by Felix Klein.
 */
class WrongLTLPrintTest: XCTestCase {

    let jsonSpec = "{\"semantics\": \"mealy\", \"inputs\": [\"i\"], \"outputs\": [\"op2\", \"op1\", \"oc2\", \"oc1\"], \"assumptions\": [], \"guarantees\": [\"(((oc1) && (! (oc2))) <-> ((! (oc2)) || (oc1)))\", \"(((op1) && (! (op2))) <-> ((! (op2)) || (op1)))\", \"(G ((i) <-> (oc2)))\", \"(G (op2))\"] }"

    var options = BoSyOptions()

    func testSynthesisInputSymbolic() throws {
        options.solver = .rareqs
        options.qbfPreprocessor = .bloqqer
        options.qbfCertifier = .quabs
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            return
        }
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
        let encoding = InputSymbolicEncoding(options: options, automaton: automaton, specification: specification, synthesize: true)
        XCTAssertTrue(try encoding.solve(forBound: 1))
        guard let transitionSystem = encoding.extractSolution() else {
            XCTFail()
            return
        }

        // Check SMV implementation
        guard let smvRepresentation = (transitionSystem as? SmvRepresentable)?.smv else {
            XCTFail()
            return
        }
        let tempFile = try TemporaryFile(suffix: ".smv")
        tempFile.fileHandle.write(Data(smvRepresentation.utf8))
        XCTAssertTrue(modelCheckSMV(file: tempFile.path.pathString))

        // Check AIGER implementation
        guard let aigerRepresentation = (transitionSystem as? AigerRepresentable)?.aiger else {
            XCTFail()
            return
        }
        XCTAssertTrue(try modelCheckAiger(specification: specification, implementation: aigerRepresentation))
    }

    static var allTests : [(String, (WrongLTLPrintTest) -> () throws -> Void)] {
        return [
            ("testSynthesisInputSymbolic", testSynthesisInputSymbolic),
        ]
    }
}

