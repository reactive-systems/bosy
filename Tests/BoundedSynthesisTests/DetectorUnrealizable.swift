
import XCTest

import Basic
import Utility

import Specification
import LTL
import Utils
import TransitionSystem

import CAiger

@testable import BoundedSynthesis

/**
 * Tests whether the synthesis result of the specification
 *
 *     GF (r_0 && r_1) <-> GF g
 *     G (r_0 && r_1) -> G (!g)
 *
 * is unrealizable in all supported backends.
 */
class DetectorUnrealizableTest: XCTestCase {

    let jsonSpec = "{\"semantics\": \"mealy\", \"inputs\": [\"r_0\", \"r_1\"], \"outputs\": [\"g\"], \"assumptions\": [], \"guarantees\": [\"((G ((F (r_0)) && (F (r_1)))) <-> (G (F (g))))\", \"(G (((r_0) && (r_1)) -> (G (! (g)))))\"] }"

    var options = BoSyOptions()

    // Realizability
    func testRealizabilityInputSymbolic() {
        options.solver = .rareqs
        options.qbfPreprocessor = .bloqqer
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec)?.dualized else {
            XCTFail()
            return
        }
        guard let ltlSpec = (!specification.ltl).ltl3ba else {
            XCTFail()
            return
        }
        guard let automaton = options.converter.convert(ltl: ltlSpec) else {
            XCTFail()
            return
        }
        var encoding = InputSymbolicEncoding(options: options, automaton: automaton, specification: specification, synthesize: false)
        XCTAssertTrue(try encoding.solve(forBound: 1))
    }

    func testRealizabilityExplicit() {
        options.solver = .picosat
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec)?.dualized else {
            XCTFail()
            return
        }
        guard let ltlSpec = (!specification.ltl).ltl3ba else {
            XCTFail()
            return
        }
        guard let automaton = options.converter.convert(ltl: ltlSpec) else {
            XCTFail()
            return
        }
        var encoding = ExplicitEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 1))
    }

    func testRealizabilitySmt() {
        options.solver = .z3
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec)?.dualized else {
            XCTFail()
            return
        }
        guard let ltlSpec = (!specification.ltl).ltl3ba else {
            XCTFail()
            return
        }
        guard let automaton = options.converter.convert(ltl: ltlSpec) else {
            XCTFail()
            return
        }
        var encoding = SmtEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 1))
    }

    func testRealizabilityGameSolver() {
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec)?.dualized else {
            XCTFail()
            return
        }
        guard let ltlSpec = (!specification.ltl).ltl3ba else {
            XCTFail()
            return
        }
        guard let automaton = options.converter.convert(ltl: ltlSpec) else {
            XCTFail()
            return
        }
        let encoding = SafetyGameReduction(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 1))
    }

    func testSynthesisInputSymbolic() throws {
        options.solver = .rareqs
        options.qbfPreprocessor = .bloqqer
        options.qbfCertifier = .quabs
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec)?.dualized else {
            XCTFail()
            return
        }
        guard let ltlSpec = (!specification.ltl).ltl3ba else {
            XCTFail()
            return
        }
        guard let automaton = options.converter.convert(ltl: ltlSpec) else {
            XCTFail()
            return
        }
        var encoding = InputSymbolicEncoding(options: options, automaton: automaton, specification: specification, synthesize: true)
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
        XCTAssertTrue(modelCheckSMV(file: tempFile.path.asString))

        // Check AIGER implementation
        guard let aigerRepresentation = (transitionSystem as? AigerRepresentable)?.aiger else {
            XCTFail()
            return
        }
        XCTAssertTrue(try modelCheckAiger(specification: specification, implementation: aigerRepresentation))
    }

    func testSynthesisExplicit() throws {
        options.solver = .picosat
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec)?.dualized else {
            XCTFail()
            return
        }
        guard let ltlSpec = (!specification.ltl).ltl3ba else {
            XCTFail()
            return
        }
        guard let automaton = options.converter.convert(ltl: ltlSpec) else {
            XCTFail()
            return
        }
        var encoding = ExplicitEncoding(options: options, automaton: automaton, specification: specification)
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
        XCTAssertTrue(modelCheckSMV(file: tempFile.path.asString))

        // Check AIGER implementation
        guard let aigerRepresentation = (transitionSystem as? AigerRepresentable)?.aiger else {
            XCTFail()
            return
        }
        XCTAssertTrue(try modelCheckAiger(specification: specification, implementation: aigerRepresentation))
    }

    func testSynthesisSmt() throws {
        options.solver = .z3
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec)?.dualized else {
            XCTFail()
            return
        }
        guard let ltlSpec = (!specification.ltl).ltl3ba else {
            XCTFail()
            return
        }
        guard let automaton = options.converter.convert(ltl: ltlSpec) else {
            XCTFail()
            return
        }
        var encoding = SmtEncoding(options: options, automaton: automaton, specification: specification)
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
        XCTAssertTrue(modelCheckSMV(file: tempFile.path.asString))

        // Check AIGER implementation
        guard let aigerRepresentation = (transitionSystem as? AigerRepresentable)?.aiger else {
            XCTFail()
            return
        }
        XCTAssertTrue(try modelCheckAiger(specification: specification, implementation: aigerRepresentation))
    }

    func testSynthesisGameSolver() {
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec)?.dualized else {
            XCTFail()
            return
        }
        guard let ltlSpec = (!specification.ltl).ltl3ba else {
            XCTFail()
            return
        }
        guard let automaton = options.converter.convert(ltl: ltlSpec) else {
            XCTFail()
            return
        }
        let encoding = SafetyGameReduction(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 1))
        guard let transitionSystem = encoding.extractSolution() else {
            XCTFail()
            return
        }
        // Check AIGER implementation
        guard let aigerRepresentation = (transitionSystem as? AigerRepresentable)?.aiger else {
            XCTFail()
            return
        }
        XCTAssertTrue(try modelCheckAiger(specification: specification, implementation: aigerRepresentation), "model checkig AIGER implementation failed")
    }

    static var allTests : [(String, (DetectorUnrealizableTest) -> () throws -> Void)] {
        return [
            ("testRealizabilityInputSymbolic", testRealizabilityInputSymbolic),
            ("testRealizabilityExplicit", testRealizabilityExplicit),
            ("testRealizabilitySmt", testRealizabilitySmt),
            ("testRealizabilityGameSolver", testRealizabilityGameSolver),
            ("testSynthesisInputSymbolic", testSynthesisInputSymbolic),
            ("testSynthesisExplicit", testSynthesisExplicit),
            ("testSynthesisSmt", testSynthesisSmt),
            ("testSynthesisGameSolver", testSynthesisGameSolver),
        ]
    }
}

