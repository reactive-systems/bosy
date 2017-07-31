
import XCTest

import Specification
import LTL
import Utils
import TransitionSystem

@testable import BoundedSynthesis

func modelCheckSMV(file: String) -> Bool {
    let task = Process()
    task.launchPath = "./Tools/NuSMV"
    task.arguments = ["-keep_single_value_vars", file]
    
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    // there may be a large amount of stdout data
    // by reading it before waiting, we avoid deadlocks
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let stdoutData = StreamHelper.readAllAvailableData(from: stdoutHandle)
    
    task.waitUntilExit()
    
    guard let stdout = String(data: stdoutData, encoding: String.Encoding.utf8) else {
        return false
    }
    
    for line in stdout.components(separatedBy: "\n") {
        if !line.hasPrefix("-- specification") {
            continue
        }
        if !line.hasSuffix("is true") {
            print(stdout)
            return false
        }
        return true
    }
    
    return false
}

class SimpleArbiterTest: XCTestCase {
    
    let jsonSpec = "{\"semantics\": \"mealy\", \"inputs\": [\"r_0\", \"r_1\", \"r_2\"], \"outputs\": [\"g_0\", \"g_1\", \"g_2\"], \"assumptions\": [], \"guarantees\": [\"(G (((! (g_0)) && (! (g_1))) || (((! (g_0)) || (! (g_1))) && (! (g_2)))))\", \"(G ((r_0) -> (F (g_0))))\", \"(G ((r_1) -> (F (g_1))))\", \"(G ((r_2) -> (F (g_2))))\"] }"
    
    var options = BoSyOptions()
    
    // Realizability
    func testRealizabilityInputSymbolic() {
        options.solver = .rareqs
        options.qbfPreprocessor = .bloqqer
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, LTL.BinaryOperator(.Implies,
                                         specification.assumptions.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) }),
                                         specification.guarantees.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) })))
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = InputSymbolicEncoding(options: options, automaton: automaton, specification: specification, synthesize: false)
        XCTAssertFalse(try encoding.solve(forBound: 2))
        XCTAssertTrue(try encoding.solve(forBound: 3))
        XCTAssertTrue(try encoding.solve(forBound: 4))
    }
    
    func testRealizabilityExplicit() {
        options.solver = .picosat
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, LTL.BinaryOperator(.Implies,
                                                                 specification.assumptions.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) }),
                                                                 specification.guarantees.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) })))
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = ExplicitEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertFalse(try encoding.solve(forBound: 2))
        XCTAssertTrue(try encoding.solve(forBound: 3))
        XCTAssertTrue(try encoding.solve(forBound: 4))
    }
    
    func testRealizabilitySmt() {
        options.solver = .z3
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, LTL.BinaryOperator(.Implies,
                                                                 specification.assumptions.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) }),
                                                                 specification.guarantees.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) })))
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = SmtEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertFalse(try encoding.solve(forBound: 2))
        XCTAssertTrue(try encoding.solve(forBound: 3))
        XCTAssertTrue(try encoding.solve(forBound: 4))
    }
    
    func testSynthesisInputSymbolic() {
        options.solver = .rareqs
        options.qbfPreprocessor = .bloqqer
        options.qbfCertifier = .quabs
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, LTL.BinaryOperator(.Implies,
                                                                 specification.assumptions.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) }),
                                                                 specification.guarantees.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) })))
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = InputSymbolicEncoding(options: options, automaton: automaton, specification: specification, synthesize: true)
        XCTAssertTrue(try encoding.solve(forBound: 3))
        guard let transitionSystem = encoding.extractSolution() as? SmvRepresentable else {
            XCTFail()
            fatalError()
        }
        guard let tempFile = TempFile(suffix: ".smv") else {
            XCTFail()
            fatalError()
        }
        do {
            try transitionSystem.smv.write(toFile: tempFile.path, atomically: true, encoding: .utf8)
        } catch {
            XCTFail()
            fatalError()
        }
        XCTAssertTrue(modelCheckSMV(file: tempFile.path))
    }
    
    func testSynthesisExplicit() {
        options.solver = .picosat
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, LTL.BinaryOperator(.Implies,
                                                                 specification.assumptions.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) }),
                                                                 specification.guarantees.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) })))
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = ExplicitEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 3))
        guard let transitionSystem = encoding.extractSolution() as? SmvRepresentable else {
            XCTFail()
            fatalError()
        }
        guard let tempFile = TempFile(suffix: ".smv") else {
            XCTFail()
            fatalError()
        }
        do {
            try transitionSystem.smv.write(toFile: tempFile.path, atomically: true, encoding: .utf8)
        } catch {
            XCTFail()
            fatalError()
        }
        XCTAssertTrue(modelCheckSMV(file: tempFile.path))
    }
    
    func testSynthesisSmt() {
        options.solver = .z3
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, LTL.BinaryOperator(.Implies,
                                                                 specification.assumptions.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) }),
                                                                 specification.guarantees.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) })))
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = SmtEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 3))
        guard let transitionSystem = encoding.extractSolution() as? SmvRepresentable else {
            XCTFail()
            fatalError()
        }
        guard let tempFile = TempFile(suffix: ".smv") else {
            XCTFail()
            fatalError()
        }
        do {
            try transitionSystem.smv.write(toFile: tempFile.path, atomically: true, encoding: .utf8)
        } catch {
            XCTFail()
            fatalError()
        }
        XCTAssertTrue(modelCheckSMV(file: tempFile.path))
    }
    
    static var allTests : [(String, (SimpleArbiterTest) -> () throws -> Void)] {
        return [
            ("testRealizabilityInputSymbolic", testRealizabilityInputSymbolic),
            ("testRealizabilityExplicit", testRealizabilityExplicit),
            ("testRealizabilitySmt", testRealizabilitySmt),
            ("testSynthesisInputSymbolic", testSynthesisInputSymbolic),
            ("testSynthesisExplicit", testSynthesisExplicit),
            ("testSynthesisSmt", testSynthesisSmt),
        ]
    }
}
