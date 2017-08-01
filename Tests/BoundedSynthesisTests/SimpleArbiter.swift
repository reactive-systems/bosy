
import XCTest

import Specification
import LTL
import Utils
import TransitionSystem

import CAiger

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

/**
 * Tests if AIGER implementation satisfies given specification.
 *
 * Transforms specification to empty SMV model with LTLSPEC, then uses the tool
 * `smvtoaig` from the AIGER toolset to build an AIGER monitor.
 * Then, we combine monitor and implementation and use `aigbmc` to search for
 * bounded counterexamples.
 *
 * TODO: should use non-bounded model checker instead.
 */
func modelCheckAiger(specification: SynthesisSpecification, implementation: UnsafeMutablePointer<aiger>) throws -> Bool {
    guard let smvSecification = specification.smv else {
        fatalError()
    }
    guard let tempFile = TempFile(suffix: ".smv"),
          let monitorFile = TempFile(suffix: ".aig"),
          let implementationFile = TempFile(suffix: ".aig"),
          let combinedFile = TempFile(suffix: ".aig") else {
        fatalError()
    }
    guard (try? smvSecification.write(toFile: tempFile.path, atomically: true, encoding: .utf8)) != nil else {
        fatalError()
    }
    
    let buildMonitor = Process()
    buildMonitor.launchPath = "./Tools/smvtoaig"
    buildMonitor.arguments = ["-L", "Tools/ltl2smv", tempFile.path, monitorFile.path]

    buildMonitor.launch()
    
    buildMonitor.waitUntilExit()
    
    aiger_open_and_write_to_file(implementation, implementationFile.path)
    
    let buildCombined = Process()
    buildCombined.launchPath = "./Tools/combine-aiger"
    buildCombined.arguments = [monitorFile.path, implementationFile.path]
    
    let stdoutPipe = Pipe()
    buildCombined.standardOutput = stdoutPipe
    buildCombined.launch()
    
    // there may be a large amount of stdout data
    // by reading it before waiting, we avoid deadlocks
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let stdoutData = StreamHelper.readAllAvailableData(from: stdoutHandle)
    
    buildCombined.waitUntilExit()
    
    try stdoutData.write(to: combinedFile.url)
    
    let modelChecker = Process()
    modelChecker.launchPath = "./Tools/aigbmc"
    modelChecker.arguments = [combinedFile.path]
    
    let mcOutPipe = Pipe()
    modelChecker.standardOutput = mcOutPipe
    modelChecker.launch()
    
    // there may be a large amount of stdout data
    // by reading it before waiting, we avoid deadlocks
    let mcStdoutHandle = mcOutPipe.fileHandleForReading
    let mcStdoutData = StreamHelper.readAllAvailableData(from: mcStdoutHandle)

    modelChecker.waitUntilExit()
    
    guard let mcStdout = String(data: mcStdoutData, encoding: .utf8) else {
        fatalError()
    }
    if mcStdout.hasPrefix("1") {
        // found counterexample
        print(mcStdout)
        return false
    }
    
    return true
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
        let ltlSpec = LTL.UnaryOperator(.Not, specification.ltl)
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
        let ltlSpec = LTL.UnaryOperator(.Not, specification.ltl)
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
        let ltlSpec = LTL.UnaryOperator(.Not, specification.ltl)
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = SmtEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertFalse(try encoding.solve(forBound: 2))
        XCTAssertTrue(try encoding.solve(forBound: 3))
        XCTAssertTrue(try encoding.solve(forBound: 4))
    }
    
    func testRealizabilityGameSolver() {
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, specification.ltl)
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        let encoding = SafetyGameReduction(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 1))
    }
    
    func testSynthesisInputSymbolic() {
        options.solver = .rareqs
        options.qbfPreprocessor = .bloqqer
        options.qbfCertifier = .quabs
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, specification.ltl)
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = InputSymbolicEncoding(options: options, automaton: automaton, specification: specification, synthesize: true)
        XCTAssertTrue(try encoding.solve(forBound: 3))
        guard let transitionSystem = encoding.extractSolution() else {
            XCTFail()
            fatalError()
        }
        
        // Check SMV implementation
        guard let smvRepresentation = (transitionSystem as? SmvRepresentable)?.smv else {
            XCTFail()
            fatalError()
        }
        guard let tempFile = TempFile(suffix: ".smv") else {
            XCTFail()
            fatalError()
        }
        do {
            try smvRepresentation.write(toFile: tempFile.path, atomically: true, encoding: .utf8)
        } catch {
            XCTFail()
            fatalError()
        }
        XCTAssertTrue(modelCheckSMV(file: tempFile.path))
        
        // Check AIGER implementation
        guard let aigerRepresentation = (transitionSystem as? AigerRepresentable)?.aiger else {
            XCTFail()
            fatalError()
        }
        XCTAssertTrue(try modelCheckAiger(specification: specification, implementation: aigerRepresentation))
    }
    
    func testSynthesisExplicit() {
        options.solver = .picosat
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, specification.ltl)
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = ExplicitEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 3))
        guard let transitionSystem = encoding.extractSolution() else {
            XCTFail()
            fatalError()
        }
        
        // Check SMV implementation
        guard let smvRepresentation = (transitionSystem as? SmvRepresentable)?.smv else {
            XCTFail()
            fatalError()
        }
        guard let tempFile = TempFile(suffix: ".smv") else {
            XCTFail()
            fatalError()
        }
        do {
            try smvRepresentation.write(toFile: tempFile.path, atomically: true, encoding: .utf8)
        } catch {
            XCTFail()
            fatalError()
        }
        XCTAssertTrue(modelCheckSMV(file: tempFile.path))
        
        // Check AIGER implementation
        guard let aigerRepresentation = (transitionSystem as? AigerRepresentable)?.aiger else {
            XCTFail()
            fatalError()
        }
        XCTAssertTrue(try modelCheckAiger(specification: specification, implementation: aigerRepresentation))
    }
    
    func testSynthesisSmt() {
        options.solver = .z3
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, specification.ltl)
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = SmtEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 3))
        guard let transitionSystem = encoding.extractSolution() else {
            XCTFail()
            fatalError()
        }
        
        // Check SMV implementation
        guard let smvRepresentation = (transitionSystem as? SmvRepresentable)?.smv else {
            XCTFail()
            fatalError()
        }
        guard let tempFile = TempFile(suffix: ".smv") else {
            XCTFail()
            fatalError()
        }
        do {
            try smvRepresentation.write(toFile: tempFile.path, atomically: true, encoding: .utf8)
        } catch {
            XCTFail()
            fatalError()
        }
        XCTAssertTrue(modelCheckSMV(file: tempFile.path))
        
        // Check AIGER implementation
        guard let aigerRepresentation = (transitionSystem as? AigerRepresentable)?.aiger else {
            XCTFail()
            fatalError()
        }
        XCTAssertTrue(try modelCheckAiger(specification: specification, implementation: aigerRepresentation))
    }
    
    func testSynthesisGameSolver() {
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, specification.ltl)
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        let encoding = SafetyGameReduction(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 1))
        guard let transitionSystem = encoding.extractSolution() else {
            XCTFail()
            fatalError()
        }
        // Check AIGER implementation
        guard let aigerRepresentation = (transitionSystem as? AigerRepresentable)?.aiger else {
            XCTFail()
            fatalError()
        }
        XCTAssertTrue(try modelCheckAiger(specification: specification, implementation: aigerRepresentation), "model checkig AIGER implementation failed")
    }
    
    static var allTests : [(String, (SimpleArbiterTest) -> () throws -> Void)] {
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
