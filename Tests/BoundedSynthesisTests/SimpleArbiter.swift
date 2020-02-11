
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
    let tempFile = try TemporaryFile(suffix: ".smv")
    let monitorFile = try TemporaryFile(suffix: ".aig")
    let implementationFile = try TemporaryFile(suffix: ".aig")
    let combinedFile = try TemporaryFile(suffix: ".aig")

    tempFile.fileHandle.write(Data(smvSecification.utf8))


    try Basic.Process.checkNonZeroExit(arguments: ["./Tools/smvtoaig", "-L", "Tools/ltl2smv", tempFile.path.pathString, monitorFile.path.pathString])
    
    aiger_open_and_write_to_file(implementation, implementationFile.path.pathString)

    let combiner = Basic.Process(arguments: ["./Tools/combine-aiger", monitorFile.path.pathString, implementationFile.path.pathString])
    try combiner.launch()
    let combinationResult = try combiner.waitUntilExit()
    let sequence: [UInt8] = try combinationResult.output.dematerialize()

    combinedFile.fileHandle.write(Data(bytes: sequence))

    let modelCheckOutput = try Basic.Process.checkNonZeroExit(arguments: ["./Tools/aigbmc", combinedFile.path.pathString])

    if modelCheckOutput.hasPrefix("1") {
        // found counterexample
        print(modelCheckOutput)
        return false
    }
    
    return true
}

class SimpleArbiterTest: XCTestCase {
    
    let jsonSpec = "{\"semantics\": \"mealy\", \"inputs\": [\"r_0\", \"r_1\", \"r_2\"], \"outputs\": [\"g_0\", \"g_1\", \"g_2\"], \"assumptions\": [], \"guarantees\": [\"(G (((! (g_0)) && (! (g_1))) || (((! (g_0)) || (! (g_1))) && (! (g_2)))))\", \"(G ((r_0) -> (F (g_0))))\", \"(G ((r_1) -> (F (g_1))))\", \"(G ((r_2) -> (F (g_2))))\"] }"
    
    var options = BoSyOptions()
    
    // Realizability
    func testRealizabilityInputSymbolic() throws {
        options.solver = .rareqs
        options.qbfPreprocessor = .bloqqer
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            return
        }
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
        let encoding = InputSymbolicEncoding(options: options, automaton: automaton, specification: specification, synthesize: false)
        XCTAssertFalse(try encoding.solve(forBound: 2))
        XCTAssertTrue(try encoding.solve(forBound: 3))
        XCTAssertTrue(try encoding.solve(forBound: 4))
    }
    
    func testRealizabilityExplicit() throws {
        options.solver = .picosat
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            return
        }
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
        var encoding = ExplicitEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertFalse(try encoding.solve(forBound: 2))
        XCTAssertTrue(try encoding.solve(forBound: 3))
        XCTAssertTrue(try encoding.solve(forBound: 4))
    }
    
    func testRealizabilitySmt() throws {
        options.solver = .z3
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            return
        }
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
        var encoding = SmtEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertFalse(try encoding.solve(forBound: 2))
        XCTAssertTrue(try encoding.solve(forBound: 3))
        XCTAssertTrue(try encoding.solve(forBound: 4))
    }
    
    func testRealizabilityGameSolver() throws {
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            return
        }
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
        let encoding = SafetyGameReduction(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 1))
    }
    
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
        XCTAssertTrue(try encoding.solve(forBound: 3))
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
    
    func testSynthesisExplicit() throws {
        options.solver = .picosat
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            return
        }
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
        var encoding = ExplicitEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 3))
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
    
    func testSynthesisSmt() throws {
        options.solver = .z3
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            return
        }
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
        var encoding = SmtEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertTrue(try encoding.solve(forBound: 3))
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
    
    func testSynthesisGameSolver() throws {
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            return
        }
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
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

    func testAigerSmtBackend() throws {
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            return
        }
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
        let encoding = AigerSmtEncoding(options: options, automaton: automaton, specification: specification, stateBits: 2)
        XCTAssertFalse(try encoding.solve(forBound: NumberOfAndGatesInAIGER(value: 0)))
        XCTAssertTrue(try encoding.solve(forBound: NumberOfAndGatesInAIGER(value: 1)))
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

    func testAigerInputSymbolicBackend() throws {
        options.solver = .rareqs
        options.qbfPreprocessor = .bloqqer
        options.qbfCertifier = .quabs
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            return
        }
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
        let encoding = AigerInputSymbolicEncoding(options: options, automaton: automaton, specification: specification, stateBits: 2)
        XCTAssertFalse(try encoding.solve(forBound: NumberOfAndGatesInAIGER(value: 0)))
        XCTAssertTrue(try encoding.solve(forBound: NumberOfAndGatesInAIGER(value: 1)))
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
