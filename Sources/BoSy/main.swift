import Foundation
import Dispatch

import Basic
import Utility

import Utils
import Specification
import Automata
import BoundedSynthesis
import TransitionSystem
import LTL
import CAiger

func search(specification: SynthesisSpecification, player: Player, synthesize: Bool) {
    do {
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
        Logger.default().info("automaton contains \(automaton.states.count) states")

        // search for minimal number of rejecting state visits
        let backend = SafetyGameReduction(options: BoSyOptions(), automaton: automaton, specification: specification)

        guard let rejectingCounter = try backend.searchMinimalLinear() else {
            fatalError()
        }
        Logger.default().info("found solution with rejecting counter \(rejectingCounter)")
        guard synthesize else {
            print("result:", player == .system ? "realizable" : "unrealizable")
            return
        }

        let safetyAutomaton = automaton.reduceToSafety(bound: rejectingCounter.value)
        var options = BoSyOptions()
        options.qbfCertifier = .quabs
        options.qbfPreprocessor = .bloqqer
        options.solver = .rareqs
        let synthesizer = InputSymbolicEncoding(options: options, automaton: safetyAutomaton, specification: specification, synthesize: true)
        guard let states = try synthesizer.searchMinimalLinear() else {
            fatalError()
        }
        Logger.default().info("found solution with \(states) states")

        guard let solution = synthesizer.extractSolution() else {
            fatalError()
        }
        guard let aiger_solution = (solution as? AigerRepresentable)?.aiger else {
            Logger.default().error("could not encode solution as AIGER")
            return
        }
        let minimized = aiger_solution.minimized
        aiger_write_to_file(minimized, aiger_ascii_mode, stdout)
        player == .system ? print("result: realizable") : print("result: unrealizable")

    } catch {
        Logger.default().error("search for winning strategy failed")
        Logger.default().error("\(error)")
    }
}

do {
    // MARK: - argument parsing
    let parser = ArgumentParser(commandName: "BoSy", usage: "[options] specification", overview: "BoSy is a reactive synthesis tool from temporal specifications.")
    let specificationFile = parser.add(positional: "specification", kind: String.self, optional: true, usage: "a file containing the specification in BoSy format", completion: .filename)
    let readStdinOption = parser.add(option: "--read-from-stdin", shortName: "-in", kind: Bool.self, usage: "read specification from standard input")
    let synthesizeOption = parser.add(option: "--synthesize", kind: Bool.self, usage: "construct system after checking realizability")
    let verbosityOption = parser.add(option: "--verbose", shortName: "-v", kind: Bool.self, usage: "enable verbose output")

    let arguments = Array(CommandLine.arguments.dropFirst())
    let parsed = try parser.parse(arguments)


    // either --stdin was given or specification file
    let specification: SynthesisSpecification
    let readStdin = parsed.get(readStdinOption) ?? false
    if readStdin {
        // attemp to read from standard input
        guard parsed.get(specificationFile) == nil else {
            throw ArgumentParserError.unexpectedArgument("\"specification\": cannot be combined with reading from standard input")
        }
        let input = StreamHelper.readAllAvailableData(from: FileHandle.standardInput)
        specification = try SynthesisSpecification.from(data: input)

    } else if let fileName = parsed.get(specificationFile) {
        specification = try SynthesisSpecification.from(fileName: fileName)
    } else {
        throw ArgumentParserError.expectedArguments(parser, ["input file was not specified; use --help to list available arguments"])
    }

    let synthesize = parsed.get(synthesizeOption) ?? false
    let verbose = parsed.get(verbosityOption) ?? false

    Logger.default().verbosity = verbose ? .debug : .info

    // MARK: - concurrent execution of search strategy

    let condition = NSCondition()
    condition.lock()
    var finished = false
    condition.unlock()

    // search for system strategy
    DispatchQueue.global().async {
        search(specification: specification, player: .system, synthesize: synthesize)
        condition.lock()
        finished = true
        condition.broadcast()
        condition.unlock()
    }

    // search for environment strategy
    DispatchQueue.global().async {
        search(specification: specification.dualized, player: .environment, synthesize: synthesize)
        condition.lock()
        finished = true
        condition.broadcast()
        condition.unlock()
    }

    condition.lock()
    if !finished {
        condition.wait()
    }
    condition.unlock()

    

} catch {
    print(error)
    exit(1)
}

