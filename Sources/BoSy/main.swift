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

var cancelled = false

class TerminationCondition {
    let lock = NSCondition()

    var remainingRealizabilityWorker: Int
    var successfulRealizability: Bool

    init(realizabilityWorker: Int) {
        lock.lock()
        remainingRealizabilityWorker = realizabilityWorker
        successfulRealizability = false
        lock.unlock()
    }

    func realizabilityDone(success: Bool) {
        lock.lock()
        if success {
            successfulRealizability = true
        }
        assert(remainingRealizabilityWorker > 0)
        remainingRealizabilityWorker -= 1
        if condition {
            lock.broadcast()
        }
        lock.unlock()
    }

    func wait() {
        lock.lock()
        if !condition {
            lock.wait()
        }
        lock.unlock()
    }

    var condition: Bool {
        return successfulRealizability || remainingRealizabilityWorker == 0
    }
}

func search(specification: SynthesisSpecification, player: Player) -> SafetyAutomaton<CoBüchiAutomaton.CounterState>? {
    do {
        let automaton = try CoBüchiAutomaton.from(ltl: !specification.ltl)
        Logger.default().info("automaton contains \(automaton.states.count) states")

        // search for minimal number of rejecting state visits
        let backend = SafetyGameReduction(options: BoSyOptions(), automaton: automaton, specification: specification)

        guard let rejectingCounter = try backend.searchMinimalLinear(cancelled: &cancelled) else {
            Logger.default().info("search for player \(player) aborted; either cancelled or max-bound reached")
            return nil
        }
        Logger.default().info("found solution with rejecting counter \(rejectingCounter)")
        return automaton.reduceToSafety(bound: rejectingCounter.value)
    } catch {
        Logger.default().error("search for winning strategy failed")
        Logger.default().error("\(error)")
        return nil
    }
}

func synthesizeSolution(specification: SynthesisSpecification, player: Player, safetyAutomaton: SafetyAutomaton<CoBüchiAutomaton.CounterState>) {
    do {
        var options = BoSyOptions()
        options.qbfCertifier = .quabs
        options.qbfPreprocessor = .bloqqer
        options.solver = .rareqs
        let synthesizer = InputSymbolicEncoding(options: options, automaton: safetyAutomaton, specification: specification, synthesize: true)
        var f = false
        guard let states = try synthesizer.searchMinimalExponential(cancelled: &f) else {
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
        Logger.default().error("synthesizing winning strategy failed")
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

    let termination = TerminationCondition(realizabilityWorker: 2)

    var winner: Player? = nil
    var safetyAutomaton: SafetyAutomaton<CoBüchiAutomaton.CounterState>? = nil

    // search for system strategy
    DispatchQueue.global().async {
        if let safety = search(specification: specification, player: .system) {
            winner = .system
            safetyAutomaton = safety
            termination.realizabilityDone(success: true)
        } else {
            termination.realizabilityDone(success: false)
        }
    }

    // search for environment strategy
    DispatchQueue.global().async {
        if let safety = search(specification: specification.dualized, player: .environment) {
            winner = .environment
            safetyAutomaton = safety
            termination.realizabilityDone(success: true)
        } else {
            termination.realizabilityDone(success: false)
        }
    }

    termination.wait()

    guard let w = winner else {
        print("result: unknown")
        exit(0)
    }

    guard synthesize else {
        print("result:", w == .system ? "realizable" : "unrealizable")
        exit(0)
    }

    guard let automaton = safetyAutomaton else {
        fatalError()
    }

    cancelled = true

    synthesizeSolution(specification: w == .system ? specification : specification.dualized, player: w, safetyAutomaton: automaton)

} catch {
    print(error)
    exit(1)
}

