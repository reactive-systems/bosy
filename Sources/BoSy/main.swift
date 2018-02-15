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

func synthesizeSolution(specification: SynthesisSpecification, player: Player, safetyAutomaton: SafetyAutomaton<CoBüchiAutomaton.CounterState>) -> UnsafeMutablePointer<aiger>? {
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
            return nil
        }
        let minimized = aiger_solution.minimized
        return minimized
    } catch {
        Logger.default().error("synthesizing winning strategy failed")
        Logger.default().error("\(error)")
        return nil
    }
}

func optimizeSolution(specification: SynthesisSpecification, player: Player, safetyAutomaton: SafetyAutomaton<CoBüchiAutomaton.CounterState>, solution: UnsafeMutablePointer<aiger>) -> AigerSolution? {
    do {
        var options = BoSyOptions()
        options.solver = .cryptominisat
        let optimizer = AigerEncoding(options: options, automaton: safetyAutomaton, specification: specification, stateBits: Int(solution.pointee.num_latches))

        var bound = NumberOfAndGatesInAIGER(value: Int(solution.pointee.num_ands))
        var solution: AigerSolution? = nil
        while bound.value >= 0, try optimizer.solve(forBound: bound) {
            solution = optimizer.extractSolution() as? AigerSolution
            bound = NumberOfAndGatesInAIGER(value: bound.value - 1)
            currentlySmallestSolution = solution?.aiger
        }
        return solution

    } catch {
        Logger.default().error("optimizing winning strategy failed")
        Logger.default().error("\(error)")
        return nil
    }
}

var currentlySmallestSolution: UnsafeMutablePointer<aiger>? = nil

signal(SIGINT) {
    s in
    Logger.default().info("got SIGINT, terminating...")
    guard let solution = currentlySmallestSolution else {
        Logger.default().info("did not find solution")
        exit(1)
    }
    Logger.default().info("found solution! printing to stdout...")
    aiger_write_to_file(solution, aiger_ascii_mode, stdout)
    exit(0)
}

do {
    // MARK: - argument parsing
    let parser = ArgumentParser(commandName: "BoSy", usage: "[options] specification", overview: "BoSy is a reactive synthesis tool from temporal specifications.")
    let specificationFile = parser.add(positional: "specification", kind: String.self, optional: true, usage: "a file containing the specification in BoSy format", completion: .filename)
    let readStdinOption = parser.add(option: "--read-from-stdin", shortName: "-in", kind: Bool.self, usage: "read specification from standard input")
    let synthesizeOption = parser.add(option: "--synthesize", kind: Bool.self, usage: "construct system after checking realizability")
    let verbosityOption = parser.add(option: "--verbose", shortName: "-v", kind: Bool.self, usage: "enable verbose output")
    let optimizeOption = parser.add(option: "--optimize", kind: Bool.self, usage: "optimize parameter")
    let syntcompOption = parser.add(option: "--syntcomp", kind: Bool.self, usage: "enable mode that is tailored to the rules of the reactive synthesis competition")

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
    let syntcomp = parsed.get(syntcompOption) ?? false
    let optimize = parsed.get(optimizeOption) ?? syntcomp  // always optimize in syntcomp mode

    Logger.default().verbosity = verbose ? .debug : .info

    if syntcomp {
        //Logger.default().verbosity = .warning
    }

    // MARK: - concurrent execution of search strategy

    let termination = TerminationCondition(realizabilityWorker: 2)

    var winner: Player? = nil
    var safetyAutomaton: SafetyAutomaton<CoBüchiAutomaton.CounterState>? = nil

    // search for system strategy
    DispatchQueue(label: "system").async {
        if let safety = search(specification: specification, player: .system) {
            winner = .system
            safetyAutomaton = safety
            termination.realizabilityDone(success: true)
        } else {
            termination.realizabilityDone(success: false)
        }
    }

    // search for environment strategy
    DispatchQueue(label: "environment").async {
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

    if syntcomp && w == .environment {
        // in syntcomp, we do not need to synthesize counter-strategies
        print("result:", w == .system ? "realizable" : "unrealizable")
        exit(0)
    }

    guard let automaton = safetyAutomaton else {
        fatalError()
    }

    cancelled = true

    guard let solution = synthesizeSolution(specification: w == .system ? specification : specification.dualized, player: w, safetyAutomaton: automaton) else {
        fatalError()
    }

    if !optimize {
        aiger_write_to_file(solution, aiger_ascii_mode, stdout)
        w == .system ? print("result: realizable") : print("result: unrealizable")
        exit(0)
    }

    currentlySmallestSolution = solution

    if let optimized = optimizeSolution(specification: w == .system ? specification : specification.dualized, player: w, safetyAutomaton: automaton, solution: solution) {
        aiger_write_to_file(optimized.aiger, aiger_ascii_mode, stdout)
        w == .system ? print("result: realizable") : print("result: unrealizable")
        exit(0)
    } else {
        aiger_write_to_file(solution, aiger_ascii_mode, stdout)
        w == .system ? print("result: realizable") : print("result: unrealizable")
        exit(0)
    }


} catch {
    print(error)
    exit(1)
}

