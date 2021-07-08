import Foundation

import Automata
import Logic
import Specification
import Utils

enum CommandLineOptionsError: Error, CustomStringConvertible {
    case empty
    case unknown(argument: String)
    case noValue(argument: String)
    case wrongChoice(argument: String, choice: String, choices: [String])
    case invalidCombination(message: String)
    case wrongType(message: String)

    var description: String {
        switch self {
        case .empty:
            return "no command line arguments given"
        case let .unknown(argument):
            return "unknown command line argument \"\(argument)\""
        case let .noValue(argument):
            return "argument \"\(argument)\" requires a value, but no value was given"
        case let .wrongChoice(argument, choice, choices):
            return "value \"\(choice)\" given for \"\(argument)\" is not valid\npossible values are \(choices)"
        case let .invalidCombination(message):
            return message
        case let .wrongType(message):
            return message
        }
    }
}

public enum Target: String {
    case aiger
    case dot
    case dotTopology = "dot-topology"
    case smv
    case verilog
    case all

    public static let allValues: [Target] = [.aiger, .dot, .dotTopology, .smv, .verilog, .all]
}

public enum SimplifcationLevel: String {
    case small //new default, faster
    case medium
    case high

    public static let allValues: [SimplifcationLevel] = [.small, .medium, .high]
}

public enum SimplifcationGoal: String {
    case any //new default, faster
    case small

    public static let allValues: [SimplifcationGoal] = [.any, .small]
}

public struct BoSyOptions {
    public var name: String = "BoSy"

    // default options
    public var specificationFile: String?
    public var synthesize: Bool = false
    public var searchStrategy: SearchStrategy = .exponential
    public var player: Players = .both
    public var backend: Backends = .inputSymbolic
    public var converter: LTL2AutomatonConverter = .spot("--any --small")
    public var semantics: TransitionSystemType?
    public var statistics: BoSyStatistics?
    public var target: Target = .aiger
    public var solver: SolverInstance?
    public var qbfCertifier: SolverInstance?
    public var qbfPreprocessor: QBFPreprocessorInstance?
    public var monolithic: Bool = true
    public var syntcomp2017rules: Bool = false
    public var minBound: Int = 1
    public var maxBound: Int?
    public var spotSimplGoal: SimplifcationGoal = .any
    public var spotSimplLevel: SimplifcationLevel = .small
    public var spotOptions: String?

    public init() {}

    public mutating func parseCommandLine() throws {
        var arguments: ArraySlice<String> = CommandLine.arguments[CommandLine.arguments.indices]
        name = arguments.popFirst()!

        var autoTool = "";

        while arguments.count > 0 {
            guard let argument = arguments.popFirst() else {
                throw CommandLineOptionsError.empty
            }

            switch argument {
            case "-h", "--help":
                printHelp()
                exit(0)
            case "-v", "--verbose":
                Logger.default().verbosity = .debug
            case "--synthesize":
                synthesize = true
            case "--strategy":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let strategy = SearchStrategy(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: SearchStrategy.allValues.map { $0.rawValue })
                }
                searchStrategy = strategy
            case "--player":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                switch value {
                case "system":
                    player = .system
                case "environment":
                    player = .environment
                case "both":
                    player = .both
                default:
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: ["system", "environment", "both"])
                }
            case "--backend":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _backend = Backends(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: Backends.allValues.map { $0.rawValue })
                }
                backend = _backend
            case "--automaton-tool":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                autoTool = value //deffering init until possibly needed spot params are read
            case "--semantics":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _semantics = TransitionSystemType(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: TransitionSystemType.allValues.map { $0.rawValue })
                }
                semantics = _semantics
            case "--statistics":
                statistics = BoSyStatistics()
            case "--target":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _target = Target(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: Target.allValues.map { $0.rawValue })
                }
                target = _target
            case "--solver":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _solver = SolverInstance(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: SolverInstance.allValues.map { $0.rawValue })
                }
                solver = _solver
            case "--spot-level":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _simpLevel = SimplifcationLevel(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: SimplifcationLevel.allValues.map { $0.rawValue })
                }
                spotSimplLevel = _simpLevel
            case "--spot-goal":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _simpGoal = SimplifcationGoal(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: SimplifcationGoal.allValues.map { $0.rawValue })
                }
                spotSimplGoal = _simpGoal
            case "--spot-opt":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                spotOptions = value;
            case "--qbf-certifier":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _solver = SolverInstance(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: SolverInstance.allValues.filter { $0.instance as? CertifyingQbfSolver != nil }.map { $0.rawValue })
                }
                if _solver.instance as? CertifyingQbfSolver == nil {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: SolverInstance.allValues.filter { $0.instance as? CertifyingQbfSolver != nil }.map { $0.rawValue })
                }
                qbfCertifier = _solver
            case "--qbf-preprocessor":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _preprocessor = QBFPreprocessorInstance(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: QBFPreprocessorInstance.allValues.map { $0.rawValue })
                }
                qbfPreprocessor = _preprocessor
            case "--monolithic":
                monolithic = true
            case "--syntcomp2017-rules":
                syntcomp2017rules = true
            case "--min-bound":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let intValue = Int(value) else {
                    throw CommandLineOptionsError.wrongType(message: "argument --min-bound must be a natural number")
                }
                if intValue < 1 {
                    throw CommandLineOptionsError.wrongType(message: "argument --min-bound must be larger than 0")
                }
                minBound = intValue
            case "--max-bound":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let intValue = Int(value) else {
                    throw CommandLineOptionsError.wrongType(message: "argument --max-bound must be a natural number")
                }
                if intValue < 1 {
                    throw CommandLineOptionsError.wrongType(message: "argument --max-bound must be larger than 0")
                }
                maxBound = intValue
            case "--bound":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let intValue = Int(value) else {
                    throw CommandLineOptionsError.wrongType(message: "argument --bound must be a natural number")
                }
                if intValue < 1 {
                    throw CommandLineOptionsError.wrongType(message: "argument --bound must be larger than 0")
                }
                minBound = intValue
                maxBound = intValue
            default:
                if !argument.hasPrefix("-") {
                    specificationFile = argument
                } else {
                    throw CommandLineOptionsError.unknown(argument: argument)
                }
            }
        }

        do { // add warnings if spot options set but spot not seleced
            let args = self.spotOptions ?? self.spotSimplGoal.rawValue + " " + self.spotSimplLevel.rawValue
            try converter = initAutomatonConverter(autoTool, args: args)
            if autoTool != "spot" && (spotSimplGoal != .any && spotSimplLevel != .small){
                 Logger.default().warning("Command line options for spot set but spot is not beeing used. Ignoring. \n Set options were \(args). \n")
            }
        }
        catch ParseError.toolNotFound(let name) {
            throw CommandLineOptionsError.wrongChoice(argument: "--automaton-tool", choice: name, choices: LTL2AutomatonConverter.allValues.map { $0.rawValue })
        }


        if let solver = solver {
            if !backend.supports(solver: solver) {
                throw CommandLineOptionsError.invalidCombination(message: "backend \"\(backend)\" does not support solver \"\(solver)\"")
            }
        } else {
            solver = backend.defaultSolver
        }

        if backend == .inputSymbolic {
            if qbfCertifier == nil {
                qbfCertifier = .quabs
            }
            if qbfPreprocessor == nil {
                qbfPreprocessor = .bloqqer
            }
        } else {
            if qbfCertifier != nil {
                Logger.default().info("switch --qbf-certifier has no effect in this configuration")
            }
            if qbfPreprocessor != nil {
                Logger.default().info("switch --qbf-preprocessor has no effect in this configuration")
            }
        }

        // check if bounds are valid
        if let maxBound = maxBound {
            if maxBound < minBound {
                throw CommandLineOptionsError.invalidCombination(message: "min-bound must be smaller or equal to max-bound")
            }
            if searchStrategy == .exponential, maxBound > 1, maxBound % 2 != 0 {
                throw CommandLineOptionsError.invalidCombination(message: "max-bound must be a multiple of 2 if exponential search strategy is selected")
            }
        }
        if searchStrategy == .exponential, minBound > 1, minBound % 2 != 0 {
            throw CommandLineOptionsError.invalidCombination(message: "min-bound must be a multiple of 2 if exponential search strategy is selected")
        }
    }

    public func printHelp() {
        print("\(name) [options] instance\n\n",
              "options:\n",
              "  --help\t\tshow this help and exit\n",
              "  --verbose\t\tshow verbose output\n",
              "  --synthesize\t\tconstruct AIGER solution after realizability\n",
              "  --statistics\t\tdisplay solving statistics\n",
              "  --strategy linear|exponential\n",
              "  --player both|system|environment\n",
              "  --backend \(Backends.allValues.map { $0.rawValue }.joined(separator: "|"))\n",
              "  --semantics \(TransitionSystemType.allValues.map { $0.rawValue }.joined(separator: "|"))\n",
              "  --automaton-tool \(LTL2AutomatonConverter.allValues.map { $0.rawValue }.joined(separator: "|"))\n",
              "  --spot-level \(SimplifcationLevel.allValues.map { $0.rawValue }.joined(separator: "|"))\n",
              "  --spot-goal \(SimplifcationGoal.allValues.map { $0.rawValue }.joined(separator: "|"))\n",
              "  --spot-options a string containing the cli options that should be passed to spot \n",
              "  --target \(Target.allValues.map { $0.rawValue }.joined(separator: "|"))\n",
              "  --solver \(SolverInstance.allValues.map { $0.rawValue }.joined(separator: "|"))\n",
              "  --qbf-certifier \(SolverInstance.allValues.filter { $0.instance as? CertifyingQbfSolver != nil }.map { $0.rawValue }.joined(separator: "|"))\n",
              "  --syntcomp2017-rules\t disable construction of environment counter-strategies\n")
    }
}
