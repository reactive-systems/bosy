import Foundation


enum CommandLineOptionsError: Error, CustomStringConvertible {
    case empty
    case unknown(argument: String)
    case noValue(argument: String)
    case wrongChoice(argument: String, choice: String, choices: [String])
    case invalidCombination(message: String)
    
    var description: String {
        switch self {
        case .empty:
            return "no command line arguments given"
        case .unknown(let argument):
            return "unknown command line argument \"\(argument)\""
        case .noValue(let argument):
            return "argument \"\(argument)\" requires a value, but no value was given"
        case .wrongChoice(let argument, let choice, let choices):
            return "value \"\(choice)\" given for \"\(argument)\" is not valid\npossible values are \(choices)"
        case .invalidCombination(let message):
            return message
        }
    }
}

enum Target: String {
    case aiger = "aiger"
    case dot   = "dot"
    case smv   = "smv"
    
    static let allValues: [Target] = [.aiger, .dot, .smv]
}


struct BoSyOptions {
    
    var name: String = "BoSy"
    
    // default options
    var specificationFile: String? = nil
    var synthesize: Bool = false
    var searchStrategy: SearchStrategy = .exponential
    var player: Players = .both
    var backend: Backends = .inputSymbolic
    var converter: LTL2AutomatonConverter = .ltl3ba
    var semantics: TransitionSystemType? = nil
    var statistics: BoSyStatistics? = nil
    var target: Target = .aiger
    var solver: SolverInstance? = nil
    
    mutating func parseCommandLine() throws {
        var arguments: ArraySlice<String> = CommandLine.arguments[CommandLine.arguments.indices]
        name = arguments.popFirst()!
        
        while arguments.count > 0 {
            guard let argument = arguments.popFirst() else {
                throw CommandLineOptionsError.empty
            }
            
            switch argument {
            case "-h", "--help":
                printHelp()
                exit(0)
            case "--synthesize":
                synthesize = true
            case "--strategy":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let strategy = SearchStrategy(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: SearchStrategy.allValues.map(String.init(describing:)))
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
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: Backends.allValues.map(String.init(describing:)))
                }
                backend = _backend
            case "--automaton-tool":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let automatonConverter = LTL2AutomatonConverter(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: LTL2AutomatonConverter.allValues.map(String.init(describing:)))
                }
                converter = automatonConverter
            case "--semantics":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _semantics = TransitionSystemType(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: TransitionSystemType.allValues.map(String.init(describing:)))
                }
                semantics = _semantics
            case "--statistics":
                statistics = BoSyStatistics()
            case "--target":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _target = Target(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: Target.allValues.map(String.init(describing:)))
                }
                target = _target
            case "--solver":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _solver = SolverInstance(rawValue: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: SolverInstance.allValues.map(String.init(describing:)))
                }
                solver = _solver
            default:
                if !argument.hasPrefix("-") {
                    specificationFile = argument
                } else {
                    throw CommandLineOptionsError.unknown(argument: argument)
                }
            }
        }
        
        if let solver = solver {
            if !backend.supports(solver: solver) {
                throw CommandLineOptionsError.invalidCombination(message: "backend \"\(backend)\" does not support solver \"\(solver)\"")
            }
        } else {
            solver = backend.defaultSolver
        }
    }
    
    
    func printHelp() {
        print("\(name) [options] instance\n\n",
              "options:\n",
              "  --help\t\tshow this help and exit\n",
              "  --synthesize\t\tconstruct AIGER solution after realizability\n",
              "  --statistics\t\tdisplay solving statistics\n",
              "  --strategy linear|exponential\n",
              "  --player both|system|environment\n",
              "  --backend \(Backends.allValues.map(String.init(describing:)).joined(separator: "|"))\n",
              "  --semantics \(TransitionSystemType.allValues.map(String.init(describing:)).joined(separator: "|"))\n",
              "  --automaton-tool \(LTL2AutomatonConverter.allValues.map(String.init(describing:)).joined(separator: "|"))\n",
              "  --target \(Target.allValues.map(String.init(describing:)).joined(separator: "|"))\n",
              "  --solver \(SolverInstance.allValues.map(String.init(describing:)).joined(separator: "|"))\n"
        )
    }
    
}
