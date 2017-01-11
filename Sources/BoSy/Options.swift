import Foundation


enum CommandLineOptionsError: Error {
    case empty
    case unknown(argument: String)
    case noValue(argument: String)
    case wrongChoice(argument: String, choice: String, choices: [String])
}


struct BoSyOptions {
    
    var name: String = "BoSy"
    
    // default options
    var specificationFile: String? = nil
    var synthesize: Bool = false
    var searchStrategy: SearchStrategy = .Exponential
    var player: Player? = nil
    var backend: Backends = .InputSymbolic
    var converter: LTL2AutomatonConverter = .ltl3ba
    var semantics: TransitionSystemType? = nil
    var statistics: BoSyStatistics? = nil
    
    mutating func parseCommandLine() throws {
        var arguments: ArraySlice<String> = CommandLine.arguments[CommandLine.arguments.indices]
        name = arguments.popFirst()!
        
        while arguments.count > 0 {
            guard let argument = arguments.popFirst() else {
                throw CommandLineOptionsError.empty
            }
            
            switch argument {
            case "--synthesize":
                synthesize = true
            case "--strategy":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                switch value {
                case "linear":
                    searchStrategy = .Linear
                case "exponential":
                    searchStrategy = .Exponential
                default:
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: ["linear", "exponential"])
                }
            case "--player":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                switch value {
                case "system":
                    player = .System
                case "environment":
                    player = .Environment
                case "both":
                    player = nil
                default:
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: ["system", "environment", "both"])
                }
            case "--backend":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _backend = Backends.fromString(value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: Backends.allValues.map(String.init(describing:)))
                }
                backend = _backend
            case "--automaton-tool":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let automatonConverter = LTL2AutomatonConverter.from(string: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: LTL2AutomatonConverter.allValues.map(String.init(describing:)))
                }
                converter = automatonConverter
            case "--semantics":
                guard let value = arguments.popFirst() else {
                    throw CommandLineOptionsError.noValue(argument: argument)
                }
                guard let _semantics = TransitionSystemType.from(string: value) else {
                    throw CommandLineOptionsError.wrongChoice(argument: argument, choice: value, choices: TransitionSystemType.allValues.map(String.init(describing:)))
                }
                semantics = _semantics
            case "--statistics":
                statistics = BoSyStatistics()
            default:
                if !argument.hasPrefix("-") {
                    specificationFile = argument
                } else {
                    throw CommandLineOptionsError.unknown(argument: argument)
                }
            }
        }
    }
    
    
    func printHelp() {
        print("\(name) [options] instance\n\n",
              "options:\n",
              "  --synthesize\n",
              "  --strategy linear|exponential\n",
              "  --player both|system|environment")
    }
    
}
