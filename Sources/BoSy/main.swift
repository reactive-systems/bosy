import Foundation
import Dispatch

import Utils

import CAiger

func printArguments(name: String) {
    print("\(name) [--synthesize] [--strategy linear|exponential] [--player both|system|environment] instance.json")
}



var arguments: ArraySlice<String> = CommandLine.arguments[CommandLine.arguments.indices]
let executable = arguments.popFirst()!
var specificationFile: String? = nil
var synthesize = false
var searchStrategy: SearchStrategy = .Linear
var player: Player? = nil
var backend: Backends = .InputSymbolic

while arguments.count > 0 {
    guard let argument = arguments.popFirst() else {
        printArguments(name: executable)
        exit(1)
    }
    if argument == "--synthesize" {
        synthesize = true
    } else if argument == "--strategy" {
        guard let value = arguments.popFirst() else {
            print("no value for strategy given, can be either linear or exponential")
            exit(1)
        }
        switch value {
        case "linear":
            searchStrategy = .Linear
        case "exponential":
            searchStrategy = .Exponential
        default:
            print("wrong value \"\(value)\" for strategy, can be either linear or exponential")
            exit(1)
        }
    } else if argument == "--player" {
        guard let value = arguments.popFirst() else {
            print("no value for player given, can be either system or environment")
            exit(1)
        }
        switch value {
        case "system":
            player = .System
        case "environment":
            player = .Environment
        case "both":
            player = nil
        default:
            print("wrong value \"\(value)\" for player, can be either system or environment")
            exit(1)
        }
    } else if !argument.hasPrefix("-") {
        specificationFile = argument
        break
    } else {
        printArguments(name: executable)
        exit(1)
    }
}

let json: String

if let specificationFile = specificationFile {
    guard let specficationString = try? String(contentsOfFile: specificationFile, encoding: String.Encoding.utf8) else {
        print("error: cannot read input file \(specificationFile)")
        exit(1)
    }
    json = specficationString
} else {
    // Read from stdin
    let standardInput = FileHandle.standardInput
    
    var input = StreamHelper.readAllAvailableData(from: standardInput)
    
    guard let specficationString = String(data: input, encoding: String.Encoding.utf8) else {
        print("error: cannot read input from stdin")
        exit(1)
    }
    json = specficationString
}

guard let specification = BoSyInputFileFormat.fromJson(string: json) else {
    print("error: cannot parse specification")
    exit(1)
}

//Logger.default().info("inputs: \(specification.inputs), outputs: \(specification.outputs)")
//Logger.default().info("assumptions: \(specification.assumptions), guarantees: \(specification.guarantees)")

func search(strategy: SearchStrategy, player: Player, synthesize: Bool) -> (() -> ()) {
    return {
        let assumptionString = specification.assumptions.map(String.init(describing:)).joined(separator: " && ")
        let guaranteeString = specification.guarantees.map(String.init(describing:)).joined(separator: " && ")

        let ltlSpec: String
        if player == .System {
            ltlSpec = specification.assumptions.count == 0 ? "!(\(guaranteeString))" : "!((\(assumptionString)) -> (\(guaranteeString)))"
        } else {
            assert(player == .Environment)
            ltlSpec = specification.assumptions.count == 0 ? "\(guaranteeString)" : "(\(assumptionString)) -> (\(guaranteeString))"
        }
        
        guard let automaton = ltl3ba(ltl: ltlSpec) else {
            Logger.default().error("could not construct automaton")
            return
        }

        //Logger.default().info("automaton: \(automaton)")

        var search = SolutionSearch(specification: specification, automaton: automaton, searchStrategy: strategy, player: player, backend: backend)

        if search.hasSolution() {
            if !synthesize {
                player == .System ? print("realizable") : print("unrealizable")
                return
            }
            guard let solution = search.getSolution() else {
                Logger.default().error("could not construct solution")
                return
            }
            guard let aiger_solution = solution.toAiger() else {
                Logger.default().error("could not encode solution as AIGER")
                return
            }
            let minimized = minimizeWithABC(aiger_solution)
            aiger_write_to_file(minimized, aiger_ascii_mode, stdout)
            player == .System ? print("realizable") : print("unrealizable")
            return
        }
    }
}

//search(strategy: .Linear, player: .System, synthesize: synthesize)()

let condition = NSCondition()
var finished = false


let searchSystem = search(strategy: searchStrategy, player: .System, synthesize: synthesize)
let searchEnvironment = search(strategy: searchStrategy, player: .Environment, synthesize: synthesize)

let doSearchSystem = player == nil || player == .System
let doSearchEnvironment = player == nil || player == .Environment

if doSearchSystem {
    DispatchQueue.global().async {
        searchSystem()
        condition.lock()
        finished = true
        condition.broadcast()
        condition.unlock()
    }
}

if doSearchEnvironment {
    DispatchQueue.global().async {
        searchEnvironment()
        condition.lock()
        finished = true
        condition.broadcast()
        condition.unlock()
    }
}

condition.lock()
if !finished {
    condition.wait()
}
condition.unlock()


