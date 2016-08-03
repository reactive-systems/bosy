import Foundation

import Utils

import CAiger

func printArguments(name: String) {
    print("\(name) [--synthesize] [--strategy linear|exponential] instance.json")
}


var arguments: ArraySlice<String> = CommandLine.arguments[CommandLine.arguments.indices]
let executable = arguments.popFirst()!
var specificationFile: String? = nil
var synthesize = false
var searchStrategy: SearchStrategy = .Linear

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
    #if os(Linux)
        let standardInput = NSFileHandle.fileHandleWithStandardInput()
    #else
        let standardInput = FileHandle.standardInput
    #endif
    
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
        let assumptionString = specification.assumptions.joined(separator: " && ")
        let guaranteeString = specification.guarantees.joined(separator: " && ")

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

        var search = SolutionSearch(specification: specification, automaton: automaton, searchStrategy: strategy, player: player)

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

#if os(Linux)
let thread1 = NSThread() {
    searchSystem()
    condition.lock()
    finished = true
    condition.broadcast()
    condition.unlock()
}
let thread2 = NSThread() {
    searchEnvironment()
    condition.lock()
    finished = true
    condition.broadcast()
    condition.unlock()
}
thread1.start()
thread2.start()
#else
class ThreadedExecution: Thread {
    
    let function: () -> ()
    
    init(function: (() -> ())) {
        self.function = function
    }
    
    override func main() {
        function()
        condition.lock()
        finished = true
        condition.broadcast()
        condition.unlock()
    }
}

ThreadedExecution(function: searchSystem).start()
ThreadedExecution(function: searchEnvironment).start()
#endif

condition.lock()
if !finished {
    condition.wait()
}
condition.unlock()


