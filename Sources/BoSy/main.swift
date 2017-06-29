import Foundation
//import Dispatch

import Utils

import CAiger


var options = BoSyOptions()

do {
    try options.parseCommandLine()
} catch {
    print(error)
    options.printHelp()
    exit(1)
}

let json: String

let parseTimer = options.statistics?.startTimer(phase: .parsing)

if let specificationFile = options.specificationFile {
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

guard var specification = BoSyInputFileFormat.fromJson(string: json) else {
    print("error: cannot parse specification")
    exit(1)
}

parseTimer?.stop()

// override semantics if given as command line argument
if let semantics = options.semantics {
    specification.semantics = semantics
}

/*if paths {
    let unrolling = Unrolling(specification: specification)
    var i = 1
    while true {
        guard let instance = unrolling.getEncoding(forBound: i) else {
            exit(0)
        }
        print("Path length = \(i)")
        
        let qcirVisitor = QCIRVisitor(formula: instance)
        guard let (result, certificate) = quabs(qcir: "\(qcirVisitor)") else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        //try? "\(qcirVisitor)".write(toFile: "/Users/leander/Desktop/bounded-tree-models/arbiter_15_\(i).qcir", atomically: false, encoding: .ascii)
        
        
        /*let qdimacsVisitor = QDIMACSVisitor(formula: instance)
        guard let (result, assignments) = rareqs(qdimacs: bloqqer(qdimacs: "\(qdimacsVisitor)")) else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }*/
        if result == .SAT {
            print("realizable")
            exit(0)
        }
        
        i += 1
    }
}*/

//Logger.default().info("inputs: \(specification.inputs), outputs: \(specification.outputs)")
//Logger.default().info("assumptions: \(specification.assumptions), guarantees: \(specification.guarantees)")

private func buildAutomaton(player: Player) -> CoBüchiAutomaton? {
    if options.monolithic || player == .environment || specification.assumptions.count > 0 {
        let assumptionString = specification.assumptions.map(String.init(describing:)).joined(separator: " && ")
        let guaranteeString = specification.guarantees.map(String.init(describing:)).joined(separator: " && ")
        
        let ltlSpec: String
        if player == .system {
            ltlSpec = specification.assumptions.count == 0 ? "!(\(guaranteeString))" : "!((\(assumptionString)) -> (\(guaranteeString)))"
        } else {
            assert(player == .environment)
            ltlSpec = specification.assumptions.count == 0 ? "\(guaranteeString)" : "(\(assumptionString)) -> (\(guaranteeString))"
        }
        
        let automatonTimer = options.statistics?.startTimer(phase: .ltl2automaton)
        guard let automaton = options.converter.convert(ltl: ltlSpec) else {
            Logger.default().error("could not construct automaton")
            return nil
        }
        automatonTimer?.stop()
        return automaton
    } else {
        assert(specification.assumptions.count == 0)
        assert(player == .system)
        
        var automata: [CoBüchiAutomaton] = []
        for guarantee in specification.guarantees {
            let automatonTimer = options.statistics?.startTimer(phase: .ltl2automaton)
            guard let automaton = options.converter.convert(ltl: "!(\(guarantee))") else {
                Logger.default().error("could not construct automaton")
                return nil
            }
            automatonTimer?.stop()
            automata.append(automaton)
        }
        
        return CoBüchiAutomaton(automata: automata)
    }
}

func search(strategy: SearchStrategy, player: Player, synthesize: Bool) -> (() -> ()) {
    return {
        guard let automaton = buildAutomaton(player: player) else {
            return
        }

        Logger.default().info("automaton contains \(automaton.states.count) states")

        let synthesize = synthesize && !(player == .environment && options.syntcomp2017rules)
        
        var search = SolutionSearch(specification: specification, automaton: automaton, searchStrategy: strategy, player: player, backend: options.backend, initialBound: options.minBound, synthesize: synthesize)

        if search.hasSolution(limit: options.maxBound ?? Int.max) {
            if !synthesize {
                player == .system ? print("result: realizable") : print("result: unrealizable")
                return
            }
            guard let solution = search.getSolution() else {
                Logger.default().error("could not construct solution")
                return
            }
            switch options.target {
            case .aiger:
                guard let aiger_solution = (solution as? AigerRepresentable)?.aiger else {
                    Logger.default().error("could not encode solution as AIGER")
                    return
                }
                let minimized = minimizeWithABC(aiger_solution)
                aiger_write_to_file(minimized, aiger_ascii_mode, stdout)
                player == .system ? print("result: realizable") : print("result: unrealizable")
            case .dot:
                guard let dot = (solution as? DotRepresentable)?.dot else {
                    Logger.default().error("could not encode solution as dot")
                    return
                }
                print(dot)
            case .smv:
                guard let smv = (solution as? SmvRepresentable)?.smv else {
                    Logger.default().error("could not encode solution as SMV")
                    return
                }
                print(smv)
            }

            return
        }
        print("unknown")
    }
}

//search(strategy: .Linear, player: .system, synthesize: synthesize)()

let condition = NSCondition()
var finished = false


let searchSystem = search(strategy: options.searchStrategy, player: .system, synthesize: options.synthesize)
let searchEnvironment = search(strategy: options.searchStrategy, player: .environment, synthesize: options.synthesize)

let doSearchSystem = options.player.contains(.system)
let doSearchEnvironment = options.player.contains(.environment)

#if os(Linux)
let thread1 = Thread() {
    searchSystem()
    condition.lock()
    finished = true
    condition.broadcast()
    condition.unlock()
}
let thread2 = Thread() {
    searchEnvironment()
    condition.lock()
    finished = true
    condition.broadcast()
    condition.unlock()
}
if doSearchSystem {
    thread1.start()
}
if doSearchEnvironment {
    thread2.start()
}
#else
    class ThreadedExecution: Thread {
        
        let function: () -> ()
        
        init(function: @escaping (() -> ())) {
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
if doSearchSystem {
    ThreadedExecution(function: searchSystem).start()
}
if doSearchEnvironment {
    ThreadedExecution(function: searchEnvironment).start()
}
#endif

condition.lock()
if !finished {
    condition.wait()
}
condition.unlock()

if let statistics = options.statistics {
    print(statistics.description)
}


