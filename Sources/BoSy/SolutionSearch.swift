import Foundation

import Utils
import CAiger

enum SearchStrategy {
    case Linear
    case Exponential
    
    func next(bound: Int) -> Int {
        switch self {
            case .Linear: return bound + 1
            case .Exponential: return bound * 2
        }
    }
}

enum Player {
    case System
    case Environment
}

enum Backends {
    case Explicit
    case InputSymbolic
    case StateSymbolic
    case Symbolic
    case Smt
    
    static func fromString(_ string: String) -> Backends? {
        switch (string) {
            case "explicit":
                return .Explicit
            case "input-symbolic":
                return .InputSymbolic
            case "state-symbolic":
                return .StateSymbolic
            case "symbolic":
                return .Symbolic
            case "smt":
                return .Smt
            default:
                return nil
        }
    }
}

struct SolutionSearch {
    let specification: InputFileFormat
    let automaton: CoBüchiAutomaton
    let searchStrategy: SearchStrategy
    let player: Player
    var bound: Int
    var encoding: BoSyEncoding
    let inputs: [String]
    let outputs: [String]
    
    init(specification: InputFileFormat, automaton: CoBüchiAutomaton, searchStrategy: SearchStrategy = .Exponential, player: Player = .System, backend: Backends = .InputSymbolic, initialBound bound: Int = 1, synthesize: Bool = true) {
        self.specification = specification
        self.automaton = automaton
        self.searchStrategy = searchStrategy
        self.player = player
        self.bound = bound
        
        let semantics: TransitionSystemType
        switch player {
        case .System:
            semantics = specification.semantics
            inputs = specification.inputs
            outputs = specification.outputs
        case .Environment:
            semantics = specification.semantics.swap()
            inputs = specification.outputs
            outputs = specification.inputs
        }
        
        switch backend {
        case .Explicit:
            encoding = ExplicitEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs)
        case .InputSymbolic:
            encoding = InputSymbolicEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs, synthesize: synthesize)
        case .StateSymbolic:
            encoding = StateSymbolicEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs)
        case .Symbolic:
            encoding = SymbolicEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs)
        case .Smt:
            encoding = SmtEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs)
        }
    }
    
    mutating func hasSolution(limit: Int = Int.max) -> Bool {
        while bound < limit {
            do {
                if try encoding.solve(forBound: bound) {
                    Logger.default().info("found solution with \(bound) states")
                    return true
                }
            } catch BoSyEncodingError.EncodingFailed(let message) {
                Logger.default().error(message)
                return false
            } catch BoSyEncodingError.SolvingFailed(let message) {
                Logger.default().error(message)
                return false
            } catch {
                Logger.default().error("Unknown error while building/solving")
                return false
            }
            
            bound = searchStrategy.next(bound: bound)
        }
        return false
    }
    
    func getSolution() -> BoSySolution? {
        return encoding.extractSolution()
    }
}
