import Foundation

import Utils
import CAiger
import Logic
import Automata

enum SearchStrategy: String {
    case linear      = "linear"
    case exponential = "exponential"
    
    func next(bound: Int) -> Int {
        switch self {
            case .linear: return bound + 1
            case .exponential: return bound * 2
        }
    }
    
    static let allValues: [SearchStrategy] = [.linear, .exponential]
}

enum Player: Int {
    case system      = 0b01
    case environment = 0b10
}

struct Players: OptionSet {
    let rawValue: Int
    
    public init(rawValue: Int) {
        self.rawValue = rawValue
    }
    init(player: Player) {
        rawValue = player.rawValue
    }
    
    static let system        = Players(player: .system)
    static let environment   = Players(player: .environment)
    static let both: Players = [.system, .environment]
}

enum Backends: String {
    case explicit      = "explicit"
    case inputSymbolic = "input-symbolic"
    case stateSymbolic = "state-symbolic"
    case symbolic      = "symbolic"
    case smt           = "smt"
    
    static let allValues: [Backends] = [
        .explicit,
        .inputSymbolic,
        .stateSymbolic,
        .symbolic,
        .smt
    ]
    
    func supports(solver: SolverInstance) -> Bool {
        switch self {
        case .explicit:
            return (solver.instance as? SatSolver) != nil
        case .inputSymbolic:
            return (solver.instance as? QbfSolver) != nil
        case .stateSymbolic:
            return (solver.instance as? DqbfSolver) != nil
        case .symbolic:
            return (solver.instance as? DqbfSolver) != nil
        case .smt:
            return (solver.instance as? SmtSolver) != nil
        }
    }
    
    var defaultSolver: SolverInstance {
        switch self {
        case .explicit:
            return .cryptominisat
        case .inputSymbolic:
            return .rareqs
        case .stateSymbolic:
            return .idq
        case .symbolic:
            return .idq
        case .smt:
            return .z3
        }
    }
}

struct SolutionSearch {
    var specification: BoSySpecification
    let automaton: CoBüchiAutomaton
    let searchStrategy: SearchStrategy
    let player: Player
    var bound: Int
    var encoding: BoSyEncoding
    
    init(specification spec: BoSySpecification, automaton: CoBüchiAutomaton, searchStrategy: SearchStrategy = .exponential, player: Player = .system, backend: Backends = .inputSymbolic, initialBound bound: Int = 1, synthesize: Bool = true) {
        self.specification = player == .system ? spec : spec.dualized
        self.automaton = automaton
        self.searchStrategy = searchStrategy
        self.player = player
        self.bound = bound
        
        switch backend {
        case .explicit:
            encoding = ExplicitEncoding(automaton: automaton, specification: specification)
        case .inputSymbolic:
            encoding = InputSymbolicEncoding(automaton: automaton, specification: specification, synthesize: synthesize)
        case .stateSymbolic:
            encoding = StateSymbolicEncoding(automaton: automaton, specification: specification)
        case .symbolic:
            encoding = SymbolicEncoding(automaton: automaton, specification: specification)
        case .smt:
            encoding = SmtEncoding(automaton: automaton, specification: specification)
        }
    }
    
    mutating func hasSolution(limit: Int = Int.max) -> Bool {
        while bound <= limit {
            Logger.default().debug("search for solution of bound \(bound) (player: \"\(player)\")")
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
