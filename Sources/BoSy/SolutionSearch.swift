import Foundation

import Utils
import CAiger

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
    let specification: InputFileFormat
    let automaton: CoBüchiAutomaton
    let searchStrategy: SearchStrategy
    let player: Player
    var bound: Int
    var encoding: BoSyEncoding
    let inputs: [String]
    let outputs: [String]
    
    init(specification: InputFileFormat, automaton: CoBüchiAutomaton, searchStrategy: SearchStrategy = .exponential, player: Player = .system, backend: Backends = .inputSymbolic, initialBound bound: Int = 1, synthesize: Bool = true) {
        self.specification = specification
        self.automaton = automaton
        self.searchStrategy = searchStrategy
        self.player = player
        self.bound = bound
        
        let semantics: TransitionSystemType
        switch player {
        case .system:
            semantics = specification.semantics
            inputs = specification.inputs
            outputs = specification.outputs
        case .environment:
            semantics = specification.semantics.swap()
            inputs = specification.outputs
            outputs = specification.inputs
        }
        
        switch backend {
        case .explicit:
            encoding = ExplicitEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs)
        case .inputSymbolic:
            encoding = InputSymbolicEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs, synthesize: synthesize)
        case .stateSymbolic:
            encoding = StateSymbolicEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs)
        case .symbolic:
            encoding = SymbolicEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs)
        case .smt:
            encoding = SmtEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs)
        }
    }
    
    mutating func hasSolution(limit: Int = Int.max) -> Bool {
        while bound <= limit {
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
