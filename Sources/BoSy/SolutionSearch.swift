import Foundation

import Utils
import CAiger

enum SearchStrategy {
    case Linear
    case Exponential
    
    func next(bound: Int) -> Int {
        switch self {
            case Linear: return bound + 1
            case Exponential: return bound * 2
        }
    }
}

enum Player {
    case System
    case Environment
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
    
    init(specification: InputFileFormat, automaton: CoBüchiAutomaton, searchStrategy: SearchStrategy = .Exponential, player: Player = .System, initialBound bound: Int = 1) {
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
        
        encoding = InputSymbolicEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs)
        //encoding = ExplicitEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs)
        //encoding = StateSymbolicEncoding(automaton: automaton, semantics: semantics, inputs: inputs, outputs: outputs)
    }
    
    mutating func hasSolution(limit: Int = Int.max) -> Bool {
        while bound < limit {
            do {
                if try encoding.solve(forBound: bound) {
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
