import SafetyGameSolver
import CUDD
import Utils
import Automata
import Logic
import TransitionSystem
import Specification


class UCWGame: SafetyGame {
    var manager: CUDDManager
    
    var controllables: [CUDDNode]
    var uncontrollables: [CUDDNode]
    var latches: [CUDDNode]
    
    var compose: [CUDDNode]
    var initial: CUDDNode
    var safetyCondition: CUDDNode
    
    var controllableNames: [String]
    var uncontrollableNames: [String]
    var latchNames: [String]
    
    init(manager: CUDDManager, automaton: CoBüchiAutomaton, inputs: [String], outputs: [String], bound k: Int) {
        self.manager = manager

        let safetyAutomaton = automaton.reduceToSafety(bound: k)
        let safetyAutomatonStates = safetyAutomaton.states.map({ $0 })
        
        self.controllables = outputs.map({ _ in manager.newVar() });
        self.uncontrollables = inputs.map({ _ in manager.newVar() });
        self.latches = safetyAutomatonStates.map({ _ in manager.newVar() })
        
        self.compose = self.controllables + self.uncontrollables + (0..<self.latches.count).map({ _ in manager.zero() })
        self.initial = latches.reduce(manager.one(), { states, state in states & !state })
        self.safetyCondition = manager.one()

        let composeOffset = controllables.count + uncontrollables.count
        
        self.controllableNames = outputs
        self.uncontrollableNames = inputs
        self.latchNames = safetyAutomatonStates.map({ $0.description })

        assert(compose.count == controllables.count + uncontrollables.count + latches.count)

        // build lookup table for propositions
        var lookupTable: [String:CUDDNode] = [:]
        for (proposition, node) in zip(inputs, uncontrollables) {
            lookupTable[proposition] = node
        }
        for (proposition, node) in zip(outputs, controllables) {
            lookupTable[proposition] = node
        }
        let cuddEncoder = CUDDVisitor(manager: manager, lookupTable: lookupTable)

        for (state, encoded) in zip(safetyAutomatonStates, latches) {
            if let localSafetyCondition = safetyAutomaton.safetyConditions[state] {
                self.safetyCondition &= !(encoded & !localSafetyCondition.accept(visitor: cuddEncoder))
                //print("\(state): \(localSafetyCondition)")
            }

            if let outgoing = safetyAutomaton.transitions[state] {
                for (target, transitionGuard) in outgoing {
                    let index = safetyAutomatonStates.index(of: target)!
                    compose[composeOffset + index] |= encoded & transitionGuard.accept(visitor: cuddEncoder)
                    //print("\(state) -\(transitionGuard)-> \(target)")
                }
            } else {
                assert(safetyAutomaton.safetyConditions[state] != nil)
            }
        }
        
        /*for initialState in automaton.initialStates {
            let state = SafetyState(state: initialState, counter: 0)
            let index = getStateIndex(state: state)
            let latch = latches[index]
            var others: [CUDDNode] = []
            for (i, element) in latches.enumerated() {
                if i != index {
                    others.append(!element)
                }
            }
            initial &= ([latch] + others).reduce(manager.one(), &)
        }*/

        // simulate fake initial state in safety game
        for initialState in safetyAutomaton.initialStates {
            if let localSafetyCondition = safetyAutomaton.safetyConditions[initialState] {
                self.safetyCondition &= !(initial & !localSafetyCondition.accept(visitor: cuddEncoder))
                //print("initial: \(localSafetyCondition)")
            }

            guard let outgoing = safetyAutomaton.transitions[initialState] else {
                fatalError()
            }
            for (target, transitionGuard) in outgoing {
                let index = safetyAutomatonStates.index(of: target)!
                compose[composeOffset + index] |= initial & transitionGuard.accept(visitor: cuddEncoder)
                //print("initial -\(transitionGuard)-> \(target)")
            }
        }

    }
    
    /**
     * Given the winning strategies of the outputs, the function derives
     * the winning strategy for the synthesis problem.
     */
    func getImplementation(strategies: [CUDDNode], semantics: TransitionSystemType) -> SymbolicStateSolution {
        
        // need to get rid of the outputs in the transition functions
        let composeOutputs = strategies + uncontrollables + latches
        assert(composeOutputs.count == compose.count)
        let latchFunctions: [CUDDNode] = Array(compose.suffix(latches.count)).map({ $0.compose(vector: composeOutputs) })
        
        let solution = SymbolicStateSolution(manager: manager, inputs: uncontrollableNames, outputs: controllableNames, semantics: semantics, latches: latches, inputNodes: uncontrollables, outputFunctions: strategies, latchFunctions: latchFunctions)
        return solution
    }
}

class SafetyGameReduction: BoSyEncoding {
    
    let options: BoSyOptions
    let automaton: CoBüchiAutomaton
    let specification: SynthesisSpecification
    
    var safetyGame: UCWGame? = nil
    var solver: SafetyGameSolver? = nil
    var winningRegion: CUDDNode? = nil
    
    init(options: BoSyOptions, automaton: CoBüchiAutomaton, specification: SynthesisSpecification) {
        self.options = options
        self.automaton = automaton
        self.specification = specification
    }
    
    func solve(forBound bound: Int) throws -> Bool {
        Logger.default().debug("build safety game with k=\(bound)")
        
        let manager = CUDDManager()
        manager.AutodynEnable(reorderingAlgorithm: .GroupSift)
        
        let safetyGame = UCWGame(manager: manager, automaton: automaton, inputs: specification.inputs, outputs: specification.outputs, bound: bound)
        
        let solver = SafetyGameSolver(instance: safetyGame, mealy: specification.semantics == .mealy)
        if let winningRegion = solver.solve() {
            self.solver = solver
            self.winningRegion = winningRegion
            self.safetyGame = safetyGame
            return true
        } else {
            return false
        }
    }
    
    func extractSolution() -> TransitionSystem? {
        guard let solver = solver else {
            fatalError()
        }
        guard let winningRegion = winningRegion else {
            fatalError()
        }
        guard let game = self.safetyGame else {
            fatalError()
        }
        let strategies = solver.getStrategiesFrom(winningRegion: winningRegion)
        assert(strategies.count == specification.outputs.count)
        
        
        let solution = game.getImplementation(strategies: strategies, semantics: specification.semantics)
        
        return solution
    }
    
}

