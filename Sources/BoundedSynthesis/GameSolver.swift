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
    
    struct SafetyState: Hashable, CustomStringConvertible {
        let state: CoBüchiAutomaton.State
        let counter: Int
        
        static func ==(lhs: UCWGame.SafetyState, rhs: UCWGame.SafetyState) -> Bool {
            return lhs.state == rhs.state && lhs.counter == rhs.counter
        }
        
        var hashValue: Int {
            return state.hashValue ^ counter.hashValue
        }
        
        var description: String {
            return "[\(state),\(counter)]"
        }
        
    }
    
    init(manager: CUDDManager, automaton: CoBüchiAutomaton, inputs: [String], outputs: [String], bound k: Int) {
        self.manager = manager
        
        self.controllables = outputs.map({ _ in manager.newVar() });
        self.uncontrollables = inputs.map({ _ in manager.newVar() });
        self.latches = []
        
        self.compose = self.controllables + self.uncontrollables
        self.initial = manager.one()
        self.safetyCondition = manager.one()
        
        self.controllableNames = outputs
        self.uncontrollableNames = inputs
        self.latchNames = []
        
        var queue: [SafetyState] = automaton.initialStates.map({ SafetyState(state: $0, counter: 0) })
        
        var latchMapping: [SafetyState : Int] = [:]
        
        func getStateIndex(state: SafetyState) -> Int {
            if let index = latchMapping[state] {
                return index
            } else {
                // create new variable if not exists
                let encoded = manager.newVar()
                let index = latches.count
                latchMapping[state] = index
                latches.append(encoded)
                compose.append(manager.zero())
                latchNames.append(state.state)
                return index
            }
        }
        
        let offset = controllables.count + uncontrollables.count
        
        var lookupTable: [String:CUDDNode] = [:]
        for (proposition, node) in zip(inputs, uncontrollables) {
            lookupTable[proposition] = node
        }
        for (proposition, node) in zip(outputs, controllables) {
            lookupTable[proposition] = node
        }
        let cuddEncoder = CUDDVisitor(manager: manager, lookupTable: lookupTable)
        
        var processed = Set<SafetyState>()
        while let state = queue.popLast() {
            guard !processed.contains(state) else {
                // already processed
                continue
            }
            let index = getStateIndex(state: state)
            let encoded: CUDDNode = latches[index]
            
            guard let outgoing = automaton.transitions[state.state] else {
                fatalError()
            }
            for (target, transitionGuard) in outgoing {
                let next: SafetyState
                if automaton.isStateInNonRejectingSCC(state.state) || automaton.isStateInNonRejectingSCC(target) || !automaton.isInSameSCC(state.state, target) {
                    // can reset the counter
                    next = SafetyState(state: target, counter: 0)
                } else {
                    next = SafetyState(state: target, counter: automaton.rejectingStates.contains(target) ? state.counter + 1 : state.counter)
                }
                let nextStateIndex = getStateIndex(state: next)
                if next.counter > k {
                    // rejecting counter overflow => safety condition violation
                    safetyCondition &= !(encoded & transitionGuard.accept(visitor: cuddEncoder))
                    //print("\(state) --(\(transitionGuard))--> bad")
                } else {
                    compose[offset + nextStateIndex] |= encoded & transitionGuard.accept(visitor: cuddEncoder)
                    queue.append(next)
                    //print("\(state) --(\(transitionGuard))--> \(next)")
                }
            }
            if let stateSafetyCondition = automaton.safetyConditions[state.state] {
                safetyCondition &= !(encoded & !stateSafetyCondition.accept(visitor: cuddEncoder))
                //print("\(state) --(\(!safetyCondition))--> bad")
            }
            processed.insert(state)
        }
        
        assert(compose.count == controllables.count + uncontrollables.count + latches.count)
        
        for initialState in automaton.initialStates {
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
        }
    }
    
    /**
     * Given the winning strategies of the outputs, the function derives
     * the winning strategy for the synthesis problem.
     */
    func getImplementation(strategies: [CUDDNode], semantics: TransitionSystemType) -> SymbolicStateSolution {
        
        // need to get rid of the outputs in the transition functions
        let composeOutputs = uncontrollables + strategies + latches
        assert(composeOutputs.count == compose.count)
        let latchFunctions: [CUDDNode] = Array(compose.suffix(latches.count)).map({ $0.compose(vector: composeOutputs) })
        
        let solution = SymbolicStateSolution(manager: manager, inputs: uncontrollableNames, outputs: controllableNames, semantics: semantics, latches: latches, inputNodes: uncontrollables, outputFunctions: strategies, latchFunctions: latchFunctions)
        return solution
    }
}

class SafetyGameReduction: BoSyEncoding {
    
    let automaton: CoBüchiAutomaton
    let semantics: TransitionSystemType
    let inputs: [String]
    let outputs: [String]
    
    var safetyGame: UCWGame? = nil
    var solver: SafetyGameSolver? = nil
    var winningRegion: CUDDNode? = nil
    
    init(automaton: CoBüchiAutomaton, semantics: TransitionSystemType, inputs: [String], outputs: [String]) {
        self.automaton = automaton
        self.semantics = semantics
        self.inputs = inputs
        self.outputs = outputs
    }
    
    func solve(forBound bound: Int) throws -> Bool {
        Logger.default().debug("build safety game with k=\(bound)")
        
        let manager = CUDDManager()
        manager.AutodynEnable(reorderingAlgorithm: .GroupSift)
        
        let safetyGame = UCWGame(manager: manager, automaton: automaton, inputs: inputs, outputs: outputs, bound: bound)
        
        let solver = SafetyGameSolver(instance: safetyGame, mealy: semantics == .mealy)
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
        assert(strategies.count == outputs.count)
        
        
        let solution = game.getImplementation(strategies: strategies, semantics: semantics)
        
        return solution
    }
    
}

class CUDDVisitor: ReturnConstantVisitor<CUDDNode> {
    
    let manager: CUDDManager
    
    // lookup propositions
    let lookupTable: [String:CUDDNode]
    
    init(manager: CUDDManager, lookupTable: [String:CUDDNode]) {
        self.manager = manager
        self.lookupTable = lookupTable
        super.init(constant: manager.zero())
    }
    
    override func visit(literal: Literal) -> CUDDNode {
        if literal == .False {
            return manager.zero()
        } else {
            return manager.one()
        }
    }
    
    override func visit(proposition: Proposition) -> CUDDNode {
        guard let node = lookupTable[proposition.name] else {
            fatalError()
        }
        return node
    }
    
    override func visit(unaryOperator: UnaryOperator) -> CUDDNode {
        assert(unaryOperator.type == .Negation)
        return !unaryOperator.operand.accept(visitor: self)
    }
    
    override func visit(binaryOperator: BinaryOperator) -> CUDDNode {
        let application = binaryOperator.operands.map({ $0.accept(visitor: self) })
        switch binaryOperator.type {
        case .And:
            return application.reduce(manager.one(), &)
        case .Or:
            return application.reduce(manager.zero(), |)
        case .Xnor:
            return application[0] <-> application[1]
        case .Xor:
            return application[0] ^ application[1]
        }
    }
}
