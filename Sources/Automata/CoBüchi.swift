import Logic
import LTL
import Utils

public class CoBüchiAutomaton: Automaton, SafetyAcceptance, CoBüchiAcceptance {
    public typealias State = String

    public var initialStates: Set<State>
    public var states: Set<State>
    public var transitions: [State: [State: Logic]]
    public var safetyConditions: [State: Logic]
    public var rejectingStates: Set<State>

    // SCC optimizations
    var scc: [State: Int] = [:]
    var inRejectingScc: [State: Bool] = [:]

    public init(initialStates: Set<State>, states: Set<State>, transitions: [State: [State: Logic]], safetyConditions: [State: Logic], rejectingStates: Set<State>) {
        self.initialStates = initialStates
        self.states = states
        self.transitions = transitions
        self.safetyConditions = safetyConditions
        self.rejectingStates = rejectingStates
    }

    public init(automata: [CoBüchiAutomaton]) {
        /// makes sure every state is unique
        func transform(state: State, index: Int) -> State {
            "s\(index)_\(state)"
        }
        initialStates = Set<State>()
        states = Set<State>()
        transitions = [:]
        safetyConditions = [:]
        rejectingStates = Set<State>()

        for (i, automaton) in automata.enumerated() {
            initialStates.formUnion(automaton.initialStates.map { transform(state: $0, index: i) })
            states.formUnion(automaton.states.map { transform(state: $0, index: i) })
            for (source, outgoing) in automaton.transitions {
                var newOutgoing: [State: Logic] = [:]
                for (target, guardCondition) in outgoing {
                    newOutgoing[transform(state: target, index: i)] = guardCondition
                }
                transitions[transform(state: source, index: i)] = newOutgoing
            }
            for (source, safetyCondition) in automaton.safetyConditions {
                safetyConditions[transform(state: source, index: i)] = safetyCondition
            }
            rejectingStates.formUnion(automaton.rejectingStates.map { transform(state: $0, index: i) })
        }
    }

    // MARK: - SCC optimization

    public func calculateSCC() {
        for (i, scc) in trajan(graph: self).enumerated() {
            let isRejecting = !rejectingStates.intersection(scc).isEmpty
            for node in scc {
                self.scc[node] = i
                inRejectingScc[node] = isRejecting
            }
        }
    }

    public func isStateInNonRejectingSCC(_ state: State) -> Bool {
        guard let inRejecting = inRejectingScc[state] else {
            return false
        }
        return !inRejecting
    }

    public func isInSameSCC(_ state1: State, _ state2: State) -> Bool {
        guard let sccState1 = scc[state1] else {
            return true
        }
        guard let sccState2 = scc[state2] else {
            return true
        }
        return sccState1 == sccState2
    }

    // MARK: - Safety reduction

    public struct CounterState: Hashable, CustomStringConvertible {
        let state: State
        let counter: Int

        public static func == (lhs: CounterState, rhs: CounterState) -> Bool {
            lhs.state == rhs.state && lhs.counter == rhs.counter
        }

        public func hash(into hasher: inout Hasher) {
            hasher.combine(state)
            hasher.combine(counter)
        }

        public var description: String {
            "[\(state),\(counter)]"
        }
    }

    public func reduceToSafety(bound k: Int) -> SafetyAutomaton<CounterState> {
        var queue: [CounterState] = self.initialStates.map { CounterState(state: $0, counter: 0) }
        let initialStates = Set<CounterState>(queue)

        var transitions: [CounterState: [CounterState: Logic]] = [:]
        var safetyConditions: [CounterState: Logic] = [:]

        var processed = Set<CounterState>()
        while let state = queue.popLast() {
            guard !processed.contains(state) else {
                // already processed
                continue
            }

            if let localSafetyCondition = self.safetyConditions[state.state] {
                assert(safetyConditions[state] == nil)
                safetyConditions[state] = localSafetyCondition
            }

            guard let outgoing = self.transitions[state.state] else {
                fatalError()
            }
            for (target, transitionGuard) in outgoing {
                let next: CounterState
                if isStateInNonRejectingSCC(state.state) || isStateInNonRejectingSCC(target) || !isInSameSCC(state.state, target) {
                    // can reset the counter
                    next = CounterState(state: target, counter: 0)
                } else {
                    next = CounterState(state: target, counter: rejectingStates.contains(target) ? state.counter + 1 : state.counter)
                }
                if next.counter > k {
                    assert(next.counter == k + 1)
                    // rejecting counter overflow => safety condition violation
                    var localSafetyCondition = safetyConditions[state] ?? Literal.True
                    localSafetyCondition = localSafetyCondition & !transitionGuard
                    safetyConditions[state] = localSafetyCondition
                } else {
                    queue.append(next)

                    // add transition in safety automaton
                    var stateTransition = transitions[state] ?? [:]
                    assert(stateTransition[next] == nil)
                    stateTransition[next] = transitionGuard
                    transitions[state] = stateTransition
                }
            }
            processed.insert(state)
        }

        return SafetyAutomaton(initialStates: initialStates, states: processed, transitions: transitions, safetyConditions: safetyConditions)
    }

    // MARK: - LTL conversion

    public static func from(ltl: LTL, using converter: LTL2AutomatonConverter = .spot) throws -> CoBüchiAutomaton {
        try converter.convert(ltl: ltl)
    }
}
