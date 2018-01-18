import Logic

public class SafetyAutomaton<S: Hashable & CustomStringConvertible>: Automaton, SafetyAcceptance {
    public typealias State = S

    public var initialStates: Set<State>
    public var states: Set<State>
    public var transitions: [State : [State : Logic]]
    public var safetyConditions: [State : Logic]

    public init(initialStates: Set<State>, states: Set<State>, transitions: [State : [State : Logic]], safetyConditions: [State : Logic]) {
        self.initialStates = initialStates
        self.states = states
        self.transitions = transitions
        self.safetyConditions = safetyConditions
    }

}
