import Foundation
import TSCBasic
import TSCUtility

import Logic
import Utils

public protocol Automaton: GraphRepresentable where State: CustomStringConvertible {
    var initialStates: Set<State> { get set }
    var states: Set<State> { get set }
    var transitions: [State: [State: Logic]] { get set }
}

extension Automaton {
    // default implementation for GraphRepresentable
    public var edges: [State: [State]] {
        var e: [State: [State]] = [:]
        for (source, outgoing) in transitions {
            e[source] = []
            for (target, condition) in outgoing {
                if condition as? Literal != nil, condition as! Literal == Literal.False {
                    continue
                }
                e[source]?.append(target)
            }
        }
        return e
    }
}

public protocol SafetyAcceptance {
    associatedtype State: Hashable
    var safetyConditions: [State: Logic] { get set }
}

public protocol CoBüchiAcceptance {
    associatedtype State: Hashable
    var rejectingStates: Set<State> { get set }
}

extension Automaton where Self: CoBüchiAcceptance & SafetyAcceptance {
    /**
     * Transforms rejecting sink states to safety conditions
     */
    public mutating func removeRejectingSinks() {
        for state in rejectingStates {
            guard let outgoing = transitions[state] else {
                assert(false)
                continue
            }
            if outgoing.count != 1 {
                continue
            }
            guard let guardStatement = outgoing[state] else {
                continue
            }
            guard let literal = guardStatement as? Literal else {
                continue
            }
            if literal != Literal.True {
                continue
            }
            if state.description == "init" {
                safetyConditions[state] = Literal.False
                continue
            }
            // print("rejecting sink")

            rejectingStates.remove(state)
            states.remove(state)
            transitions.removeValue(forKey: state)
            for (source, var outgoing) in transitions {
                guard let guardExpression = outgoing.removeValue(forKey: state) else {
                    continue
                }
                // there is a transition into rejecting sink
                // => transform to safety condition on state
                var condition = safetyConditions[source] ?? Literal.True
                condition = condition & !guardExpression
                safetyConditions[source] = condition

                transitions[source] = outgoing
            }
        }
    }
}
