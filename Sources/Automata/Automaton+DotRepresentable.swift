import Logic

extension CoBüchiAutomaton {
    public var dot: String {
        var dot: [String] = []

        // initial state
        for state in initialStates {
            dot += ["\t_init [style=\"invis\"];", "\t_init -> \"s\(state)\"[label=\"\"];"]
        }

        for state in states {
            dot.append("\t\"s\(state)\"[shape=rectangle,label=\"\(state)\"];")
        }

        for state in rejectingStates {
            dot.append("\t\"s\(state)\"[shape=rectangle,label=\"rejecting:\(state)\"];")
        }

        for (source, outgoing) in transitions {
            for (target, transitionGuard) in outgoing {
                dot.append("\t\"s\(source)\" -> \"s\(target)\" [label=\"\(transitionGuard)\"];")
            }
        }

        if !safetyConditions.isEmpty {
            dot.append("\tbad[shape=rectangle,label=\"bad\"];")
            for (source, localSafetyCondition) in safetyConditions {
                dot.append("\t\"s\(source)\" -> bad [label=\"\(!localSafetyCondition)\"];")
            }
        }

        return "digraph graphname {\n\(dot.joined(separator: "\n"))\n}"
    }
}

extension SafetyAutomaton {
    public var dot: String {
        var dot: [String] = []

        // initial state
        for state in initialStates {
            dot += ["\t_init [style=\"invis\"];", "\t_init -> \"s\(state)\"[label=\"\"];"]
        }

        for state in states {
            dot.append("\t\"s\(state)\"[shape=rectangle,label=\"\(state)\"];")
        }

        for (source, outgoing) in transitions {
            for (target, transitionGuard) in outgoing {
                dot.append("\t\"s\(source)\" -> \"s\(target)\" [label=\"\(transitionGuard)\"];")
            }
        }

        if !safetyConditions.isEmpty {
            dot.append("\tbad[shape=rectangle,label=\"bad\"];")
            for (source, localSafetyCondition) in safetyConditions {
                dot.append("\t\"s\(source)\" -> bad [label=\"\(!localSafetyCondition)\"];")
            }
        }

        return "digraph graphname {\n\(dot.joined(separator: "\n"))\n}"
    }
}

