import Foundation

import Utils

struct CoBüchiAutomaton: GraphRepresentable {
    typealias State = String
    var initialStates: Set<State>
    var states: Set<State>
    var transitions: [State : [State : Logic]]
    var safetyConditions: [State : Logic]
    var rejectingStates: Set<State>
    
    // SCC optimizations
    var scc: [State: Int] = [:]
    var inRejectingScc: [State: Bool] = [:]
    
    // conformance with GraphRepresentable
    var edges: [State: [State]] {
        var e: [State: [State]] = [:]
        for (source, outgoing) in transitions {
            e[source] = []
            for (target, condition) in outgoing {
                if condition as? Literal != nil && condition as! Literal == Literal.False {
                    continue
                }
                e[source]?.append(target)
            }
        }
        return e
    }
    
    init(initialStates: Set<State>, states: Set<State>, transitions: [State : [State : Logic]], safetyConditions: [State : Logic], rejectingStates: Set<State>) {
        self.initialStates = initialStates
        self.states = states
        self.transitions = transitions
        self.safetyConditions = safetyConditions
        self.rejectingStates = rejectingStates
    }
    
    /**
     * Remove rejecting sink states
     */
    mutating func simplify() {
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
            
            //print("rejecting sink")
            
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
                
                var newOutgoing: [State : Logic] = [:]
                for (target, outgoingGuard) in outgoing {
                    newOutgoing[target] = outgoingGuard | guardExpression
                    // TODO: check if condition becomes valid
                }
                transitions[source] = newOutgoing
            }
        }
    }
    
    func isSafety() -> Bool {
        return rejectingStates.isEmpty
    }
    
    mutating func claculateSCC() {
        for (i, scc) in trajan(graph: self).enumerated() {
            let isRejecting = !rejectingStates.intersection(scc).isEmpty
            for node in scc {
                self.scc[node] = i
                self.inRejectingScc[node] = isRejecting
            }
        }
    }
    
    func isStateInNonRejectingSCC(_ state: State) -> Bool {
        guard let inRejecting = inRejectingScc[state] else {
            return false
        }
        return !inRejecting
    }

    func isInSameSCC(_ state1: State, _ state2: State) -> Bool {
        guard let sccState1 = scc[state1] else {
            return true
        }
        guard let sccState2 = scc[state2] else {
            return true
        }
        return sccState1 == sccState2
    }
}

func ltl3ba(ltl: String) -> CoBüchiAutomaton? {
    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif

    task.launchPath = "./ltl3ba"
    task.arguments = ["-f", "\"(\(ltl))\""] // read from stdin
    
    //let stdinPipe = NSPipe()
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    //task.standardInput = stdinPipe
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    /*let stdinHandle = stdinPipe.fileHandleForWriting
    if let data = ltl.data(using: NSUTF8StringEncoding) {
        #if os(Linux)
        stdinHandle.writeData(data)
        #else
        stdinHandle.write(data)
        #endif
        stdinHandle.closeFile()
    }*/
    
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let outputData = StreamHelper.readAllAvailableData(from: stdoutHandle)
    
    task.waitUntilExit()
    //let stdoutData = stdoutPipe.fileHandleForReading.readDataToEndOfFile()
    guard let neverClaim = String(data: outputData, encoding: String.Encoding.utf8) else {
        return nil
    }
    return parseSpinNeverClaim(neverClaim: neverClaim)
}

func spot(ltl: String) -> CoBüchiAutomaton? {
    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif

    task.launchPath = "./ltl2tgba"
    task.arguments = ["--spin", "--low", "-F", "-"] // read from stdin
    
    let stdinPipe = Pipe()
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    task.standardInput = stdinPipe
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    let stdinHandle = stdinPipe.fileHandleForWriting
    if let data = ltl.data(using: String.Encoding.utf8) {
        stdinHandle.write(data)
        stdinHandle.closeFile()
    }
    
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let outputData = StreamHelper.readAllAvailableData(from: stdoutHandle)
    
    task.waitUntilExit()
    //let stdoutData = stdoutPipe.fileHandleForReading.readDataToEndOfFile()
    guard let neverClaim = String(data: outputData, encoding: String.Encoding.utf8) else {
        return nil
    }
    return parseSpinNeverClaim(neverClaim: neverClaim)
}

func parseSpinNeverClaim(neverClaim: String) -> CoBüchiAutomaton? {
    var states: Set<String> = Set()
    var rejectingStates: Set<String> = Set()
    var initialState: String? = nil
    var transitions: [String : [String: Logic]] = [:]
    
    var lastState: String? = nil
    
    //print(neverClaim)
    
    func normalizeStateName(_ name: String) -> String {
        return name.replacingOccurrences(of: "_init", with: "").replacingOccurrences(of: "accept_", with: "")
    }
    
    //print("parse never claim")
    for var line in neverClaim.components(separatedBy: "\n") {
        line = line.trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines)
        if line.hasPrefix("never") || line.hasPrefix("}") || line.hasPrefix("if") || line.hasPrefix("fi") {
            continue
        } else if line.hasSuffix(":") {
            // state
            let origName = line[line.startIndex..<line.index(before: line.endIndex)]
            let name = normalizeStateName(origName)
            transitions[name] = [:]
            lastState = name
            if origName.hasPrefix("accept_") {
                rejectingStates.insert(name)
            }
            if origName.hasSuffix("_init") {
                assert(initialState == nil)
                initialState = name
            }
            states.insert(name)
        } else if line.hasPrefix("::") {
            // transition
            line = line.replacingOccurrences(of: ":: ", with: "")
            let components = line.components(separatedBy: " -> goto ")
            assert(components.count == 2)
            guard let guardStatement = BooleanUtils.parse(string: components[0]) else {
                Logger.default().error("could not parse guard expression")
                exit(1)
            }
            let target = normalizeStateName(components[1])
            guard let source = lastState else {
                exit(1)
            }
            transitions[source]?[target] = guardStatement
        } else if line.contains("skip") {
            guard let source = lastState else {
                exit(1)
            }
            transitions[source]?[source] = Literal.True
        }
    }
    assert(initialState != nil)
    var automaton =  CoBüchiAutomaton(initialStates: [initialState!],
                            states: states,
                            transitions: transitions,
                            safetyConditions: [:],
                            rejectingStates: rejectingStates)
    automaton.simplify()
    automaton.claculateSCC()
    return automaton
}
