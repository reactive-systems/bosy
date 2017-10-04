import Foundation

import Logic
import Utils

public protocol Automaton: GraphRepresentable {
    var initialStates: Set<State> { get set }
    var states: Set<State> { get set }
    var transitions: [State : [State : Logic]] { get set }
}

extension Automaton {
    // default implementation for GraphRepresentable
    public var edges: [State: [State]] {
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
}

public protocol SafetyAcceptance {
    associatedtype State: Hashable
    var safetyConditions: [State : Logic] { get set }
}

public protocol CoBüchiAcceptance {
    associatedtype State: Hashable
    var rejectingStates: Set<State> { get set }
}

extension Automaton where Self: CoBüchiAcceptance & SafetyAcceptance {
    
    /**
     * Remove rejecting sink states
     */
    public mutating func simplify() {
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

                transitions[source] = outgoing
            }
        }
    }
}

public class SafetyAutomaton<S: Hashable>: Automaton, SafetyAcceptance {
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

public class CoBüchiAutomaton: Automaton, SafetyAcceptance, CoBüchiAcceptance {
    public typealias State = String

    public var initialStates: Set<State>
    public var states: Set<State>
    public var transitions: [State : [State : Logic]]
    public var safetyConditions: [State : Logic]
    public var rejectingStates: Set<State>
    
    // SCC optimizations
    var scc: [State: Int] = [:]
    var inRejectingScc: [State: Bool] = [:]
    
    public init(initialStates: Set<State>, states: Set<State>, transitions: [State : [State : Logic]], safetyConditions: [State : Logic], rejectingStates: Set<State>) {
        self.initialStates = initialStates
        self.states = states
        self.transitions = transitions
        self.safetyConditions = safetyConditions
        self.rejectingStates = rejectingStates
    }
    
    public init(automata: [CoBüchiAutomaton]) {
        /// makes sure every state is unique
        func transform(state: State, index: Int) -> State {
            return "s\(index)_\(state)"
        }
        self.initialStates = Set<State>()
        self.states = Set<State>()
        self.transitions = [:]
        self.safetyConditions = [:]
        self.rejectingStates = Set<State>()
        
        for (i, automaton) in automata.enumerated() {
            self.initialStates.formUnion(automaton.initialStates.map({ transform(state: $0, index: i) }))
            self.states.formUnion(automaton.states.map({ transform(state: $0, index: i) }))
            for (source, outgoing) in automaton.transitions {
                var newOutgoing: [State:Logic] = [:]
                for (target, guardCondition) in outgoing {
                    newOutgoing[transform(state: target, index: i)] = guardCondition
                }
                self.transitions[transform(state: source, index: i)] = newOutgoing
            }
            for (source, safetyCondition) in automaton.safetyConditions {
                self.safetyConditions[transform(state: source, index: i)] = safetyCondition
            }
            self.rejectingStates.formUnion(automaton.rejectingStates.map({ transform(state: $0, index: i) }))
        }
    }
    
    
    public func calculateSCC() {
        for (i, scc) in trajan(graph: self).enumerated() {
            let isRejecting = !rejectingStates.intersection(scc).isEmpty
            for node in scc {
                self.scc[node] = i
                self.inRejectingScc[node] = isRejecting
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


    public struct CounterState: Hashable, CustomStringConvertible {
        let state: State
        let counter: Int

        public static func ==(lhs: CounterState, rhs: CounterState) -> Bool {
            return lhs.state == rhs.state && lhs.counter == rhs.counter
        }

        public var hashValue: Int {
            return state.hashValue ^ counter.hashValue
        }

        public var description: String {
            return "[\(state),\(counter)]"
        }

    }

    public func reduceToSafety(bound k: Int) -> SafetyAutomaton<CounterState> {

        var queue: [CounterState] = self.initialStates.map({ CounterState(state: $0, counter: 0) })
        let initialStates = Set<CounterState>(queue)

        var transitions: [CounterState : [CounterState : Logic]] = [:]
        var safetyConditions: [CounterState : Logic] = [:]


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
                if self.isStateInNonRejectingSCC(state.state) || self.isStateInNonRejectingSCC(target) || !self.isInSameSCC(state.state, target) {
                    // can reset the counter
                    next = CounterState(state: target, counter: 0)
                } else {
                    next = CounterState(state: target, counter: self.rejectingStates.contains(target) ? state.counter + 1 : state.counter)
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
}

extension CoBüchiAutomaton {
    public var dot: String {
        var dot: [String] = []

        // initial state
        for state in initialStates {
            dot += ["\t_init [style=\"invis\"];", "\t_init -> s\(state)[label=\"\"];"]
        }

        for state in states {
            dot.append("\ts\(state)[shape=rectangle,label=\"\(state)\"];")
        }

        for state in rejectingStates {
            dot.append("\ts\(state)[shape=rectangle,label=\"rejecting:\(state)\"];")
        }

        for (source, outgoing) in transitions {
            for (target, transitionGuard) in outgoing {
                dot.append("\ts\(source) -> s\(target) [label=\"\(transitionGuard)\"];")
            }
        }

        if !safetyConditions.isEmpty {
            dot.append("\tbad[shape=rectangle,label=\"bad\"];")
            for (source, localSafetyCondition) in safetyConditions {
                dot.append("\ts\(source) -> bad [label=\"\(!localSafetyCondition)\"];")
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
            dot += ["\t_init [style=\"invis\"];", "\t_init -> s\(state.hashValue)[label=\"\"];"]
        }

        for state in states {
            dot.append("\ts\(state.hashValue)[shape=rectangle,label=\"\(state)\"];")
        }

        for (source, outgoing) in transitions {
            for (target, transitionGuard) in outgoing {
                dot.append("\ts\(source.hashValue) -> s\(target.hashValue) [label=\"\(transitionGuard)\"];")
            }
        }

        if !safetyConditions.isEmpty {
            dot.append("\tbad[shape=rectangle,label=\"bad\"];")
            for (source, localSafetyCondition) in safetyConditions {
                dot.append("\ts\(source.hashValue) -> bad [label=\"\(!localSafetyCondition)\"];")
            }
        }

        return "digraph graphname {\n\(dot.joined(separator: "\n"))\n}"
    }
}

public enum LTL2AutomatonConverter: String {
    case ltl3ba = "ltl3ba"
    case spot   = "spot"
    
    public func convert(ltl: String) -> CoBüchiAutomaton? {
        switch self {
        case .ltl3ba:
            return _ltl3ba(ltl: ltl)
        case .spot:
            return _spot(ltl: ltl)
        }
    }
    
    public static let allValues: [LTL2AutomatonConverter] = [.ltl3ba, .spot]
}

func _ltl3ba(ltl: String) -> CoBüchiAutomaton? {
    let task = Process()

    task.launchPath = "./Tools/ltl3ba"
    task.arguments = ["-f", "\"(\(ltl))\""]
    //print(ltl)
    
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

func _spot(ltl: String, hoaf: Bool = false) -> CoBüchiAutomaton? {
    let task = Process()

    task.launchPath = "./Tools/ltl2tgba"
    task.arguments = ["-f", "(\(ltl))"]
    if hoaf {
        task.arguments? += ["-H", "-B"]
    } else {
        task.arguments?.append("--spin")
    }
    
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let outputData = StreamHelper.readAllAvailableData(from: stdoutHandle)
    
    task.waitUntilExit()
    //let stdoutData = stdoutPipe.fileHandleForReading.readDataToEndOfFile()
    guard let output = String(data: outputData, encoding: String.Encoding.utf8) else {
        return nil
    }
    if hoaf {
        return parse(hoaf: output)
    } else {
        return parseSpinNeverClaim(neverClaim: output)
    }
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
            let origName = String(line[line.startIndex..<line.index(before: line.endIndex)])
            let name = normalizeStateName(String(origName))
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
    guard let initial = initialState else {
        Logger.default().error("could not extract initial state from never claim")
        return nil
    }
    var automaton =  CoBüchiAutomaton(initialStates: [initial],
                            states: states,
                            transitions: transitions,
                            safetyConditions: [:],
                            rejectingStates: rejectingStates)
    automaton.simplify()
    automaton.calculateSCC()
    return automaton
}

/**
 *  This function parses the [HOA format](http://adl.github.io/hoaf/),
 *  but is very limited as it assumes Buchi acceptance
 */
private func parse(hoaf: String) -> CoBüchiAutomaton? {
    var states: Set<String> = Set()
    var rejectingStates: Set<String> = Set()
    var initialStates: Set<String> = Set()
    var transitions: [String : [String: Logic]] = [:]
    var ap: [String] = []
    
    var lastState: String? = nil
    
    func toState(_ n: Int) -> String {
        return "s\(n)"
    }
    
    func parseAP(_ line: String) -> [String] {
        var aps: [String] = []
        
        var ap: String? = nil
        for character in line.characters {
            if character == "\"" {
                if let apValue = ap {
                    aps.append(apValue)
                    ap = nil
                } else {
                    ap = ""
                }
            } else {
                ap?.append(character)
            }
        }
        return aps
    }
    
    func getTransition(_ line: String) -> (Logic, String)? {
        var formula: String? = nil
        var proposition: Int? = nil
        var target: Int? = nil
        for character in line.characters {
            if character == "[" {
                formula = ""
            } else if character == "]" {
                if let prop = proposition {
                    formula?.append(ap[prop])
                    proposition = nil
                }
                target = 0
            } else if target == nil {
                if character == "t" {
                    formula = "1"
                }
                else if ["!", "|", "&", " "].contains(character) {
                    if let prop = proposition {
                        formula?.append(ap[prop])
                        proposition = nil
                    }
                    formula?.append(character)
                } else {
                    assert(("0"..."9").contains(character))
                    guard let number = Int(String(character)) else {
                        return nil
                    }
                    if let prop = proposition {
                        proposition = prop * 10 + number
                    } else {
                        proposition = number
                    }
                }
            } else if ("0"..."9").contains(character) {
                if let targetValue = target {
                    target = targetValue * 10 + Int(String(character))!
                }
            }
        }
        guard let formulaValue = formula else {
            return nil
        }
        guard let parsedFormula = BooleanUtils.parse(string: formulaValue) else {
            return nil
        }
        guard let targetValue = target else {
            return nil
        }
        return (parsedFormula, toState(targetValue))
    }
    
    var isBody = false
    for var line in hoaf.components(separatedBy: "\n") {
        line = line.trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines)
        //print(line)
        if line.hasPrefix("acc-name:") {
            if line != "acc-name: Buchi" {
                Logger.default().error("wrong acceptance condition found in HOAF")
                return nil
            }
        } else if line.hasPrefix("Acceptance:") {
            if line != "Acceptance: 1 Inf(0)" {
                Logger.default().error("wrong acceptance condition found in HOAF")
                return nil
            }
        } else if line.hasPrefix("States:") {
            guard let number = Int(line.components(separatedBy: " ")[1]) else {
                return nil
            }
            (0..<number).forEach({ states.insert(toState($0)) })
        } else if line.hasPrefix("Start:") {
            guard let number = Int(line.components(separatedBy: " ")[1]) else {
                return nil
            }
            initialStates.insert(toState(number))
        } else if line.hasPrefix("AP:") {
            ap = parseAP(line)
        } else if line.hasPrefix("--BODY--") {
            isBody = true
        } else if isBody && line.hasPrefix("State:") {
            let parts = line.components(separatedBy: " ")
            guard let number = Int(parts[1]) else {
                return nil
            }
            lastState = toState(number)
            if parts.count > 2 && !parts[parts.endIndex.advanced(by: -1)].hasPrefix("\"") {
                // is rejecting
                rejectingStates.insert(toState(number))
            }
            transitions[toState(number)] = [:]
        } else if isBody && line.hasPrefix("[") {
            // transitions
            assert(lastState != nil)
            
            guard let (transitionGuard, targetState) = getTransition(line) else {
                return nil
            }
            transitions[lastState!]?[targetState] = transitionGuard
        }
    }
    var automaton =  CoBüchiAutomaton(initialStates: initialStates,
                                      states: states,
                                      transitions: transitions,
                                      safetyConditions: [:],
                                      rejectingStates: rejectingStates)
    automaton.simplify()
    automaton.calculateSCC()
    return automaton
}

