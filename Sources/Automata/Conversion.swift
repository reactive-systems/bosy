import Foundation
import TSCBasic
import TSCUtility

import Logic
import LTL
import Utils

public enum LTL2AutomatonConverter: String {
    case ltl3ba
    case spot

    func convert(ltl: LTL) throws -> CoBüchiAutomaton {
        switch self {
        case .ltl3ba:
            return try convertWithLtl3ba(ltl: ltl)
        case .spot:
            return try convertWithSpot(ltl: ltl)
        }
    }

    public static let allValues: [LTL2AutomatonConverter] = [.ltl3ba, .spot]
}

func convertWithLtl3ba(ltl: LTL) throws -> CoBüchiAutomaton {
    guard let ltl3baFormatted = ltl.ltl3ba else {
        throw "cannot transform LTL to ltl3ba format"
    }
    let neverClaim = try TSCBasic.Process.checkNonZeroExit(arguments: ["./Tools/ltl3ba", "-f", "(\(ltl3baFormatted))"])
    return try parseSpinNeverClaim(neverClaim: neverClaim)
}

func convertWithSpot(ltl: LTL, hoaf: Bool = false) throws -> CoBüchiAutomaton {
    guard let ltl3baFormatted = ltl.spot else {
        throw "cannot transform LTL to ltl3ba format"
    }
    var arguments = ["./Tools/ltl2tgba", "-f", "(\(ltl3baFormatted))"]
    if hoaf {
        arguments += ["-H", "-B"]
    } else {
        arguments.append("--spin")
    }
    let output = try TSCBasic.Process.checkNonZeroExit(arguments: arguments)
    if hoaf {
        return try parse(hoaf: output)
    } else {
        return try parseSpinNeverClaim(neverClaim: output)
    }
}

func parseSpinNeverClaim(neverClaim: String) throws -> CoBüchiAutomaton {
    var states: Set<String> = Set()
    var rejectingStates: Set<String> = Set()
    var initialState: String?
    var transitions: [String: [String: Logic]] = [:]

    var lastState: String?

    // print(neverClaim)

    func normalizeStateName(_ name: String) -> String {
        name.replacingOccurrences(of: "_init", with: "").replacingOccurrences(of: "accept_", with: "")
    }

    // print("parse never claim")
    for var line in neverClaim.components(separatedBy: "\n") {
        line = line.trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines)
        if line.hasPrefix("never") || line.hasPrefix("}") || line.hasPrefix("if") || line.hasPrefix("fi") {
            continue
        } else if line.hasSuffix(":") {
            // state
            let origName = String(line[line.startIndex ..< line.index(before: line.endIndex)])
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
        throw "could not extract initial state from never claim"
    }
    var automaton = CoBüchiAutomaton(initialStates: [initial],
                                     states: states,
                                     transitions: transitions,
                                     safetyConditions: [:],
                                     rejectingStates: rejectingStates)
    automaton.removeRejectingSinks()
    automaton.calculateSCC()
    return automaton
}

/**
 *  This function parses the [HOA format](http://adl.github.io/hoaf/),
 *  but is very limited as it assumes Buchi acceptance
 */
private func parse(hoaf: String) throws -> CoBüchiAutomaton {
    var states: Set<String> = Set()
    var rejectingStates: Set<String> = Set()
    var initialStates: Set<String> = Set()
    var transitions: [String: [String: Logic]] = [:]
    var ap: [String] = []

    var lastState: String?

    func toState(_ n: Int) -> String {
        "s\(n)"
    }

    func parseAP(_ line: String) -> [String] {
        var aps: [String] = []

        var ap: String?
        for character in line {
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
        var formula: String?
        var proposition: Int?
        var target: Int?
        for character in line {
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
                } else if ["!", "|", "&", " "].contains(character) {
                    if let prop = proposition {
                        formula?.append(ap[prop])
                        proposition = nil
                    }
                    formula?.append(character)
                } else {
                    assert(("0" ... "9").contains(character))
                    guard let number = Int(String(character)) else {
                        return nil
                    }
                    if let prop = proposition {
                        proposition = prop * 10 + number
                    } else {
                        proposition = number
                    }
                }
            } else if ("0" ... "9").contains(character) {
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
        // print(line)
        if line.hasPrefix("acc-name:") {
            if line != "acc-name: Buchi" {
                throw "wrong acceptance condition found in HOAF"
            }
        } else if line.hasPrefix("Acceptance:") {
            if line != "Acceptance: 1 Inf(0)" {
                throw "wrong acceptance condition found in HOAF"
            }
        } else if line.hasPrefix("States:") {
            guard let number = Int(line.components(separatedBy: " ")[1]) else {
                throw "wrong formating of states in HOAF"
            }
            (0 ..< number).forEach { states.insert(toState($0)) }
        } else if line.hasPrefix("Start:") {
            guard let number = Int(line.components(separatedBy: " ")[1]) else {
                throw "wrong formating of states in HOAF"
            }
            initialStates.insert(toState(number))
        } else if line.hasPrefix("AP:") {
            ap = parseAP(line)
        } else if line.hasPrefix("--BODY--") {
            isBody = true
        } else if isBody, line.hasPrefix("State:") {
            let parts = line.components(separatedBy: " ")
            guard let number = Int(parts[1]) else {
                throw "wrong formating of states in HOAF"
            }
            lastState = toState(number)
            if parts.count > 2, !parts[parts.endIndex.advanced(by: -1)].hasPrefix("\"") {
                // is rejecting
                rejectingStates.insert(toState(number))
            }
            transitions[toState(number)] = [:]
        } else if isBody, line.hasPrefix("[") {
            // transitions
            assert(lastState != nil)

            guard let (transitionGuard, targetState) = getTransition(line) else {
                throw "wrong formating of transition in HOAF"
            }
            transitions[lastState!]?[targetState] = transitionGuard
        }
    }
    var automaton = CoBüchiAutomaton(initialStates: initialStates,
                                     states: states,
                                     transitions: transitions,
                                     safetyConditions: [:],
                                     rejectingStates: rejectingStates)
    automaton.removeRejectingSinks()
    automaton.calculateSCC()
    return automaton
}
