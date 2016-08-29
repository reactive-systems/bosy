import Foundation

import Utils

import Jay
//import Jay_Extras

enum TransitionSystemType {
    case Mealy
    case Moore
    
    static func from(string: String) -> TransitionSystemType? {
        switch string {
        case "mealy":
            return .Mealy
        case "moore":
            return .Moore
        default:
            return nil
        }
    }
    
    func swap() -> TransitionSystemType {
        switch self {
            case .Mealy: return .Moore
            case .Moore: return .Mealy
        }
    }
}

protocol InputFileFormat {
    var semantics: TransitionSystemType { get }
    var inputs: [String] { get }
    var outputs: [String] { get }
    var assumptions: [String] { get }
    var guarantees: [String] { get }
}

struct BoSyInputFileFormat: InputFileFormat {
    let semantics: TransitionSystemType
    let inputs: [String]
    let outputs: [String]
    let assumptions: [String]
    let guarantees: [String]
    
    static func fromJson(string: String) -> BoSyInputFileFormat? {
        let data: [UInt8] = Array(string.utf8)
        guard let spec = try? Jay().jsonFromData(data) else {
            Logger.default().error("could not decode JSON")
            return nil
        }
        
        guard case JSON.object(let specDictionary) = spec else {
            Logger.default().error("JSON format is not valid")
            return nil
        }
        
        // Decode semantics
        guard let semanticsJSON = specDictionary["semantics"] else {
            Logger.default().error("no semantics given")
            return nil
        }
        guard case JSON.string(let semanticsString) = semanticsJSON else {
            Logger.default().error("semantics is not given as string")
            return nil
        }
        guard let semantics = TransitionSystemType.from(string: semanticsString) else {
            Logger.default().error("invalid semantics, expect either \"mealy\" or \"moore\", found \"\(semanticsString)\"")
            return nil
        }
        
        // Decode arrays
        func toArray(key: String) -> [String]? {
            guard let json = specDictionary[key] else {
                return nil
            }
            guard case JSON.array(let jsonArray) = json else {
                return nil
            }
            return jsonArray.flatMap({ 
                element in
                if case JSON.string(let string) = element {
                    return string
                } else {
                    return nil
                }
            })
        }
        
        guard let inputs = toArray(key: "inputs") else {
            Logger.default().error("no inputs given")
            return nil
        }
        guard let outputs = toArray(key: "outputs") else {
            Logger.default().error("no outputs given")
            return nil
        }

        guard let guarantees = toArray(key: "guarantees") else {
            Logger.default().error("no guarantees given")
            return nil
        }
        guard let assumptions = toArray(key: "assumptions") else {
            Logger.default().error("no assumptions given")
            return nil
        }
        return BoSyInputFileFormat(semantics: semantics, inputs: inputs, outputs: outputs, assumptions: assumptions, guarantees: guarantees)
    }
}

/*enum InputFileFormat {
    //case TLSF(String)
    //case LTL(ltl: String, part: String)
    
    func specification() -> (assumptions: [String], guarantees: [String])? {
        switch self {
        case .LTL(let ltl, _):
            return ([], [ltl])
        case .TLSF(let content):
            var assumptions: [String] = []
            var guarantees: [String] = []
            for line in syfco(tlsf: content, arguments: ["--format", "acacia", "--strong-simplify", "--mode", "fully", "--overwrite-semantics", "Mealy"]).components(separatedBy: ";\n") {
                // quick and dirty hack to transform to LTL format
                let isAssumption = line.hasPrefix("assume")
                let transformed = line.replacingOccurrences(of: "=1", with: "")
                                      .replacingOccurrences(of: "*", with: "&&")
                                      .replacingOccurrences(of: "+", with: "||")
                                      .replacingOccurrences(of: "assume ", with: "")
                let regexp_ = try? NSRegularExpression(pattern: "([a-zA-Z_][a-zA-Z_0-9]*)=0", options: NSRegularExpressionOptions(rawValue: 0))
                guard let regexp = regexp_ else {
                    Logger.default().error("could not build regular expression")
                    return nil
                }
                let test = NSMutableString(string: transformed)
                regexp.replaceMatches(in: test, options: NSMatchingOptions(rawValue: 0), range: NSMakeRange(0, test.length), withTemplate: "!$1")
                let result = String.init(test)
                if result.isEmpty {
                    continue
                }
                isAssumption ? assumptions.append(result) : guarantees.append(result)
            }
            return (assumptions, guarantees)
        }
    }
    
    func propositions() -> (inputs: [String], outputs: [String])? {
        switch self {
        case .LTL(_, let part):
            var inputs: [String]?
            var outputs: [String]?
            for line in part.components(separatedBy: "\n") {
                var signals = line.components(separatedBy: " ")
                let signalType = signals.removeFirst()
                if signalType == ".inputs" {
                    inputs = signals.filter({ signal in signal != ".inputs" })
                } else {
                    outputs = signals.filter({ signal in signal != ".outputs" })
                }
        
                //print("#\(signalType) \(signals)")
            }
            guard let inputs_ = inputs, let outputs_ = outputs else { return nil }
            return (inputs_, outputs_)
        case .TLSF(let content):
            let inputs = syfco(tlsf: content, arguments: ["-ins"])
                         .trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines())
                         .components(separatedBy: ", ")
                         .map({s in s.lowercased()})
                         .filter({ !$0.isEmpty })
            let outputs = syfco(tlsf: content, arguments: ["-outs"])
                          .trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines())
                          .components(separatedBy: ", ")
                          .map({s in s.lowercased()})
                          .filter({ !$0.isEmpty })
            return (inputs, outputs)
        }
    }
}*/

func syfco(tlsf: String, arguments: [String]) -> String {
    let task = Process()

    task.launchPath = "./syfco"
    task.arguments = ["--stdin"] + arguments
    
    let stdinPipe = Pipe()
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    task.standardInput = stdinPipe
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    let stdinHandle = stdinPipe.fileHandleForWriting
    if let data = tlsf.data(using: String.Encoding.utf8) {
        #if os(Linux)
        stdinHandle.writeData(data)
        #else
        stdinHandle.write(data)
        #endif
        stdinHandle.closeFile()
    }
    
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let outputData = StreamHelper.readAllAvailableData(from: stdoutHandle)
    
    task.waitUntilExit()
    
    //let data = stdoutPipe.fileHandleForReading.readDataToEndOfFile()
    return String(data: outputData, encoding: String.Encoding.utf8)!
}
