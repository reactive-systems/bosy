import Foundation

import Utils

import LTL

enum TransitionSystemType: String {
    case mealy = "mealy"
    case moore = "moore"
    
    func swap() -> TransitionSystemType {
        switch self {
            case .mealy: return .moore
            case .moore: return .mealy
        }
    }
    
    static let allValues: [TransitionSystemType] = [.mealy, .moore]
}

protocol InputFileFormat {
    var semantics: TransitionSystemType { get set }
    var inputs: [String] { get }
    var outputs: [String] { get }
    var assumptions: [LTL] { get }
    var guarantees: [LTL] { get }
}

struct BoSyInputFileFormat: InputFileFormat {
    var semantics: TransitionSystemType
    let inputs: [String]
    let outputs: [String]
    let assumptions: [LTL]
    let guarantees: [LTL]
    
    static func fromJson(string: String) -> BoSyInputFileFormat? {
        guard let data = string.data(using: .utf8) else {
            Logger.default().error("could not decode JSON")
            return nil
        }
        guard let spec = try? JSONSerialization.jsonObject(with: data, options: []) else {
            Logger.default().error("could not decode JSON")
            return nil
        }
        
        guard let specDictionary = spec as? [String:Any] else {
            Logger.default().error("JSON format is not valid")
            return nil
        }
        
        // Decode semantics
        guard let semanticsJSON = specDictionary["semantics"] else {
            Logger.default().error("no semantics given")
            return nil
        }
        guard let semanticsString = semanticsJSON as? String else {
            Logger.default().error("semantics is not given as string")
            return nil
        }
        guard let semantics = TransitionSystemType(rawValue: semanticsString) else {
            Logger.default().error("invalid semantics, expect either \"mealy\" or \"moore\", found \"\(semanticsString)\"")
            return nil
        }
        
        // Decode arrays
        func toArray(key: String) -> [String]? {
            guard let json = specDictionary[key] else {
                return nil
            }
            guard let jsonArray = json as? [String] else {
                return nil
            }
            return jsonArray
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
        let parsedGuarantees = guarantees.flatMap({ try? LTL.parse(fromString: $0) })
        if guarantees.count != parsedGuarantees.count {
            Logger.default().error("could not parse guarantees")
            return nil
        }
        
        guard let assumptions = toArray(key: "assumptions") else {
            Logger.default().error("no assumptions given")
            return nil
        }
        let parsedAssumptions = assumptions.flatMap({ try? LTL.parse(fromString: $0) })
        if assumptions.count != parsedAssumptions.count {
            Logger.default().error("could not parse assumptions")
            return nil
        }
        return BoSyInputFileFormat(semantics: semantics, inputs: inputs, outputs: outputs, assumptions: parsedAssumptions, guarantees: parsedGuarantees)
    }
}

func syfco(tlsf: String, arguments: [String]) -> String {
    let task = Process()

    task.launchPath = "./Tools/syfco"
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
        stdinHandle.write(data)
        stdinHandle.closeFile()
    }
    
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let outputData = StreamHelper.readAllAvailableData(from: stdoutHandle)
    
    task.waitUntilExit()
    
    //let data = stdoutPipe.fileHandleForReading.readDataToEndOfFile()
    return String(data: outputData, encoding: String.Encoding.utf8)!
}
