import Foundation

import Utils
import LTL

public enum TransitionSystemType: String {
    case mealy = "mealy"
    case moore = "moore"
    
    public var swapped: TransitionSystemType {
        switch self {
            case .mealy: return .moore
            case .moore: return .mealy
        }
    }
    
    public static let allValues: [TransitionSystemType] = [.mealy, .moore]
}

public enum SupportedFileFormats {
    case bosy
    case tlsf
}

public struct SynthesisSpecification {
    public var semantics: TransitionSystemType
    public let inputs: [String]
    public let outputs: [String]
    public let assumptions: [LTL]
    public let guarantees: [LTL]
    
    public var dualized: SynthesisSpecification {
        let dualizedLTL = !ltl
        return SynthesisSpecification(semantics: semantics.swapped, inputs: outputs, outputs: inputs, assumptions: [], guarantees: [dualizedLTL])
    }
    
    public var ltl: LTL {
        return assumptions.reduce(LTL.tt, &&) => guarantees.reduce(LTL.tt, &&)
    }
    
    public static func fromJson(string: String) -> SynthesisSpecification? {
        Logger.default().debug("parse JSON input file")
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
        Logger.default().debug("parsing JSON succeeded")
        return SynthesisSpecification(semantics: semantics, inputs: inputs, outputs: outputs, assumptions: parsedAssumptions, guarantees: parsedGuarantees)
    }

    public static func from(tlsf: String) -> SynthesisSpecification? {

        guard let tempFile = TempFile(suffix: "tlsf") else {
            return nil
        }
        guard (try? tlsf.write(to: tempFile.url, atomically: true, encoding: .utf8)) != nil else {
            return nil
        }

        let outputPipe = Pipe()

        let syfco = Process()
        syfco.launchPath = "./Tools/syfco"
        syfco.arguments = ["--format", "bosy", tempFile.path]
        syfco.standardOutput = outputPipe
        syfco.launch()

        let result = StreamHelper.readAllAvailableData(from: outputPipe.fileHandleForReading)
        syfco.waitUntilExit()

        guard let bosyJson = String(data: result, encoding: .utf8) else {
            return nil
        }

        return .fromJson(string: bosyJson)
    }
    
    public var smv: String? {
        var smv: [String] =  ["MODULE main", "\tVAR"]
        smv += (inputs + outputs).map({ proposition in "\t\t\(proposition) : boolean;" })
        guard let smvLTLSpec = ltl.normalized.smv else {
            return nil
        }
        smv.append("\tLTLSPEC \(smvLTLSpec)")
        return smv.joined(separator: "\n")
    }
}

