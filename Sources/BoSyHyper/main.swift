
import Foundation
import Basic
import Utility

import Specification
import Utils

// MARK: - argument parsing

/**
 * Parse specification given by file name.
 * If no file name is given, try to read from standard input.
 */
func parseSpecification(fileName: String?) throws -> SynthesisSpecification {
    let json: String
    if let specificationFileName = fileName {
        Logger.default().debug("reading from file \"\(specificationFileName)\"")
        json = try String(contentsOfFile: specificationFileName, encoding: .utf8)
    } else {
        // Read from stdin
        Logger.default().debug("reading from standard input")

        let standardInput = FileHandle.standardInput
        let input = StreamHelper.readAllAvailableData(from: standardInput)
        guard let decoded = String(data: input, encoding: String.Encoding.utf8) else {
            print("error: cannot read input from stdin")
            exit(1)
        }
        json = decoded
    }
    guard let specification = SynthesisSpecification.fromJson(string: json) else {
        print("error: cannot parse specification")
        exit(1)
    }
    return specification
}

do {
    let parser = ArgumentParser(commandName: "BoSyHyper", usage: "specification", overview: "BoSyHyper is a synthesis tool for temporal hyperproperties.")
    let specification = parser.add(positional: "specification", kind: String.self, optional: true, usage: "A file containing the specification in BoSy format", completion: .filename)

    let args = Array(CommandLine.arguments.dropFirst())
    let result = try parser.parse(args)

    print(try parseSpecification(fileName: result.get(specification)))


} catch ArgumentParserError.expectedValue(let value) {
    print("Missing value for argument \(value).")
} catch ArgumentParserError.expectedArguments(let parser, let stringArray) {
    print("Missing arguments: \(stringArray.joined()).")
} catch {
    print(error.localizedDescription)
}
