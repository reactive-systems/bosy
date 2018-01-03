
import Foundation
import Basic
import Utility

import Specification
import Utils
import LTL
import Automata
import BoundedSynthesis
import TransitionSystem
import CAiger

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
        guard let decoded = String(data: input, encoding: .utf8) else {
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
    let specificationFile = parser.add(positional: "specification", kind: String.self, optional: true, usage: "A file containing the specification in BoSy format", completion: .filename)

    let args = Array(CommandLine.arguments.dropFirst())
    let result = try parser.parse(args)

    let specification = try parseSpecification(fileName: result.get(specificationFile))

    assert(specification.assumptions.count == 0)
    assert(specification.guarantees.count == 1)
    guard let hyperltl = specification.guarantees.first else {
        fatalError()
    }
    assert(hyperltl.isHyperLTL)
    print(hyperltl)
    let body = hyperltl.ltlBody
    guard let spot = (!body).spot else {
        fatalError()
    }
    print(spot)
    guard let automaton = LTL2AutomatonConverter.spot.convert(ltl: spot) else {
        Logger.default().error("could not construct automaton")
        fatalError()
    }
    print(automaton)

    var encoding = HyperSmtEncoding(
        options: BoSyOptions(),
        automaton: automaton,
        specification: specification)

    for i in 1... {
        if try encoding.solve(forBound: i) {
            print("realizable")

            guard let solution = encoding.extractSolution() else {
                fatalError()
            }
            print((solution as! DotRepresentable).dot)

            guard let aiger_solution = (solution as? AigerRepresentable)?.aiger else {
                Logger.default().error("could not encode solution as AIGER")
                exit(1)
            }
            let minimized = aiger_solution.minimized
            aiger_write_to_file(minimized, aiger_ascii_mode, stdout)

            exit(0)
        }
    }

} catch {
    print(error)
    exit(1)
}
