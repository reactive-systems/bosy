
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
import Logic

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
    let environmentOption = parser.add(option: "--environment", kind: Bool.self, usage: "Search for environment strategies instead of system")
    let minBoundOption = parser.add(option: "--min-bound", kind: Int.self, usage: "Specify the initial bound (default 1)")

    let args = Array(CommandLine.arguments.dropFirst())
    let result = try parser.parse(args)

    let searchEnvironment = result.get(environmentOption) ?? false
    let initialBound = result.get(minBoundOption) ?? 1

    let specification = try parseSpecification(fileName: result.get(specificationFile))

    let linear = specification.ltl
    let hyperltl = specification.hyperPrenex
    print("linear", linear)
    print("hyper", hyperltl)

    if !searchEnvironment {

        // build automaton for linear
        guard let linearSpot = (!linear).spot else {
            fatalError()
        }
        guard let linearAutomaton = LTL2AutomatonConverter.spot.convert(ltl: linearSpot) else {
            Logger.default().error("could not construct automaton")
            fatalError()
        }

        Logger.default().info("Linear automaton contains \(linearAutomaton.states.count) states")

        // build the specification automaton for the system player

        let body = hyperltl.ltlBody
        guard let spot = (!body).spot else {
            fatalError()
        }
        guard let automaton = LTL2AutomatonConverter.spot.convert(ltl: spot) else {
            Logger.default().error("could not construct automaton")
            fatalError()
        }

        Logger.default().info("Hyper automaton contains \(automaton.states.count) states")

        let encoding = HyperSmtEncoding(
                options: BoSyOptions(),
                linearAutomaton: linearAutomaton,
                hyperAutomaton: automaton,
                specification: specification)
        
        for i in initialBound... {
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

    } else {
        // build the specification automaton for environment player

        // the environment wins, if it
        // 1) either forces a violation of the specification, or
        // 2) the system player plays non-deterministic

        let body = hyperltl.ltlBody
        fatalError("does not work currently")

        let pathVariables = hyperltl.pathVariables
        guard pathVariables.count == 2 else {
            fatalError("more than two path variables is currently not implemented")
        }
        let pi = pathVariables[0]
        let piPrime = pathVariables[1]
        let outputPropositions: [LTLAtomicProposition] = specification.outputs.map({ LTLAtomicProposition(name: $0) })
        let inputPropositions: [LTLAtomicProposition] = specification.inputs.map({ LTLAtomicProposition(name: $0) })
        let outputEqual: LTL = outputPropositions.map({ ap in LTL.pathProposition(ap, pi) <=> LTL.pathProposition(ap, piPrime) })
                                                 .reduce(LTL.tt, { val, res in val && res })
        let inputEqual: LTL = inputPropositions.map({ ap in LTL.pathProposition(ap, pi) <=> LTL.pathProposition(ap, piPrime) })
                                               .reduce(LTL.tt, { val, res in val && res })
        let deterministic: LTL
        switch specification.semantics {
        case .mealy:
            deterministic = .weakUntil(outputEqual, !inputEqual)
        case .moore:
            deterministic = .release(!inputEqual, outputEqual)
        }

        let environmentSpec = deterministic && body

        guard let spot = environmentSpec.spot else {
            fatalError()
        }
        print(spot)
        guard let specificationAutomaton = LTL2AutomatonConverter.spot.convert(ltl: spot) else {
            Logger.default().error("could not construct automaton")
            fatalError()
        }

        let ltlSpecification = SynthesisSpecification(semantics: specification.semantics.swapped,
                                                      inputs: outputPropositions.reduce([], { res, val in res + pathVariables.map({ pi in LTL.pathProposition(val, pi).description }) }),
                                                      outputs: inputPropositions.reduce([], { res, val in res + pathVariables.map({ pi in LTL.pathProposition(val, pi).description }) }),
                                                      assumptions: [],
                                                      guarantees: [environmentSpec])

        var options = BoSyOptions()
        options.solver = .rareqs
        options.qbfPreprocessor = .bloqqer
        options.qbfCertifier = .quabs

        let encoding = InputSymbolicEncoding(options: options, automaton: specificationAutomaton, specification: ltlSpecification, synthesize: false)

        for i in initialBound... {
            if try encoding.solve(forBound: i) {
                print("unrealizable")

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
    }





} catch {
    print(error)
    exit(1)
}
