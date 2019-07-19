
import Foundation
import Basic
import SPMUtility

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
    let synthesizeOption = parser.add(option: "--synthesize", kind: Bool.self, usage: "Synthesize implementation after realizability check")
    let environmentPaths = parser.add(option: "--paths", kind: Int.self, usage: "Number of paths the environment can use for counterexample strategy (default 2)")
    let dqbfOption = parser.add(option: "--dqbf", kind: Bool.self, usage: "Use DQBF encoding")

    let args = Array(CommandLine.arguments.dropFirst())
    let result = try parser.parse(args)

    let searchEnvironment = result.get(environmentOption) ?? false
    let initialBound = result.get(minBoundOption) ?? 1
    let synthesize = result.get(synthesizeOption) ?? false
    let environmentBound = result.get(environmentPaths) ?? 2
    let dqbf = result.get(dqbfOption) ?? false

    let specification = try parseSpecification(fileName: result.get(specificationFile))

    let linear = specification.ltl
    let hyperltl = specification.hyperPrenex
    //print("linear", linear)
    //print("hyper", hyperltl)

    if !searchEnvironment {

        // build automaton for linear
        guard let linearAutomaton = try? CoBüchiAutomaton.from(ltl: !linear, using: .spot) else {
            Logger.default().error("could not construct automaton")
            fatalError()
        }

        Logger.default().info("Linear automaton contains \(linearAutomaton.states.count) states")

        // build the specification automaton for the system player
        guard let automaton = try? CoBüchiAutomaton.from(ltl: !hyperltl.ltlBody, using: .spot) else {
            Logger.default().error("could not construct automaton")
            fatalError()
        }

        Logger.default().info("Hyper automaton contains \(automaton.states.count) states")

        var encoding: BoSyEncoding
        if dqbf {
            var option = BoSyOptions()
            option.solver = SolverInstance.idq
            encoding = HyperStateSymbolicEncoding(
                options: option,
                linearAutomaton: linearAutomaton,
                hyperAutomaton: automaton,
                specification: specification)
        } else {
            encoding = HyperSmtEncoding(
                options: BoSyOptions(),
                linearAutomaton: linearAutomaton,
                hyperAutomaton: automaton,
                specification: specification)
        }
        
        for i in initialBound... {
            if try encoding.solve(forBound: i) {
                print("realizable")

                if !synthesize {
                    exit(0)
                }
                
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

        let pathVariables = hyperltl.pathVariables
        guard pathVariables.count == 2 else {
            fatalError("more than two path variables is currently not implemented")
        }

        var counterPaths: [LTLPathVariable] = []
        for i in 1...environmentBound {
            counterPaths.append(LTLPathVariable(name: "env\(i)"))
        }

        let outputPropositions: [LTLAtomicProposition] = specification.outputs.map({ LTLAtomicProposition(name: $0) })
        let inputPropositions: [LTLAtomicProposition] = specification.inputs.map({ LTLAtomicProposition(name: $0) })


        var equalOutputs: [LTL] = []
        var equalInputs: [LTL] = []

        for (i, path1) in counterPaths.enumerated() {
            for path2 in counterPaths[(i+1)...] {
                equalOutputs += outputPropositions.map({ ap in LTL.pathProposition(ap, path1) <=> LTL.pathProposition(ap, path2) })
                equalInputs += inputPropositions.map({ ap in LTL.pathProposition(ap, path1) <=> LTL.pathProposition(ap, path2) })
            }
        }
        let outputEqual: LTL = equalOutputs.reduce(LTL.tt, { val, res in val && res })
        let inputEqual: LTL = equalInputs.reduce(LTL.tt, { val, res in val && res })
        let deterministic: LTL
        switch specification.semantics {
        case .mealy:
            deterministic = .weakUntil(outputEqual, !inputEqual)
        case .moore:
            deterministic = .release(!inputEqual, outputEqual)
        }

        // actually the negated spec of environment
        var environmentSpec = deterministic

        let pi = pathVariables[0]
        let piPrime = pathVariables[1]
        for (i, path1) in counterPaths.enumerated() {
            for path2 in counterPaths[(i+1)...] {
                environmentSpec &= body.replacePathProposition(mapping: [pi: path1, piPrime: path2])
            }
        }

        for pathVar in counterPaths {
            environmentSpec &= linear.addPathPropositions(path: pathVar)
        }

        guard let specificationAutomaton = try? CoBüchiAutomaton.from(ltl: environmentSpec, using: .spot) else {
            Logger.default().error("could not construct automaton")
            fatalError()
        }

        Logger.default().info("Automaton contains \(specificationAutomaton.states.count) states")

        let ltlSpecification = SynthesisSpecification(semantics: specification.semantics.swapped,
                                                      inputs: outputPropositions.reduce([], { res, val in res + counterPaths.map({ pi in LTL.pathProposition(val, pi).description }) }),
                                                      outputs: inputPropositions.reduce([], { res, val in res + counterPaths.map({ pi in LTL.pathProposition(val, pi).description }) }),
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

                if !synthesize {
                    exit(0)
                }

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
