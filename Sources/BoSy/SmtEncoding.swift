import Utils
import CAiger
import Foundation

struct SmtEncoding: BoSyEncoding {
    
    let automaton: CoBüchiAutomaton
    let semantics: TransitionSystemType
    let inputs: [String]
    let outputs: [String]
    
    // intermediate results
    var assignments: String?
    var instance: Logic?
    var solutionBound: Int
    
    init(automaton: CoBüchiAutomaton, semantics: TransitionSystemType, inputs: [String], outputs: [String]) {
        self.automaton = automaton
        self.semantics = semantics
        self.inputs = inputs
        self.outputs = outputs
        
        assignments = nil
        instance = nil
        solutionBound = 0
    }
    
    func getEncoding(forBound bound: Int) -> String? {
        
        let states = 0..<bound
        
        var smt = String()
        
        // states
        smt.append("(declare-datatypes () ((S \(states.map({ "s\($0)" }).joined(separator: " ")))))\n")
        
        // lambdas
        for q in automaton.states {
            smt.append("(declare-fun \(lambda(q)) (S) Bool)\n")
        }
        
        // lambda sharp
        for q in automaton.states {
            smt.append("(declare-fun \(lambdaSharp(q)) (S) Int)\n")
        }
        
        // tau
        smt.append("(declare-fun tau (S \(inputs.map({ name in "Bool" }).joined(separator: " "))) S)\n")
        
        // moore only!
        for o in outputs {
            smt.append("(declare-fun \(o) (S) Bool)\n")
        }
        
        for state in automaton.initialStates {
            smt.append("(assert (\(lambda(state)) s0))\n")
        }

        let printer = SmtPrinter()
        
        for q in automaton.states {
            
            let replacer = ReplacingPropositionVisitor(replace: {
                proposition in
                if self.outputs.contains(proposition.name) {
                    return FunctionApplication(function: proposition, application: [Proposition("s")])
                } else {
                    return nil
                }
            })
            
            if let condition = automaton.safetyConditions[q] {
                let assertion = FunctionApplication(function: lambda(q), application: [Proposition("s")]) --> condition.accept(visitor: replacer)
                smt.append("(assert (forall ((s S) \(inputs.map({ "(\($0) Bool)" }).joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
            guard let outgoing = automaton.transitions[q] else {
                continue
            }
            
            for (qPrime, guardCondition) in outgoing {
                let transitionCondition = requireTransition(q: q, qPrime: qPrime, rejectingStates: automaton.rejectingStates)
                let assertion = (FunctionApplication(function: lambda(q), application: [Proposition("s")]) & guardCondition.accept(visitor: replacer)) --> transitionCondition
                smt.append("(assert (forall ((s S) \(inputs.map({ "(\($0) Bool)" }).joined(separator: " "))) \(assertion.accept(visitor: printer))))\n")
            }
        }
        
        smt.append("(check-sat)\n")
        let inputPropositions: [Proposition] = inputs.map({ Proposition($0) })
        // extract solution: transition relation
        for source in 0..<bound {
            for i in allBooleanAssignments(variables: inputPropositions){
                smt.append("(get-value ((tau s"+String(source)+""+smtStringFromAssignment(i)+")))\n")
            }
        }
        // extract solution: outputs
        for o in outputs {
            for state in 0..<bound {
                smt.append("(get-value (("+o+" s"+String(state)+")))\n")
            }
        }
        
        return smt
    }
    
    func requireTransition(q: CoBüchiAutomaton.State, qPrime: CoBüchiAutomaton.State, rejectingStates: Set<CoBüchiAutomaton.State>) -> Logic {
        let lambdaNext = FunctionApplication(function: lambda(qPrime), application: [
            FunctionApplication(function: Proposition("tau"), application: [
                Proposition("s")
                ] + inputs.map(Proposition.init) as [Proposition])
            ])
        if automaton.isStateInNonRejectingSCC(q) || automaton.isStateInNonRejectingSCC(qPrime) || !automaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            return lambdaNext
        } else {
            return lambdaNext & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual,
                                                  lhs: FunctionApplication(function: lambdaSharp(qPrime), application: [
                                                    FunctionApplication(function: Proposition("tau"), application: [
                                                        Proposition("s")
                                                        ] + inputs.map(Proposition.init) as [Proposition])
                                                    ]),
                                                  rhs: FunctionApplication(function: lambdaSharp(q), application: [Proposition("s")]))
        }
    }

    func lambda(_ automatonState: CoBüchiAutomaton.State) -> String {
        return "lambda_\(automatonState)"
    }
    
    func lambda(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition(lambda(automatonState))
    }
    
    func lambdaSharp(_ automatonState: CoBüchiAutomaton.State) -> String {
        return "lambdaSharp_\(automatonState)"
    }
    
    func lambdaSharp(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition(lambdaSharp(automatonState))
    }

    mutating func solve(forBound bound: Int) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")
        
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        
        //print(instance)
        
        guard let result = z3(smt2: instance) else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        
        if (result.0 == .SAT) {
            self.solutionBound = bound
            print(result.1!)
            self.assignments = result.1!
        }
        
        return result.0 == .SAT
    }
    
    func rangeToStrIndex(range: Range<Int>, str: String) -> Range<String.Index> {
        let start = str.index(str.startIndex, offsetBy: range.lowerBound)
        let end = str.index(str.startIndex, offsetBy: range.upperBound)
        let groupRange = start..<end
        return groupRange
    }
    
    func extractTransition(smtString: String) -> (Int,Logic,Int) {
        let targetRegex = try! NSRegularExpression(pattern: "s(\\d+)")
        let matches = targetRegex.matches(in: smtString, range: NSMakeRange(0, smtString.utf16.count))
        let firstGroup = matches[0].rangeAt(1).toRange()
        let sourceState = Int(smtString.substring(with: rangeToStrIndex(range: firstGroup!, str:smtString)))
        let secondGroup = matches[1].rangeAt(1).toRange()
        let targetState = Int(smtString.substring(with: rangeToStrIndex(range: secondGroup!, str:smtString)))
        
        let transitionRegex = try! NSRegularExpression(pattern: "(true|false)")
        let matchesProps = transitionRegex.matches(in: smtString, range: NSMakeRange(0, smtString.utf16.count))
        
        var transition: Logic
        transition = Literal.True
        for i in 0..<inputs.count {
            let match = matchesProps[i].rangeAt(1).toRange()
            let truthvalue = smtString.substring(with: rangeToStrIndex(range: match!, str: smtString))
            if truthvalue == "true" {
                transition = transition & Proposition(inputs[i])
            } else if truthvalue == "false" {
                transition = transition & !Proposition(inputs[i])
            }
        }
        
        return(sourceState!,transition,targetState!)
    }
    
    func extractOutput(smtString: String) -> (Int,String,Bool) {
        let targetRegex = try! NSRegularExpression(pattern: "s(\\d+)")
        let matches = targetRegex.matches(in: smtString, range: NSMakeRange(0, smtString.utf16.count))
        let firstGroup = matches[0].rangeAt(1).toRange()
        let sourceState = Int(smtString.substring(with: rangeToStrIndex(range: firstGroup!, str:smtString)))
        
        let guardRegex = try! NSRegularExpression(pattern: "(true|false)")
        let tvalue = guardRegex.matches(in: smtString, range: NSMakeRange(0, smtString.utf16.count))
        let tgroup = tvalue[0].rangeAt(1).toRange()
        let tval = Bool(smtString.substring(with: rangeToStrIndex(range:tgroup!, str:smtString)))
        
        let outputRegex = try! NSRegularExpression(pattern: "([^(\\s)]+)\\s")
        let outMatches = outputRegex.matches(in: smtString, range: NSMakeRange(0, smtString.utf16.count))
        let outGroup = outMatches[0].rangeAt(1).toRange()
        let outVal = smtString.substring(with: rangeToStrIndex(range:outGroup!, str:smtString))
        
        return (sourceState!,outVal,tval!)
    }
    
    func extractSolution() -> BoSySolution? {
        print("Extracting Solution\n")
        guard let assignments = assignments else {
            Logger.default().error("hasSolution() must be true before calling this function")
            return nil
        }

        var solution = ExplicitStateSolution(bound: solutionBound, inputs: inputs, outputs: outputs)
        assignments.enumerateLines {
            line, stop in
            if line.hasPrefix("(((tau") {
                let (source,transition,target) = self.extractTransition(smtString: line)
                solution.addTransition(from: source, to: target, withGuard: transition)
            } else if line.hasPrefix("(((") {
                let (source, output, truthvalue) = self.extractOutput(smtString: line)
                if truthvalue {
                    solution.add(output: output, inState: source, withGuard: Literal.True)
                } else {
                    solution.add(output: output, inState: source, withGuard: Literal.False)
                }
                
            }
        }
//        for source in 0..<solutionBound {
//            for target in 0..<solutionBound {
//                var transitions: [Logic] = []
//                for i in allBooleanAssignments(variables: inputPropositions) {
//                    if assignments[tau(source, i, target)]! == Literal.False {
//                        let clause = i.map({ v, val in val == Literal.True ? !v : v })
//                        transitions.append(clause.reduce(Literal.False, |))
//                    }
//                }
//                let transition = transitions.reduce(Literal.True, &)
//                if transition as? Literal != nil && transition as! Literal == Literal.False {
//                    continue
//                }
//                solution.addTransition(from: source, to: target, withGuard: transition)
//            }
//            for output in outputs {
//                let enabled: Logic
//                let proposition = Proposition(self.output(output, forState: source))
//                enabled = assignments[proposition]!
//
//            solution.add(output: output, inState: source, withGuard: enabled)
//            }
//        }
//        return solution
        return solution
    }
}
