import Utils
import CAiger
import Logic
import Automata
import Specification
import TransitionSystem

struct StateSymbolicEncoding: BoSyEncoding {
    
    let options: BoSyOptions
    let automaton: CoBüchiAutomaton
    let specification: SynthesisSpecification
    
    init(options: BoSyOptions, automaton: CoBüchiAutomaton, specification: SynthesisSpecification) {
        self.options = options
        self.automaton = automaton
        self.specification = specification
    }
    
    func getEncoding(forBound bound: Int) -> Logic? {
        
        let states = 0..<bound
        
        var preconditions: [Logic] = []
        var matrix: [Logic] = []
        
        let statePropositions: [Proposition] = (0..<numBitsNeeded(states.count)).map({ bit in Proposition("s\(bit)") })
        let nextStatePropositions: [Proposition] = (0..<numBitsNeeded(states.count)).map({ bit in Proposition("sp\(bit)") })
        let tauPropositions: [Proposition] = (0..<numBitsNeeded(states.count)).map({ bit in tau(bit: bit) })
        let inputPropositions: [Proposition] = self.specification.inputs.map(Proposition.init)
        let outputPropositions: [Proposition] = self.specification.outputs.map(Proposition.init)
        let tauApplications: [FunctionApplication] = tauPropositions.map({ FunctionApplication(function: $0, application: statePropositions + inputPropositions) })
        
        let numBits = numBitsNeeded(bound)
        for i in bound ..< (1 << numBits) {
            preconditions.append(!explicitToSymbolic(base: "s", value: i, bits: numBits))
            preconditions.append(!explicitToSymbolic(base: "sp", value: i, bits: numBits))
            matrix.append(!explicitToSymbolic(base: "t_", value: i, bits: numBits, parameters: statePropositions + inputPropositions))
        }
        
        // initial states
        let premise = explicitToSymbolic(base: "s", value: 0, bits: numBits)
        for q in automaton.initialStates {
            matrix.append(premise --> lambda(q, states: statePropositions))
        }
        
        for q in automaton.states {
            var conjunct: [Logic] = []
            
            let replacer = ReplacingPropositionVisitor(replace: {
                proposition in
                if self.specification.outputs.contains(proposition.name) {
                    let dependencies = self.specification.semantics == .mealy ? statePropositions + inputPropositions : statePropositions
                    return FunctionApplication(function: proposition, application: dependencies)
                } else {
                    return nil
                }
            })
            
            if let condition = automaton.safetyConditions[q] {
                conjunct.append(condition.accept(visitor: replacer))
            }
            guard let outgoing = automaton.transitions[q] else {
                assert(conjunct.isEmpty)
                continue
            }
            
            for (qPrime, guardCondition) in outgoing {
                let transitionCondition = requireTransition(q: q, qPrime: qPrime, bound: bound, rejectingStates: automaton.rejectingStates, states: statePropositions, nextStates: nextStatePropositions, taus: tauApplications)
                if guardCondition as? Literal != nil && guardCondition as! Literal == Literal.True {
                    conjunct.append(transitionCondition)
                } else {
                    conjunct.append(guardCondition.accept(visitor: replacer) --> transitionCondition)
                }
            }
            matrix.append(lambda(q, states: statePropositions) --> conjunct.reduce(Literal.True, &))
        }
        
        let formula: Logic = preconditions.reduce(Literal.True, &) --> matrix.reduce(Literal.True, &)
        
        let lambdaPropositions: [Proposition] = self.automaton.states.map({ lambdaProposition($0) })
        let lambdaSharpPropositions: [Proposition] = self.automaton.states.map({ lambdaSharpProposition($0) })
        
        let universalQuantified: Logic = Quantifier(.Forall, variables: statePropositions + nextStatePropositions + inputPropositions, scope: formula)
        let outputQuantification: Logic = Quantifier(.Exists, variables: outputPropositions, scope: universalQuantified, arity: specification.semantics == .mealy ? numBitsNeeded(states.count) + self.specification.inputs.count : numBitsNeeded(states.count))
        let tauQuantification: Logic = Quantifier(.Exists, variables: tauPropositions, scope: outputQuantification, arity: numBitsNeeded(states.count) + self.specification.inputs.count)
        let lambdaQuantification: Logic = Quantifier(.Exists, variables: lambdaPropositions + lambdaSharpPropositions, scope: tauQuantification, arity: numBitsNeeded(states.count))
        
        let boundednessCheck = BoundednessVisitor()
        assert(lambdaQuantification.accept(visitor: boundednessCheck))
        
        let removeComparable = RemoveComparableVisitor(bound: bound)
        let result = lambdaQuantification.accept(visitor: removeComparable)
        
        return result
    }
    
    func requireTransition(q: CoBüchiAutomaton.State, qPrime: CoBüchiAutomaton.State, bound: Int, rejectingStates: Set<CoBüchiAutomaton.State>, states: [Proposition], nextStates: [Proposition], taus: [FunctionApplication]) -> Logic {
        if automaton.isStateInNonRejectingSCC(q) || automaton.isStateInNonRejectingSCC(qPrime) || !automaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            return tauNextStateAssertion(states: nextStates, taus: taus) --> lambda(qPrime, states: nextStates)
        } else {
            return tauNextStateAssertion(states: nextStates, taus: taus) -->
                   (lambda(qPrime, states: nextStates) & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual, lhs: lambdaSharp(qPrime, states: nextStates), rhs: lambdaSharp(q, states: states)))
        }
    }
    
    func explicitToSymbolic(base: String, value: Int, bits: Int, parameters: [Proposition]? = nil) -> Logic {
        var and: [Logic] = []
        for (i, bit) in binaryFrom(value, bits: bits).characters.enumerated() {
            let prop: Logic
            if let parameters = parameters {
                prop = FunctionApplication(function: Proposition("\(base)\(i)"), application: parameters)
            } else {
                prop = Proposition("\(base)\(i)")
            }
            and.append(bit == "1" ? prop : !prop)
        }
        return and.reduce(Literal.True, &)
    }
    
    func tauNextStateAssertion(states: [Proposition], taus: [FunctionApplication]) -> Logic {
        assert(states.count == taus.count)
        var assertion: [Logic] = []
        for (state, tau) in zip(states, taus) {
            assertion.append(state <-> tau)
        }
        return assertion.reduce(Literal.True, &)
    }
    
    func lambdaProposition(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("l_\(automatonState)")
    }
    
    func lambda(_ automatonState: CoBüchiAutomaton.State, states: [Proposition]) -> FunctionApplication {
        return FunctionApplication(function: lambdaProposition(automatonState), application: states)
    }
    
    func lambdaSharpProposition(_ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("ls_\(automatonState)")
    }
    
    func lambdaSharp(_ automatonState: CoBüchiAutomaton.State, states: [Proposition]) -> FunctionApplication {
        return FunctionApplication(function: lambdaSharpProposition(automatonState), application: states)
    }
    
    func tau(bit: Int) -> Proposition {
        return Proposition("t_\(bit)")
    }
    
    func output(_ name: String, forState state: Int) -> String {
        return "\(name)_\(state)"
    }
    
    mutating func solve(forBound bound: Int) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")
        
        let constraintTimer = options.statistics?.startTimer(phase: .constraintGeneration)
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        constraintTimer?.stop()
        //print(instance)
        
        guard let solver = options.solver?.instance as? DqbfSolver else {
            throw BoSyEncodingError.SolvingFailed("solver creation failed")
        }
        
        let solvingTimer = options.statistics?.startTimer(phase: .solving)
        guard let result = solver.solve(formula: instance) else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        solvingTimer?.stop()
        
        return result == .sat
    }
    
    func extractSolution() -> TransitionSystem? {
        return nil
    }
}
