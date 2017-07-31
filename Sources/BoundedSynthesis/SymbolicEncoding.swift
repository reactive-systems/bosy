import Utils
import CAiger
import Logic
import Automata
import Specification
import TransitionSystem

struct SymbolicEncoding: BoSyEncoding {
    
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
        
        let automatonStates = automaton.states.map({ $0 })  // fix order of automaton states
        //print(automatonStates)
        
        let statePropositions: [Proposition] = (0..<numBitsNeeded(states.count)).map({ bit in Proposition("s\(bit)") })
        let nextStatePropositions: [Proposition] = (0..<numBitsNeeded(states.count)).map({ bit in Proposition("sp\(bit)") })
        let automatonStatePropositions: [Proposition] = (0..<numBitsNeeded(automaton.states.count)).map({ bit in Proposition("q\(bit)") })
        let automatonNextStatePropositions: [Proposition] = (0..<numBitsNeeded(automaton.states.count)).map({ bit in Proposition("qp\(bit)") })
        let tauPropositions: [Proposition] = (0..<numBitsNeeded(states.count)).map({ bit in tau(bit: bit) })
        let inputPropositions: [Proposition] = self.specification.inputs.map(Proposition.init)
        let outputPropositions: [Proposition] = self.specification.outputs.map(Proposition.init)
        let tauApplications: [FunctionApplication] = tauPropositions.map({ FunctionApplication(function: $0, application: statePropositions + inputPropositions) })
        
        let numBitsSystem = numBitsNeeded(bound)
        for i in bound ..< (1 << numBitsSystem) {
            preconditions.append(!explicitToSymbolic(base: "s", value: i, bits: numBitsSystem))
            preconditions.append(!explicitToSymbolic(base: "sp", value: i, bits: numBitsSystem))
            matrix.append(!explicitToSymbolic(base: "t_", value: i, bits: numBitsSystem, parameters: statePropositions + inputPropositions))
        }
        
        let numBitsAutomaton = numBitsNeeded(automaton.states.count)
        for i in automaton.states.count ..< (1 << numBitsAutomaton) {
            preconditions.append(!explicitToSymbolic(base: "q", value: i, bits: numBitsAutomaton))
            preconditions.append(!explicitToSymbolic(base: "qp", value: i, bits: numBitsAutomaton))
        }
        
        // initial states
        let initialSystem = explicitToSymbolic(base: "s", value: 0, bits: numBitsSystem)
        var initialAutomaton: [Logic] = []
        for q in automaton.initialStates {
            initialAutomaton.append(automatonState(q, states: automatonStates, primed: false))
        }
        assert(!initialAutomaton.isEmpty)
        matrix.append((initialSystem & initialAutomaton.reduce(Literal.False, |)) --> lambda(automatonStatePropositions, states: statePropositions))
        
        
        // automaton transition function
        var deltas: [Logic] = []
        var safety: [Logic] = []
        for q in automaton.states {
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
                safety.append(automatonState(q, states: automatonStates, primed: false) --> condition.accept(visitor: replacer))
            }
            
            guard let outgoing = automaton.transitions[q] else {
                continue
            }
            
            for (qPrime, guardCondition) in outgoing {
                if guardCondition as? Literal != nil && guardCondition as! Literal == Literal.True {
                    deltas.append(automatonState(q, states: automatonStates, primed: false) & automatonState(qPrime, states: automatonStates, primed: true))
                } else {
                    deltas.append(automatonState(q, states: automatonStates, primed: false) & guardCondition.accept(visitor: replacer) & automatonState(qPrime, states: automatonStates, primed: true))
                }
            }
        }
        //let delta = deltas.reduce(Literal.True, &)
        let delta = deltas.reduce(Literal.False, |)
        
        // rejecting states
        let rejecting: Logic = automaton.rejectingStates.map({ state in automatonState(state, states: automatonStates, primed: true) }).reduce(Literal.False, |)
        
        matrix.append(
            (lambda(automatonStatePropositions, states: statePropositions) & delta & tauNextStateAssertion(states: nextStatePropositions, taus: tauApplications))
                -->
            (lambda(automatonNextStatePropositions, states: nextStatePropositions) &
                (rejecting --> BooleanComparator(.Less, lhs: lambdaSharp(automatonNextStatePropositions, states: nextStatePropositions), rhs: lambdaSharp(automatonStatePropositions, states: statePropositions))) &
                (!rejecting --> BooleanComparator(.LessOrEqual, lhs: lambdaSharp(automatonNextStatePropositions, states: nextStatePropositions), rhs: lambdaSharp(automatonStatePropositions, states: statePropositions)))
            )
        )
        matrix.append(lambda(automatonStatePropositions, states: statePropositions) --> safety.reduce(Literal.True, &))
        
        let formula: Logic = preconditions.reduce(Literal.True, &) --> matrix.reduce(Literal.True, &)
        
        
        let lambdaPropositions: [Proposition] = [lambdaProposition()]
        let lambdaSharpPropositions: [Proposition] = [lambdaSharpProposition()]
        
        let universalQuantified: Logic = Quantifier(.Forall, variables: statePropositions + nextStatePropositions + automatonStatePropositions + automatonNextStatePropositions + inputPropositions, scope: formula)
        let outputQuantification: Logic = Quantifier(.Exists, variables: outputPropositions, scope: universalQuantified, arity: specification.semantics == .mealy ? numBitsNeeded(states.count) + self.specification.inputs.count : numBitsNeeded(states.count))
        let tauQuantification: Logic = Quantifier(.Exists, variables: tauPropositions, scope: outputQuantification, arity: numBitsNeeded(states.count) + self.specification.inputs.count)
        let lambdaQuantification: Logic = Quantifier(.Exists, variables: lambdaPropositions + lambdaSharpPropositions, scope: tauQuantification, arity: numBitsNeeded(states.count))
        
        let boundednessCheck = BoundednessVisitor()
        assert(lambdaQuantification.accept(visitor: boundednessCheck))
        
        let removeComparable = RemoveComparableVisitor(bound: bound)
        let result = lambdaQuantification.accept(visitor: removeComparable)
        
        //print(result)
        
        return result
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
    
    func automatonState(_ state: String, states: [String], primed: Bool) -> Logic {
        precondition(states.contains(state))
        let base = primed ? "qp" : "q"
        return explicitToSymbolic(base: base, value: states.index(of: state)!, bits: numBitsNeeded(states.count))
    }
    
    func lambdaProposition() -> Proposition {
        return Proposition("l")
    }
    
    func lambda(_ automatonStates: [Proposition], states: [Proposition]) -> FunctionApplication {
        return FunctionApplication(function: lambdaProposition(), application: automatonStates + states)
    }
    
    func lambdaSharpProposition() -> Proposition {
        return Proposition("ls")
    }
    
    func lambdaSharp(_ automatonStates: [Proposition], states: [Proposition]) -> FunctionApplication {
        return FunctionApplication(function: lambdaSharpProposition(), application: automatonStates + states)
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
