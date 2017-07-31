import LTL
import Logic
import Specification

struct Unrolling {
    let specification: SynthesisSpecification
    
    func getEncoding(forBound bound: Int) -> Logic? {
        var ltl: LTL = specification.guarantees.reduce(.Literal(true), { val, element in .BinaryOperator(.And, val, element) })
        if specification.assumptions.count > 0 {
            let assumptions: LTL = specification.assumptions.reduce(.Literal(true), { val, element in .BinaryOperator(.And, val, element) })
            ltl = .BinaryOperator(.Implies, assumptions, ltl)
        }
        //print(ltl)
        ltl = ltl.normalized.nnf
        //print(ltl)
        
        let atLeastOneLoop = (0..<bound).map({ i in loop(step: i) }).reduce(Literal.False, |)
        let atMostOneLoop = (0..<bound).map({
            i in
            (0..<i).map({ j in loop(step: j) }).reduce(Literal.False, |) --> !loop(step: i)
        }).reduce(Literal.True, &)
        
        let loopConstraint = atLeastOneLoop & atMostOneLoop
        
        let atLeastOneLeaf = (1...bound).map({ i in leaf(step: i) }).reduce(Literal.False, |)
        let atMostOneLeaf = (1...bound).map({
            i in
            (1..<i).map({ j in leaf(step: j) }).reduce(Literal.False, |) --> !leaf(step: i)
        }).reduce(Literal.True, &)
        
        let loopBeforeLeaf = (1...bound).map({
            i in
            (0..<i).map({ j in !loop(step: j) }).reduce(Literal.True, &) --> !leaf(step: i)
        }).reduce(Literal.True, &)
        
        let leafConstraint = atLeastOneLeaf & atMostOneLeaf & loopBeforeLeaf
        
        let formulaUnrolling = unrolling(ltl: ltl, max: bound, current: 0)
        
        let constraints = loopConstraint & leafConstraint & formulaUnrolling
        var qbf = Quantifier(.Exists, variables: (0..<bound).map({ i in loop(step: i) }) + (0...bound).map({ i in leaf(step: i) }), scope: constraints)
        for i in (0..<bound).reversed() {
            qbf = Quantifier(.Forall, variables: specification.inputs.map({ proposition(name: $0, step: i) }), scope:
                Quantifier(.Exists, variables:  specification.outputs.map({ proposition(name: $0, step: i) }), scope: qbf)
            )
        }
        //print(qbf)
        //print(formulaUnrolling)
        
        let boundednessCheck = BoundednessVisitor()
        assert(qbf.accept(visitor: boundednessCheck))
        
        /*let dimacsVisitor = DIMACSVisitor(formula: qbf)
        //print(dimacsVisitor)
        
        guard let (result, assignments) = cryptominisat(dimacs: "\(dimacsVisitor)") else {
            return nil
        }
        
        
        if result == .SAT {
            // keep top level valuations of solver
            let assignments = dimacsVisitor.getAssignment(fromAssignment: assignments!)
            print(assignments)
            //return nil
        }*/
        
        return qbf
    }
    
    func loop(step: Int) -> Proposition {
        return Proposition("loop_\(step)")
    }
    
    func leaf(step: Int) -> Proposition {
        return Proposition("leaf_\(step)")
    }
    
    func proposition(name: String, step: Int) -> Proposition {
        return Proposition("\(name)_\(step)")
    }
    
    func unrolling(ltl: LTL, max: Int, current: Int, inLoop: Bool = false) -> Logic {
        precondition(current <= max)
        switch ltl {
        case .Literal(let val):
            return val ? Literal.True : Literal.False
        case .Proposition(let name):
            if current == max {
                return leaf(step: current) & (0..<max).map({ proposition(name: name, step: $0) & loop(step: $0) }).reduce(Literal.False, |)
            } else {
                return (!leaf(step: current) --> proposition(name: name, step: current))
                    & (leaf(step: current) --> (0..<current).map({ proposition(name: name, step: $0) & loop(step: $0) }).reduce(Literal.False, |))
            }
            /*if current == max {
                return (0..<max).map({ proposition(name: name, step: $0) & loop(step: $0) }).reduce(Literal.False, |)
            } else {
                return proposition(name: name, step: current)
            }*/
        case .UnaryOperator(.Not, .Proposition(let name)):
            if current == max {
                return leaf(step: current) & (0..<max).map({ !proposition(name: name, step: $0) & loop(step: $0) }).reduce(Literal.False, |)
            } else {
                return (!leaf(step: current) --> !proposition(name: name, step: current))
                    & (leaf(step: current) --> (0..<current).map({ !proposition(name: name, step: $0) & loop(step: $0) }).reduce(Literal.False, |))
            }
            /*if current == max {
                return (0..<max).map({ !proposition(name: name, step: $0) & loop(step: $0) }).reduce(Literal.False, |)
            } else {
                return !proposition(name: name, step: current)
            }*/
        case .BinaryOperator(.Release, let lhs, let rhs):
            if current == max {
                if inLoop {
                    return Literal.True
                }
                return leaf(step: current) & (0..<max).map({ loop(step: $0) & unrolling(ltl: ltl, max: max, current: $0, inLoop: true) }).reduce(Literal.False, |)
            } else {
                if inLoop {
                    return (!leaf(step: current) --> (unrolling(ltl: rhs, max: max, current: current)
                        & (unrolling(ltl: lhs, max: max, current: current) | unrolling(ltl: ltl, max: max, current: current + 1, inLoop: inLoop)))) &
                        (leaf(step: current) --> Literal.True)
                }
                return (!leaf(step: current) --> (unrolling(ltl: rhs, max: max, current: current)
                    & (unrolling(ltl: lhs, max: max, current: current) | unrolling(ltl: ltl, max: max, current: current + 1, inLoop: inLoop)))) &
                       (leaf(step: current) --> (0..<current).map({ loop(step: $0) & unrolling(ltl: ltl, max: max, current: $0, inLoop: true) }).reduce(Literal.False, |))
            }
            /*if current == max {
                if inLoop {
                    return Literal.True
                }
                return (0..<max).map({ loop(step: $0) & unrolling(ltl: ltl, max: max, current: $0, inLoop: true) }).reduce(Literal.False, |)
            } else {
                return unrolling(ltl: rhs, max: max, current: current)
                     & (unrolling(ltl: lhs, max: max, current: current) | unrolling(ltl: ltl, max: max, current: current + 1, inLoop: inLoop))
            }*/
        case .BinaryOperator(.Until, let lhs, let rhs):
            if current == max {
                if inLoop {
                    return Literal.False
                }
                return leaf(step: current) & (0..<max).map({ loop(step: $0) & unrolling(ltl: ltl, max: max, current: $0, inLoop: true) }).reduce(Literal.False, |)
            } else {
                if inLoop {
                    return (!leaf(step: current) --> (unrolling(ltl: rhs, max: max, current: current)
                        | (unrolling(ltl: lhs, max: max, current: current) & unrolling(ltl: ltl, max: max, current: current + 1, inLoop: inLoop)))) &
                           (leaf(step: current) --> Literal.False)
                }
                return (!leaf(step: current) --> (unrolling(ltl: rhs, max: max, current: current)
                    | (unrolling(ltl: lhs, max: max, current: current) & unrolling(ltl: ltl, max: max, current: current + 1, inLoop: inLoop)))) &
                       (leaf(step: current) --> (0..<current).map({ loop(step: $0) & unrolling(ltl: ltl, max: max, current: $0, inLoop: true) }).reduce(Literal.False, |))
            }
            /*if current == max {
                if inLoop {
                    return Literal.False
                }
                return (0..<max).map({ loop(step: $0) & unrolling(ltl: ltl, max: max, current: $0, inLoop: true) }).reduce(Literal.False, |)
            } else {
                return unrolling(ltl: rhs, max: max, current: current)
                    | (unrolling(ltl: lhs, max: max, current: current) & unrolling(ltl: ltl, max: max, current: current + 1, inLoop: inLoop))
            }*/
        case .BinaryOperator(.And, let lhs, let rhs):
            return unrolling(ltl: lhs, max: max, current: current) & unrolling(ltl: rhs, max: max, current: current)
        case .BinaryOperator(.Or, let lhs, let rhs):
            return unrolling(ltl: lhs, max: max, current: current) |
                unrolling(ltl: rhs, max: max, current: current)
        case .UnaryOperator(.Next, let scope):
            if current == max {
                return Literal.False
            }
            return (!leaf(step: current+1) --> unrolling(ltl: scope, max: max, current: current + 1))
                 & (leaf(step: current+1) --> (0...current).map({ loop(step: $0) & unrolling(ltl: scope, max: max, current: $0 ) }).reduce(Literal.False, |))
            /*if current == max - 1 {
                return (0..<max-1).map({ loop(step: $0) & unrolling(ltl: scope, max: max, current: $0 + 1) }).reduce(Literal.False, |)
            } else {
                assert(current < max - 1)
                return unrolling(ltl: scope, max: max, current: current + 1)
            }*/
        default:
            assert(false)
            return Literal.True
        }
    }
}
