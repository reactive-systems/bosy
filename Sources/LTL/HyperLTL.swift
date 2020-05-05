
/**
 * HyperLTL is represented as an LTL enum.
 * This file contains helper functions to work with quantifiers in LTL
 */
extension LTL {
    public var isHyperLTL: Bool {
        // a HyperLTL formula starts with a quantifier
        guard case .pathQuantifier(_, parameters: _, body: let body) = self else {
            return false
        }
        return body._isHyperLTL(header: true)
    }

    private func _isHyperLTL(header: Bool) -> Bool {
        switch (header, self) {
        case (true, .pathQuantifier(_, parameters: _, body: let body)):
            // we may have an arbitrary long quantifier prefix
            return body._isHyperLTL(header: true)
        case let (_, .application(_, parameters: parameters)):
            // and afterwards an application...
            return parameters.reduce(true) { res, ltl in res && ltl._isHyperLTL(header: false) }
        case (_, .pathProposition(_, _)):
            // ...or a path proposition
            return true
        case (_, .atomicProposition(_)):
            // but no propositions without path variable
            return false
        default:
            // and especially no quantifiers below
            return false
        }
    }

    /**
     * Contains a quantifier.
     */
    public var isHyper: Bool {
        switch self {
        case .pathQuantifier(_, parameters: _, body: _):
            return true
        case let .application(_, parameters: paramters):
            return paramters.reduce(false) { val, paramter in val || paramter.isHyper }
        default:
            return false
        }
    }

    public var ltlBody: LTL {
        precondition(isHyperLTL)
        return _getLTLBody()
    }

    private func _getLTLBody() -> LTL {
        if case .pathQuantifier(_, parameters: _, body: let body) = self {
            return body._getLTLBody()
        } else {
            return self
        }
    }

    public var pathVariables: [LTLPathVariable] {
        precondition(isHyper)
        return _getPathVariables()
    }

    private func _getPathVariables() -> [LTLPathVariable] {
        switch self {
        case let .pathQuantifier(_, parameters: variables, body: body):
            return variables + body._getPathVariables()
        default:
            return []
        }
    }

    public var isUniversal: Bool {
        // precondition(isNNF)
        switch self {
        case .pathQuantifier(let quantifier, parameters: _, body: let body):
            return quantifier == .forall && body.isUniversal
        case let .application(_, parameters: parameters):
            return parameters.reduce(true) { val, parameter in val && parameter.isUniversal }
        default:
            return true
        }
    }

    /**
     * Moves quantifier to the front.
     * Does it in a way to not introduce new quantifier.
     * This function assumes the formula in negation normal form and does not allow existential quantification.
     */
    public var prenex: LTL {
        // precondition(isNNF)
        precondition(isUniversal)
        guard case let .application(.and, parameters: parameters) = self else {
            fatalError("not implemented")
        }
        let pathVariables = parameters[0].pathVariables
        let body = parameters.reduce(.tt) { val, ltl in val && ltl.toPrenex(free: pathVariables, mapping: [:]) }
        return .pathQuantifier(.forall, parameters: pathVariables, body: body)
    }

    private func toPrenex(free: [LTLPathVariable], mapping: [LTLPathVariable: LTLPathVariable]) -> LTL {
        switch self {
        case let .pathQuantifier(quantifier, parameters: parameters, body: body):
            assert(quantifier == .forall)
            var copy = ArraySlice(free)
            var newMapping = mapping
            for parameter in parameters {
                assert(mapping[parameter] == nil)
                guard let mapped = copy.popFirst() else {
                    fatalError()
                }
                newMapping[parameter] = mapped
            }
            return body.toPrenex(free: copy.map { $0 }, mapping: newMapping)
        case let .application(function, parameters: parameters):
            return .application(function, parameters: parameters.map { $0.toPrenex(free: free, mapping: mapping) })
        case let .pathProposition(prop, pathVar):
            guard let newPathVar = mapping[pathVar] else {
                fatalError()
            }
            return .pathProposition(prop, newPathVar)
        default:
            fatalError()
        }
    }

    /**
     * For a given LTL formula, replace all atomic propositions by path propositions.
     */
    public func addPathPropositions(path: LTLPathVariable) -> LTL {
        switch self {
        case let .atomicProposition(prop):
            return .pathProposition(prop, path)
        case let .application(function, parameters: parameters):
            return .application(function, parameters: parameters.map { $0.addPathPropositions(path: path) })
        default:
            fatalError()
        }
    }

    /**
     * Replaces path variables in pathPropositions according to given mapping
     */
    public func replacePathProposition(mapping: [LTLPathVariable: LTLPathVariable]) -> LTL {
        switch self {
        case let .pathProposition(prop, variable):
            guard let newVariable = mapping[variable] else {
                fatalError("\(variable) not contained in mapping")
            }
            return .pathProposition(prop, newVariable)
        case let .application(function, parameters: parameters):
            return .application(function, parameters: parameters.map { $0.replacePathProposition(mapping: mapping) })
        default:
            fatalError()
        }
    }
}
