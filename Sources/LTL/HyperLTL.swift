
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
        case (_, .application(_, parameters: let parameters)):
            // and afterwards an application...
            return parameters.reduce(true, { res, ltl in res && ltl._isHyperLTL(header: false) })
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
        precondition(isHyperLTL)
        return _getPathVariables()
    }

    private func _getPathVariables() -> [LTLPathVariable] {
        switch self {
        case .pathQuantifier(_, parameters: let variables, body: let body):
            return variables + body._getPathVariables()
        default:
            return []
        }
    }
}
