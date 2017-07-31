
import XCTest

import Specification
import LTL

@testable import BoundedSynthesis

class SimpleArbiterTest: XCTestCase {
    
    let jsonSpec = "{\"semantics\": \"mealy\", \"inputs\": [\"r_0\", \"r_1\", \"r_2\"], \"outputs\": [\"g_0\", \"g_1\", \"g_2\"], \"assumptions\": [], \"guarantees\": [\"(G (((! (g_0)) && (! (g_1))) || (((! (g_0)) || (! (g_1))) && (! (g_2)))))\", \"(G ((r_0) -> (F (g_0))))\", \"(G ((r_1) -> (F (g_1))))\", \"(G ((r_2) -> (F (g_2))))\"] }"
    
    var options = BoSyOptions()
    
    func testRealizabilityInputSymbolic() {
        options.solver = .rareqs
        options.qbfPreprocessor = .bloqqer
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, LTL.BinaryOperator(.Implies,
                                         specification.assumptions.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) }),
                                         specification.guarantees.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) })))
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = InputSymbolicEncoding(options: options, automaton: automaton, specification: specification, synthesize: false)
        XCTAssertFalse(try encoding.solve(forBound: 2))
        XCTAssertTrue(try encoding.solve(forBound: 3))
        XCTAssertTrue(try encoding.solve(forBound: 4))
    }
    
    func testRealizabilityExplicit() {
        options.solver = .picosat
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, LTL.BinaryOperator(.Implies,
                                                                 specification.assumptions.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) }),
                                                                 specification.guarantees.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) })))
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = ExplicitEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertFalse(try encoding.solve(forBound: 2))
        XCTAssertTrue(try encoding.solve(forBound: 3))
        XCTAssertTrue(try encoding.solve(forBound: 4))
    }
    
    func testRealizabilitySmt() {
        options.solver = .z3
        guard let specification = SynthesisSpecification.fromJson(string: jsonSpec) else {
            XCTFail()
            fatalError()
        }
        let ltlSpec = LTL.UnaryOperator(.Not, LTL.BinaryOperator(.Implies,
                                                                 specification.assumptions.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) }),
                                                                 specification.guarantees.reduce(LTL.Literal(true), { res, ltl in .BinaryOperator(.And, res, ltl) })))
        guard let automaton = options.converter.convert(ltl: ltlSpec.description) else {
            XCTFail()
            fatalError()
        }
        var encoding = SmtEncoding(options: options, automaton: automaton, specification: specification)
        XCTAssertFalse(try encoding.solve(forBound: 2))
        XCTAssertTrue(try encoding.solve(forBound: 3))
        XCTAssertTrue(try encoding.solve(forBound: 4))
    }
    
    static var allTests : [(String, (SimpleArbiterTest) -> () throws -> Void)] {
        return [
            ("testRealizabilityInputSymbolic", testRealizabilityInputSymbolic),
            ("testRealizabilityExplicit", testRealizabilityExplicit),
            ("testRealizabilitySmt", testRealizabilitySmt),
        ]
    }
}
