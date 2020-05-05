@testable import AutomataTests
@testable import BoundedSynthesisTests
@testable import LogicTests
@testable import LTLTests
@testable import UtilsTests
import XCTest

XCTMain([
    testCase(BooleanTest.allTests),
    testCase(FunctionTest.allTests),
    testCase(GraphTest.allTests),
    testCase(LTLTests.allTests),
    testCase(SimpleArbiterTest.allTests),
    testCase(AutomatonTest.allTests),
])
