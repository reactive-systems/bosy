import XCTest
@testable import LogicTests
@testable import LTLTests
@testable import UtilsTests
@testable import BoundedSynthesisTests

XCTMain([
     testCase(BooleanTest.allTests),
     testCase(FunctionTest.allTests),
     testCase(GraphTest.allTests),
     testCase(LTLTests.allTests),
     testCase(SimpleArbiterTest.allTests),
])
