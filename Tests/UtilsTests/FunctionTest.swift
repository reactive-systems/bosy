import XCTest

import Utils

class FunctionTest: XCTestCase {
    
    func testNumBitsNeeded() {
        XCTAssertEqual(numBitsNeeded(0), 0, "bits(0) = 0")
        XCTAssertEqual(numBitsNeeded(1), 1, "bits(1) = 1")
        XCTAssertEqual(numBitsNeeded(2), 1, "bits(2) = 1")
        XCTAssertEqual(numBitsNeeded(3), 2, "bits(3) = 2")
        XCTAssertEqual(numBitsNeeded(4), 2, "bits(4) = 2")
        XCTAssertEqual(numBitsNeeded(5), 3, "bits(5) = 3")
        XCTAssertEqual(numBitsNeeded(8), 3, "bits(8) = 3")
        XCTAssertEqual(numBitsNeeded(9), 4, "bits(9) = 4")
        XCTAssertEqual(numBitsNeeded(16), 4, "bits(16) = 4")
        XCTAssertEqual(numBitsNeeded(17), 5, "bits(17) = 5")
        XCTAssertEqual(numBitsNeeded(32), 5, "bits(32) = 5")
    }
    
    static var allTests : [(String, (FunctionTest) -> () throws -> Void)] {
        return [
            ("testNumBitsNeeded", testNumBitsNeeded),
        ]
    }
}
