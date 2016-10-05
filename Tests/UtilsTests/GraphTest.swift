import XCTest

import Utils

class GraphTest: XCTestCase {
    
    func testTrajan() {
        let g = Graph(
            states: Set<String>(arrayLiteral:"a", "b", "c", "d", "e", "f", "g", "h"),
            edges: ["a":["b"], "b":["c"], "c":["a"], "d":["b", "c", "e"], "e":["d", "f"], "f":["c", "g"], "g":["f"], "h":["e", "g", "h"]]
        )
        let sccs = trajan(graph: g)
        XCTAssertEqual(sccs.count, 4, "graph has 4 SCC")
    }
    
    static var allTests : [(String, (GraphTest) -> () throws -> Void)] {
        return [
            ("testTrajan", testTrajan),
        ]
    }
}
