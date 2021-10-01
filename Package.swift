// swift-tools-version:5.2
import PackageDescription

let package = Package(
    name: "BoSy",
    products: [
        // The main BoSy executable, opts for the best/easiest synthesis experience
        .executable(name: "BoSy", targets: ["BoSy"]),
        // BoSy executable to only execute one backend (legacy version)
        .executable(name: "BoSyBackend", targets: ["BoSyBackend"]),
        // BoSy executable to synthesize from HyperLTL specifications
        .executable(name: "BoSyHyper", targets: ["BoSyHyper"])
    ],
    dependencies: [
        .package(url: "https://github.com/apple/swift-tools-support-core.git", from: "0.2.3"),
        .package(url: "https://github.com/ltentrup/CAiger.git", from: "0.1.3"),
        .package(url: "https://github.com/ltentrup/SafetySynth.git", from: "0.3.1"),
        .package(url: "https://github.com/ltentrup/CUDD.git", from: "0.2.4"),
    ],
    targets: [
        .target(name: "BoSy", dependencies: ["Automata", "LTL", "Logic", "Utils", "TransitionSystem", "Specification", "BoundedSynthesis"]),
        .target(name: "BoSyBackend", dependencies: ["Automata", "LTL", "Logic", "Utils", "TransitionSystem", "Specification", "BoundedSynthesis"]),
        .target(name: "BoundedSynthesis", dependencies: ["Automata", "LTL", "Logic", "Utils", "TransitionSystem", "Specification", .product(name: "SafetyGameSolver", package: "SafetySynth"), "CUDD"]),
        .testTarget(name: "BoundedSynthesisTests", dependencies: ["BoundedSynthesis"]),
        .target(name: "TransitionSystem", dependencies: ["Specification", .product(name: "SafetyGameSolver", package: "SafetySynth")]),
        .target(name: "Automata", dependencies: ["Logic","LTL"]),
        .testTarget(name: "AutomataTests", dependencies: ["Automata","LTL"]),
        .target(name: "Specification", dependencies: ["Logic"]),
        .target(name: "Logic", dependencies: ["Utils", "CAiger",.product(name: "CAigerHelper", package: "CAiger"), "CUDD",.product(name: "SwiftToolsSupport", package: "swift-tools-support-core")]),
        .testTarget(name: "LogicTests", dependencies: ["Logic"]),
        .target(name: "LTL"),
        .testTarget(name: "LTLTests", dependencies: ["LTL"]),
        .target(name: "Utils"),
        .testTarget(name: "UtilsTests", dependencies: ["Utils"]),
        
        // BoSyHyper
        .target(name: "BoSyHyper", dependencies: ["BoundedSynthesis"]),
    ]
)
