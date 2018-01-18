// swift-tools-version:4.0
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
        .package(url: "https://github.com/apple/swift-package-manager.git", from: "0.1.0"),
        .package(url: "https://github.com/ltentrup/CAiger.git", from: "0.1.3"),
        .package(url: "https://github.com/ltentrup/SafetySynth.git", from: "0.3.1"),
        .package(url: "https://github.com/ltentrup/CUDD.git", from: "0.2.4"),
    ],
    targets: [
        .target(name: "BoSy", dependencies: ["Automata", "LTL", "Logic", "Utils", "TransitionSystem", "Specification", "BoundedSynthesis"]),
        .target(name: "BoSyBackend", dependencies: ["Automata", "LTL", "Logic", "Utils", "TransitionSystem", "Specification", "BoundedSynthesis"]),
        .target(name: "BoundedSynthesis", dependencies: ["Automata", "LTL", "Logic", "Utils", "TransitionSystem", "Specification", "SafetyGameSolver", "CUDD"]),
        .testTarget(name: "BoundedSynthesisTests", dependencies: ["BoundedSynthesis"]),
        .target(name: "TransitionSystem", dependencies: ["Specification"]),
        .target(name: "Automata", dependencies: ["Logic"]),
        .testTarget(name: "AutomataTests", dependencies: ["Automata"]),
        .target(name: "Specification", dependencies: ["Logic"]),
        .target(name: "Logic", dependencies: ["Utils", "CAiger", "CUDD", "Utility"]),
        .testTarget(name: "LogicTests", dependencies: ["Logic"]),
        .target(name: "LTL"),
        .testTarget(name: "LTLTests", dependencies: ["LTL"]),
        .target(name: "Utils"),
        .testTarget(name: "UtilsTests", dependencies: ["Utils"]),
        
        // BoSyHyper
        .target(name: "BoSyHyper", dependencies: ["BoundedSynthesis"]),
    ]
)
