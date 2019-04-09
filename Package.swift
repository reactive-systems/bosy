// swift-tools-version:4.0
import PackageDescription

let package = Package(
    name: "BoSy",
    products: [
        .executable(name: "BoSy", targets: ["BoSy"]),
        .executable(name: "BoSyHyper", targets: ["BoSyHyper"])
    ],
    dependencies: [
        .package(url: "https://github.com/apple/swift-package-manager.git", from: "0.1.0"),
        .package(url: "https://github.com/ltentrup/CAiger.git", from: "0.1.3"),
        .package(url: "https://github.com/ltentrup/SafetySynth.git", from: "0.3.1"),
        .package(url: "https://github.com/ltentrup/CUDD.git", from: "0.2.4"),
    ],
    targets: [
        .target(name: "BoSy", dependencies: ["BoundedSynthesis"]),
        .target(name: "BoundedSynthesis", dependencies: ["Automata", "LTL", "TransitionSystem", "SafetyGameSolver"]),
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
