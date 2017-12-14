// swift-tools-version:4.0
import PackageDescription

let package = Package(
    name: "BoSy",
    products: [
        .executable(name: "BoSy", targets: ["BoSy"]),
    ],
    dependencies: [
        .package(url: "https://github.com/apple/swift-package-manager.git", from: "0.1.0"),
        .package(url: "https://github.com/ltentrup/CAiger.git", from: "0.1.0"),
        .package(url: "https://github.com/ltentrup/SafetySynth.git", from: "0.2.0"),
        .package(url: "https://github.com/ltentrup/CUDD.git", from: "0.2.0"),
    ],
    targets: [
        .target(name: "BoSy", dependencies: ["Automata", "LTL", "Logic", "Utils", "TransitionSystem", "Specification", "BoundedSynthesis"]),
        .target(name: "BoundedSynthesis", dependencies: ["Automata", "LTL", "Logic", "Utils", "TransitionSystem", "Specification"]),
        .testTarget(name: "BoundedSynthesisTests", dependencies: ["BoundedSynthesis"]),
        .target(name: "TransitionSystem", dependencies: ["Logic", "Utils", "Specification", "SafetySynth"]),
        .target(name: "Automata", dependencies: ["Logic", "Utils", "Utility"]),
        .testTarget(name: "AutomataTests", dependencies: ["Automata"]),
        .target(name: "Specification", dependencies: ["Logic", "Utils", "Utility"]),
        .target(name: "Logic", dependencies: ["Utils", "CAiger", "CUDD", "Utility"]),
        .testTarget(name: "LogicTests", dependencies: ["Logic"]),
        .target(name: "LTL"),
        .testTarget(name: "LTLTests", dependencies: ["LTL"]),
        .target(name: "Utils"),
        .testTarget(name: "UtilsTests", dependencies: ["Utils"]),
    ]
)
