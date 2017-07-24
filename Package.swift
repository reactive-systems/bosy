import PackageDescription

let package = Package(
    name: "BoSy",
    targets: [
        Target(name: "BoSy", dependencies: ["Automata", "LTL", "Logic", "Utils", "TransitionSystem", "Specification", "BoundedSynthesis"]),
        Target(name: "BoundedSynthesis", dependencies: ["Automata", "LTL", "Logic", "Utils", "TransitionSystem", "Specification"]),
        Target(name: "TransitionSystem", dependencies: ["Logic", "Utils", "Specification"]),
        Target(name: "Automata", dependencies: ["Logic", "Utils"]),
        Target(name: "Specification", dependencies: ["Logic", "Utils"]),
        Target(name: "Logic", dependencies: ["Utils"]),
        Target(name: "LTL"),
        Target(name: "Utils"),
    ],
    dependencies: [
        .Package(url: "https://github.com/ltentrup/CAiger.git", majorVersion: 0, minor: 1),
        .Package(url: "https://github.com/ltentrup/SafetySynth.git", majorVersion: 0, minor: 2),
    ]
)
