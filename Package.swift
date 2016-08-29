import PackageDescription

let package = Package(
    name: "BoSy",
    targets: [
        Target(name: "BoSy", dependencies: ["Utils"]),
        Target(name: "Utils"),
    ],
    dependencies: [
        .Package(url: "../Aiger", majorVersion: 0),
        .Package(url: "https://github.com/czechboy0/Jay.git", majorVersion: 0, minor: 19),
    ]
)
