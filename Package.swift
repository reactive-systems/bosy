import PackageDescription

let package = Package(
    name: "BoSy",
    targets: [
        Target(name: "BoSy", dependencies: ["Utils"]),
        Target(name: "Utils"),
    ],
    dependencies: [
        .Package(url: "../CAiger", majorVersion: 0, minor: 1),
        .Package(url: "../LTL", majorVersion: 0, minor: 1),
    ]
)
