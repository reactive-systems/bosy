import PackageDescription

let package = Package(
    name: "BoSy",
    targets: [
        Target(name: "BoSy", dependencies: ["Utils"]),
        Target(name: "Utils"),
    ],
    dependencies: [
        .Package(url: "https://github.com/ltentrup/CAiger.git", majorVersion: 0, minor: 1),
        .Package(url: "https://github.com/ltentrup/LTL.git", majorVersion: 0, minor: 1),
    ]
)
