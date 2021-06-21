import Foundation
import TSCBasic
import TSCUtility
import Utils

import CAiger

public enum SolverResult {
    case sat
    case unsat
}

public enum SolverInstance: String {
    // SAT solver
    case picosat
    case cryptominisat

    // QBF solver
    case rareqs
    case depqbf
    case caqe
    case cadet
    case quabs

    // DQBF solver
    case idq
    case hqs
    case dcaqe

    // FO solver
    case eprover
    case vampire

    // SMT solver
    case z3
    case cvc4

    public var instance: Solver {
        switch self {
        case .picosat:
            return PicoSAT()
        case .cryptominisat:
            return CryptoMiniSat()
        case .rareqs:
            return RAReQS()
        case .depqbf:
            return DepQBF()
        case .cadet:
            return CADET()
        case .caqe:
            return CAQE()
        case .quabs:
            return QuAbS()
        case .idq:
            return iDQ()
        case .hqs:
            return HQS()
        case .dcaqe:
            return DCAQE()
        case .eprover:
            return Eprover()
        case .vampire:
            return Vampire()
        case .z3:
            return Z3()
        case .cvc4:
            return CVC4()
        }
    }

    public static let allValues: [SolverInstance] = [
        .picosat,
        .cryptominisat,
        .rareqs,
        .depqbf,
        .cadet,
        .caqe,
        .quabs,
        .idq,
        .hqs,
        .dcaqe,
        .eprover,
        .vampire,
        .z3,
        .cvc4,
    ]
}

public enum QBFPreprocessorInstance: String {
    case bloqqer
    case hqspre

    public func getInstance(preserveAssignments: Bool) -> QbfPreprocessor {
        switch self {
        case .bloqqer:
            return Bloqqer(preserveAssignments: preserveAssignments)
        case .hqspre:
            return HQSPre()
        }
    }

    public static let allValues: [QBFPreprocessorInstance] = [
        .bloqqer,
        .hqspre,
    ]
}

public enum SatSolverResult {
    case unsat
    case sat(assignment: BooleanAssignment)
}

public enum QbfSolverResult {
    case unsat
    case sat(functions: [Proposition: Logic])
}

public protocol Solver {}

public protocol SatSolver: Solver {
    func solve(formula: Logic) -> SatSolverResult?
}

public protocol QbfPreprocessor {
    func preprocess(qbf: String) -> String?
}

public protocol QbfSolver: Solver {
    func solve(formula: Logic, preprocessor: QbfPreprocessor?) -> SatSolverResult?
}

public protocol CertifyingQbfSolver: Solver {
    func solve(formula: Logic) -> QbfSolverResult?
}

public protocol SmtSolver: Solver {
    func solve(formula: String) -> SolverResult?
    func getValue(expression: String) -> Logic?
    func getIntValue(name: String) -> Int?
}

public protocol DqbfSolver: Solver {
    func solve(formula: Logic, preprocessor: QbfPreprocessor?) -> SolverResult?
}

private enum SolverHelper {
    static func getDimacsAssignments(stdout: String) -> [Int] {
        var assignments: [Int] = []
        for line in stdout.components(separatedBy: "\n") {
            if !line.hasPrefix("v"), !line.hasPrefix("V") {
                continue
            }
            assignments += String(line[line.index(after: line.startIndex) ..< line.endIndex])
                .trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines)
                .components(separatedBy: " ")
                .compactMap { Int($0) }
        }
        return assignments
    }

    static func executeAndReturnStdout(task: Foundation.Process) -> String? {
        let stdoutPipe = Pipe()
        let stderrPipe = Pipe()
        task.standardOutput = stdoutPipe
        task.standardError = stderrPipe
        task.launch()

        // there may be a large amount of stdout data
        // by reading it before waiting, we avoid deadlocks
        let stdoutHandle = stdoutPipe.fileHandleForReading
        let stdoutData = StreamHelper.readAllAvailableData(from: stdoutHandle)

        task.waitUntilExit()

        guard let stdout = String(data: stdoutData, encoding: String.Encoding.utf8) else {
            return nil
        }
        return stdout
    }

    static func result(from exitCode: Int32) -> SolverResult? {
        switch exitCode {
        case 10:
            return .sat
        case 20:
            return .unsat
        default:
            return nil
        }
    }

    static func result(from exitStatus: ProcessResult.ExitStatus) -> SolverResult? {
        switch exitStatus {
        case let .terminated(code: code):
            return result(from: code)
        default:
            return nil
        }
    }
}

struct PicoSAT: SatSolver {
    func solve(formula: Logic) -> SatSolverResult? {
        // encode formula
        let dimacsVisitor = DIMACSVisitor(formula: formula)
        let encodedFormula = dimacsVisitor.description

        // start task and extract stdout
        do {
            let (stdout, result) = try withTemporaryFile(dir: nil, prefix: "", suffix: ".dimacs", deleteOnClose: true) {
                (tempFile: TemporaryFile) throws -> (String, ProcessResult) in
                tempFile.fileHandle.write(Data(encodedFormula.utf8))
                let result = try TSCBasic.Process.popen(arguments: ["./Tools/picosat-solver", tempFile.path.pathString])
                let stdout = try result.utf8Output()
                return (stdout, result)
            }

            guard let solverResult = SolverHelper.result(from: result.exitStatus) else {
                return nil
            }

            if solverResult == .unsat {
                return .unsat
            }
            let assignments = SolverHelper.getDimacsAssignments(stdout: stdout)
            return .sat(assignment: dimacsVisitor.getAssignment(fromAssignment: assignments))

        } catch {
            Logger.default().error("execution of picosat failed")
            return nil
        }
    }
}

struct CryptoMiniSat: SatSolver {
    func solve(formula: Logic) -> SatSolverResult? {
        // encode formula
        let dimacsVisitor = DIMACSVisitor(formula: formula)
        let encodedFormula = dimacsVisitor.description

        // start task and extract stdout
        do {
            let (stdout, result) = try withTemporaryFile(dir: nil, prefix: "", suffix: ".dimacs", deleteOnClose: true) {
                (tempFile: TemporaryFile) throws -> (String, ProcessResult) in
                tempFile.fileHandle.write(Data(encodedFormula.utf8))
                let result = try TSCBasic.Process.popen(arguments: ["./Tools/cryptominisat5", "--verb=0", tempFile.path.pathString])
                let stdout = try result.utf8Output()
                return (stdout, result)
            }

            guard let solverResult = SolverHelper.result(from: result.exitStatus) else {
                return nil
            }

            if solverResult == .unsat {
                return .unsat
            }
            let assignments = SolverHelper.getDimacsAssignments(stdout: stdout)
            return .sat(assignment: dimacsVisitor.getAssignment(fromAssignment: assignments))

        } catch {
            Logger.default().error("execution of cryptominisat failed")
            return nil
        }
    }
}

struct RAReQS: QbfSolver {
    func solve(formula: Logic, preprocessor: QbfPreprocessor?) -> SatSolverResult? {
        // encode formula
        let qdimacsVisitor = QDIMACSVisitor(formula: formula)
        var encodedFormula = qdimacsVisitor.description

        if let preprocessor = preprocessor {
            guard let preprocessedFormula = preprocessor.preprocess(qbf: encodedFormula) else {
                return nil
            }
            encodedFormula = preprocessedFormula
        }

        // start task and extract stdout
        do {
            let (stdout, result) = try withTemporaryFile(dir: nil, prefix: "", suffix: ".qdimacs", deleteOnClose: true) {
                (tempFile: TemporaryFile) throws -> (String, ProcessResult) in
                tempFile.fileHandle.write(Data(encodedFormula.utf8))
                let result = try TSCBasic.Process.popen(arguments: ["./Tools/rareqs", tempFile.path.pathString])
                let stdout = try result.utf8Output()
                return (stdout, result)
            }

            guard let solverResult = SolverHelper.result(from: result.exitStatus) else {
                return nil
            }

            if solverResult == .unsat {
                return .unsat
            }
            let assignments = SolverHelper.getDimacsAssignments(stdout: stdout)
            return .sat(assignment: qdimacsVisitor.getAssignment(fromAssignment: assignments))

        } catch {
            Logger.default().error("execution of rareqs failed")
            return nil
        }
    }
}

struct DepQBF: QbfSolver {
    func solve(formula: Logic, preprocessor: QbfPreprocessor?) -> SatSolverResult? {
        // encode formula
        let qdimacsVisitor = QDIMACSVisitor(formula: formula)
        var encodedFormula = qdimacsVisitor.description

        if let preprocessor = preprocessor {
            guard let preprocessedFormula = preprocessor.preprocess(qbf: encodedFormula) else {
                return nil
            }
            encodedFormula = preprocessedFormula
        }

        // start task and extract stdout
        do {
            let (stdout, result) = try withTemporaryFile(dir: nil, prefix: "", suffix: ".qdimacs", deleteOnClose: true) {
                (tempFile: TemporaryFile) throws -> (String, ProcessResult) in
                tempFile.fileHandle.write(Data(encodedFormula.utf8))
                let result = try TSCBasic.Process.popen(arguments: ["./Tools/depqbf", "--qdo", tempFile.path.pathString])
                let stdout = try result.utf8Output()
                return (stdout, result)
            }

            guard let solverResult = SolverHelper.result(from: result.exitStatus) else {
                return nil
            }

            if solverResult == .unsat {
                return .unsat
            }
            let assignments = SolverHelper.getDimacsAssignments(stdout: stdout)
            return .sat(assignment: qdimacsVisitor.getAssignment(fromAssignment: assignments))

        } catch {
            Logger.default().error("execution of depqbf failed")
            return nil
        }
    }
}

struct Bloqqer: QbfPreprocessor {
    let preserveAssignments: Bool

    init(preserveAssignments: Bool) {
        self.preserveAssignments = preserveAssignments
    }

    func preprocess(qbf: String) -> String? {
        do {
            let stdout = try withTemporaryFile(dir: nil, prefix: "", suffix: ".qdimacs", deleteOnClose: true) {
                (tempFile: TemporaryFile) throws -> String in
                let arguments = preserveAssignments ?
                    ["./Tools/bloqqer", "--partial-assignment=1", "--keep=1", tempFile.path.pathString] :
                    ["./Tools/bloqqer-031", "--keep=1", tempFile.path.pathString]
                tempFile.fileHandle.write(Data(qbf.utf8))
                let result = try TSCBasic.Process.popen(arguments: arguments)
                let stdout = try result.utf8Output()
                return stdout
            }
            return stdout
        } catch {
            Logger.default().error("execution of bloqqer failed")
            return nil
        }
    }
}

struct HQSPre: QbfPreprocessor {
    func preprocess(qbf: String) -> String? {
        do {
            let fileout = try withTemporaryFile(dir: nil, prefix: "", suffix: ".qdimacs", deleteOnClose: true) {
                (tempFile: TemporaryFile) throws -> String? in
                let fileout = try withTemporaryFile(dir: nil, prefix: "", suffix: ".qdimacs", deleteOnClose: true) {
                    (outFile: TemporaryFile) throws -> String? in

                    tempFile.fileHandle.write(Data(qbf.utf8))
                    _ = try TSCBasic.Process.popen(arguments: ["./Tools/hqspre-linux", "-o", outFile.path.pathString, tempFile.path.pathString])
                    let fileout = try? String(contentsOfFile: outFile.path.pathString, encoding: String.Encoding.utf8)
                    return fileout
                }
                return fileout
            }
            return fileout
        } catch {
            Logger.default().error("execution of hqspre failed")
            return nil
        }
    }
}

struct CAQE: QbfSolver /*CertifyingQbfSolver*/ { //current caqe version doesn't certify
    func solve(formula: Logic, preprocessor: QbfPreprocessor?) -> SatSolverResult? {
        // encode formula
        let qdimacsVisitor = QDIMACSVisitor(formula: formula)
        var encodedFormula = qdimacsVisitor.description

        if let preprocessor = preprocessor {
            guard let preprocessedFormula = preprocessor.preprocess(qbf: encodedFormula) else {
                return nil
            }
            encodedFormula = preprocessedFormula
        }

        // start task and extract stdout
        do {
            let (stdout, result) = try withTemporaryFile(dir: nil, prefix: "", suffix: ".qdimacs", deleteOnClose: true) {
                (tempFile: TemporaryFile) throws -> (String, ProcessResult) in
                tempFile.fileHandle.write(Data(encodedFormula.utf8))
                let result = try TSCBasic.Process.popen(arguments: ["./Tools/caqe", "--qdo", tempFile.path.pathString])
                let stdout = try result.utf8Output()
                return (stdout, result)
            }

            guard let solverResult = SolverHelper.result(from: result.exitStatus) else {
                return nil
            }

            if solverResult == .unsat {
                return .unsat
            }
            let assignments = SolverHelper.getDimacsAssignments(stdout: stdout)
            return .sat(assignment: qdimacsVisitor.getAssignment(fromAssignment: assignments))

        } catch {
            Logger.default().error("execution of caqe failed")
            return nil
        }
    }

    func solve(formula: Logic) -> QbfSolverResult? {
        let qdimacsVisitor = QDIMACSVisitor(formula: formula)
        let encodedFormula = qdimacsVisitor.description

        return try? withTemporaryFile(dir: nil, prefix: "", suffix: ".qdimacs", deleteOnClose: true) {
            (tempFile: TemporaryFile) throws -> QbfSolverResult? in
            tempFile.fileHandle.write(Data(encodedFormula.utf8))
            let task = Process()
            task.launchPath = "./Tools/caqem"
            task.arguments = ["-c", tempFile.path.pathString]

            let stdoutPipe = Pipe()
            let stderrPipe = Pipe()
            task.standardOutput = stdoutPipe
            task.standardError = stderrPipe
            task.launch()

            let stdoutHandle = stdoutPipe.fileHandleForReading
            let file = fdopen(stdoutHandle.fileDescriptor, "r")
            guard let aiger = aiger_init() else {
                return nil
            }
            let error = aiger_read_from_file(aiger, file)
            fclose(file)
            if error != nil {
                // print(String(cString: aiger_error(aiger)))
                return nil
            }

            task.waitUntilExit()

            guard let result = SolverHelper.result(from: task.terminationStatus) else {
                return nil
            }
            if result != .sat {
                return .unsat
            }

            guard let minimizedCertificate = aiger.minimized else {
                Logger.default().error("could not minimize certificate with ABC")
                return nil
            }
            aiger_reset(aiger)
            let functions = qdimacsVisitor.translate(certificate: minimizedCertificate)
            aiger_reset(minimizedCertificate)
            return .sat(functions: functions)
        }
    }
}

struct QuAbS: CertifyingQbfSolver {
    func solve(formula: Logic) -> QbfSolverResult? {
        let qcirVisitor = QCIRVisitor(formula: formula)
        let encodedFormula = qcirVisitor.description

        return try? withTemporaryFile(dir: nil, prefix: "", suffix: ".qcir", deleteOnClose: true) {
            (tempFile: TemporaryFile) throws -> QbfSolverResult? in
            tempFile.fileHandle.write(Data(encodedFormula.utf8))

            let task = Process()
            task.launchPath = "./Tools/quabs"
            task.arguments = ["-c", tempFile.path.pathString]

            let stdoutPipe = Pipe()
            let stderrPipe = Pipe()
            task.standardOutput = stdoutPipe
            task.standardError = stderrPipe
            task.launch()

            let stdoutHandle = stdoutPipe.fileHandleForReading
            let file = fdopen(stdoutHandle.fileDescriptor, "r")
            guard let aiger = aiger_init() else {
                return nil
            }
            let error = aiger_read_from_file(aiger, file)
            fclose(file)
            if error != nil {
                // print(String(cString: aiger_error(aiger)))
                return nil
            }

            task.waitUntilExit()

            guard let result = SolverHelper.result(from: task.terminationStatus) else {
                return nil
            }
            if result != .sat {
                return .unsat
            }

            guard let minimizedCertificate = aiger.minimized else {
                Logger.default().error("could not minimize certificate with ABC")
                return nil
            }
            aiger_reset(aiger)
            let functions = qcirVisitor.translate(certificate: minimizedCertificate)
            aiger_reset(minimizedCertificate)

            return .sat(functions: functions)
        }
    }
}

struct CADET: CertifyingQbfSolver {
    func solve(formula: Logic) -> QbfSolverResult? {
        let qdimacsVisitor = QDIMACSVisitor(formula: formula)
        let encodedFormula = qdimacsVisitor.description

        return try? withTemporaryFile(dir: nil, prefix: "", suffix: ".qdimacs", deleteOnClose: true) {
            (tempFile: TemporaryFile) throws -> QbfSolverResult? in
            tempFile.fileHandle.write(Data(encodedFormula.utf8))
            let task = Process()
            task.launchPath = "./Tools/cadet"
            task.arguments = ["-c", "stdout", tempFile.path.pathString]

            let stdoutPipe = Pipe()
            let stderrPipe = Pipe()
            task.standardOutput = stdoutPipe
            task.standardError = stderrPipe
            task.launch()

            let stdoutHandle = stdoutPipe.fileHandleForReading
            let file = fdopen(stdoutHandle.fileDescriptor, "r")
            guard let aiger = aiger_init() else {
                return nil
            }
            let error = aiger_read_from_file(aiger, file)
            fclose(file)
            if error != nil {
                // print(String(cString: aiger_error(aiger)))
                return nil
            }

            task.waitUntilExit()

            guard let result = SolverHelper.result(from: task.terminationStatus) else {
                return nil
            }
            if result != .sat {
                return .unsat
            }

            guard let minimizedCertificate = aiger.minimized else {
                Logger.default().error("could not minimize certificate with ABC")
                return nil
            }
            aiger_reset(aiger)
            let functions = qdimacsVisitor.translate(certificate: minimizedCertificate)
            aiger_reset(minimizedCertificate)

            return .sat(functions: functions)
        }
    }
}

extension UnsafeMutablePointer where Pointee == aiger {
    public var minimized: UnsafeMutablePointer<aiger>? {
        let minimized = aiger_init()

        return try? withTemporaryFile(dir: nil, prefix: "", suffix: ".aig", deleteOnClose: true) {
            (inputTempFile: TemporaryFile) throws -> UnsafeMutablePointer<aiger>? in
            try withTemporaryFile(dir: nil, prefix: "", suffix: ".aig", deleteOnClose: true) {
                (outputTempFile: TemporaryFile) throws -> UnsafeMutablePointer<aiger>? in
                aiger_open_and_write_to_file(self, inputTempFile.path.pathString)

                var abcCommand = "read \(inputTempFile.path.pathString); strash; refactor -zl; rewrite -zl;"
                if self.pointee.num_ands < 1_000_000 {
                    abcCommand += " strash; refactor -zl; rewrite -zl;"
                }
                if self.pointee.num_ands < 200_000 {
                    abcCommand += " strash; refactor -zl; rewrite -zl;"
                }
                if self.pointee.num_ands < 200_000 {
                    abcCommand += " dfraig; rewrite -zl; dfraig;"
                }
                abcCommand += " write \(outputTempFile.path.pathString);"

                do {
                    try TSCBasic.Process.checkNonZeroExit(arguments: ["./Tools/abc", "-q", abcCommand])
                } catch {
                    Logger.default().error("minimization of aiger using abc failed")
                    return nil
                }

                let result = aiger_open_and_read_from_file(minimized, outputTempFile.path.pathString)
                assert(result == nil)

                return minimized
            }
        }
    }
}

struct iDQ: DqbfSolver {
    func solve(formula: Logic, preprocessor _: QbfPreprocessor?) -> SolverResult? {
        // encode formula
        let dqdimacsVisitor = DQDIMACSVisitor(formula: formula)
        let encodedFormula = dqdimacsVisitor.description

        return try? withTemporaryFile(dir: nil, prefix: "", suffix: ".dqdimacs", deleteOnClose: true) {
            (tempFile: TemporaryFile) throws -> SolverResult? in
            tempFile.fileHandle.write(Data(encodedFormula.utf8))

            // start task and extract stdout
            do {
                let result = try TSCBasic.Process.popen(arguments: ["./Tools/idq", tempFile.path.pathString])
                let stdout = try result.utf8Output()

                if stdout.contains("UNSAT") {
                    return .unsat
                } else if stdout.contains("SAT") {
                    return .sat
                }
                return nil

            } catch {
                Logger.default().error("execution of idq failed")
                return nil
            }
        }
    }
}

struct HQS: DqbfSolver {
    func solve(formula: Logic, preprocessor: QbfPreprocessor?) -> SolverResult? {
        // encode formula
        let dqdimacsVisitor = DQDIMACSVisitor(formula: formula)
        var encodedFormula = dqdimacsVisitor.description

        if let preprocessor = preprocessor {
            guard let preprocessedFormula = preprocessor.preprocess(qbf: encodedFormula) else {
                return nil
            }
            encodedFormula = preprocessedFormula
        }

        return try? withTemporaryFile(dir: nil, prefix: "", suffix: ".dqdimacs", deleteOnClose: true) {
            (tempFile: TemporaryFile) throws -> SolverResult? in
            tempFile.fileHandle.write(Data(encodedFormula.utf8))

            // start task and extract stdout
            do {
                let result = try TSCBasic.Process.popen(arguments: ["./Tools/hqs-linux", tempFile.path.pathString])
                let stdout = try result.utf8Output()

                if stdout.contains("UNSAT") {
                    return .unsat
                } else if stdout.contains("SAT") {
                    return .sat
                }
                return nil

            } catch {
                Logger.default().error("execution of hqs failed")
                return nil
            }
        }
    }
}

struct DCAQE: DqbfSolver {
    func solve(formula: Logic, preprocessor: QbfPreprocessor?) -> SolverResult? {
        // encode formula
        let dqdimacsVisitor = DQDIMACSVisitor(formula: formula)
        var encodedFormula = dqdimacsVisitor.description

        if let preprocessor = preprocessor {
            guard let preprocessedFormula = preprocessor.preprocess(qbf: encodedFormula) else {
                return nil
            }
            encodedFormula = preprocessedFormula
        }

        return try? withTemporaryFile(dir: nil, prefix: "", suffix: ".dqdimacs", deleteOnClose: true) {
            (tempFile: TemporaryFile) throws -> SolverResult? in
            tempFile.fileHandle.write(Data(encodedFormula.utf8))

            // start task and extract stdout
            do {
                let result = try TSCBasic.Process.popen(arguments: ["./Tools/dcaqe", tempFile.path.pathString])
                let stdout = try result.utf8Output()

                if stdout.contains("c Unsatisfiable") {
                    return .unsat
                } else if stdout.contains("c Satisfiable") {
                    return .sat
                }
                return nil

            } catch {
                Logger.default().error("execution of dcaqe failed")
                return nil
            }
        }
    }
}

struct Eprover: DqbfSolver {
    func solve(formula: Logic, preprocessor: QbfPreprocessor?) -> SolverResult? {
        // encode formula
        let dqdimacsVisitor = TPTP3Visitor(formula: formula)
        let encodedFormula = dqdimacsVisitor.description

        assert(preprocessor == nil)
        return try? withTemporaryFile(dir: nil, prefix: "", suffix: ".tptp3", deleteOnClose: true) {
            (tempFile: TemporaryFile) throws -> SolverResult? in
            tempFile.fileHandle.write(Data(encodedFormula.utf8))

            // start task and extract stdout
            do {
                let result = try TSCBasic.Process.popen(arguments: ["./Tools/eprover", "--auto", "--tptp3-format", tempFile.path.pathString])
                let stdout = try result.utf8Output()

                if stdout.contains("SZS status Satisfiable") {
                    return .sat
                } else if stdout.contains("SZS status Unsatisfiable") {
                    return .unsat
                }
                return nil

            } catch {
                Logger.default().error("execution of eprover failed")
                return nil
            }
        }
    }
}

struct Vampire: DqbfSolver {
    func solve(formula: Logic, preprocessor: QbfPreprocessor?) -> SolverResult? {
        // encode formula
        let dqdimacsVisitor = TPTP3Visitor(formula: formula)
        let encodedFormula = dqdimacsVisitor.description

        assert(preprocessor == nil)

        return try? withTemporaryFile(dir: nil, prefix: "", suffix: ".tptp3", deleteOnClose: true) {
            (tempFile: TemporaryFile) throws -> SolverResult? in
            tempFile.fileHandle.write(Data(encodedFormula.utf8))

            // start task and extract stdout
            do {
                let result = try TSCBasic.Process.popen(arguments: ["./Tools/vampire", "--mode", "casc", "-t", "1200", tempFile.path.pathString])
                let stdout = try result.utf8Output()

                if stdout.contains("SZS status Satisfiable") || stdout.contains("Termination reason: Satisfiable") {
                    return .sat
                } else if stdout.contains("SZS status Unsatisfiable") || stdout.contains("Termination reason: Refutation") {
                    return .unsat
                }
                return nil

            } catch {
                Logger.default().error("execution of vampire failed")
                return nil
            }
        }
    }
}

class GenericSmtSolver: SmtSolver {
    let task: Foundation.Process
    let inputPipe: Pipe
    let outputPipe: Pipe

    init(lauchPath: String, arguments: [String]) {
        inputPipe = Pipe()
        outputPipe = Pipe()

        task = Process()
        task.launchPath = lauchPath
        task.arguments = arguments
        task.standardInput = inputPipe
        task.standardOutput = outputPipe
        #if !os(Linux)
            task.standardError = FileHandle.nullDevice
        #endif
    }

    deinit {
        if task.isRunning {
            inputPipe.fileHandleForWriting.write("(exit)\n".data(using: .utf8)!)
            task.waitUntilExit()
        }
    }

    func solve(formula: String) -> SolverResult? {
        if !task.isRunning {
            task.launch()
        }

        guard let encodedFormula = (formula + "(check-sat)\n").data(using: .utf8) else {
            return nil
        }
        inputPipe.fileHandleForWriting.write(encodedFormula)

        // inputPipe.fileHandleForWriting.write("(check-sat)\n".data(using: .utf8)!)
        var result: SolverResult?
        repeat {
            let data = outputPipe.fileHandleForReading.availableData
            guard let output = String(data: data, encoding: .utf8) else {
                return nil
            }
            if output.contains("error") {
                Logger.default().error("SMT solver returns error: \(output)")
            }
            if output.contains("unsat") {
                result = .unsat
                return .unsat
            } else if output.contains("sat") {
                result = .sat
                return .sat
            }
        } while result == nil
        return nil
    }

    func getValue(expression: String) -> Logic? {
        precondition(task.isRunning)

        guard let encoded = "(get-value (\(expression)))\n".data(using: .utf8) else {
            return nil
        }
        inputPipe.fileHandleForWriting.write(encoded)
        let data = outputPipe.fileHandleForReading.availableData
        guard let resultString = String(data: data, encoding: .utf8) else {
            return nil
        }
        guard let result = BooleanUtils.parse(string: resultString.replacingOccurrences(of: "\(expression)", with: "")) else {
            return nil
        }
        return result
    }

    func getIntValue(name: String) -> Int? {
        precondition(task.isRunning)

        guard let encoded = "(get-value (\(name)))\n".data(using: .utf8) else {
            return nil
        }
        inputPipe.fileHandleForWriting.write(encoded)
        let data = outputPipe.fileHandleForReading.availableData
        guard let resultString = String(data: data, encoding: .utf8) else {
            return nil
        }
        let int = resultString.replacingOccurrences(of: name, with: "").replacingOccurrences(of: "(", with: "").replacingOccurrences(of: ")", with: "").replacingOccurrences(of: " ", with: "").replacingOccurrences(of: "\n", with: "")
        return Int(int, radix: 10)
    }
}

final class Z3: GenericSmtSolver {
    init() {
        super.init(lauchPath: "./Tools/z3", arguments: ["-in"])
    }
}

final class CVC4: GenericSmtSolver {
    init() {
        super.init(lauchPath: "./Tools/cvc4", arguments: ["--lang", "smt", "--finite-model-find", "--produce-models"])
    }
}
