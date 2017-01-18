import Foundation

import Utils

import CAiger

enum SolverResult {
    case sat
    case unsat
}

enum SolverInstance: String {
    // SAT solver
    case picosat = "picosat"
    case cryptominisat = "cryptominisat"
    
    // QBF solver
    case rareqs = "rareqs"
    case depqbf = "depqbf"
    case caqe   = "caqe"
    
    // DQBF solver
    case idq = "idq"
    
    // FO solver
    case eprover = "eprover"
    case vampire  = "vampire"
    
    // SMT solver
    case z3 = "z3"
    case cvc4 = "cvc4"
    
    var instance: Solver {
        switch self {
        case .picosat:
            return PicoSAT()
        case .cryptominisat:
            return CryptoMiniSat()
        case .rareqs:
            return RAReQS()
        case .depqbf:
            return DepQBF()
        case .caqe:
            return CAQE()
        case .idq:
            return iDQ()
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
    
    static let allValues: [SolverInstance] = [
        .picosat,
        .cryptominisat,
        .rareqs,
        .depqbf,
        .caqe,
        .idq,
        .eprover,
        .vampire,
        .z3,
        .cvc4
    ]
}

enum SatSolverResult {
    case unsat
    case sat(assignment: BooleanAssignment)
}

enum QbfSolverResult {
    case unsat
    case sat(functions: [Proposition:Logic])
}

protocol Solver {
}

protocol SatSolver: Solver {
    func solve(formula: Logic) -> SatSolverResult?
}

protocol QbfPreprocessor {
    func preprocess(qbf: String) -> String?
}

protocol QbfSolver: Solver {
    func solve(formula: Logic, preprocessor: QbfPreprocessor?) -> SatSolverResult?
}

protocol CertifyingQbfSolver: Solver {
    func solve(formula: Logic) -> QbfSolverResult?
}

protocol SmtSolver: Solver {
    func solve(formula: String) -> SolverResult?
}

protocol DqbfSolver: Solver {
    func solve(formula: Logic) -> SolverResult?
}

private enum SolverHelper {
    static func getDimacsAssignments(stdout: String) -> [Int] {
        var assignments: [Int] = []
        for line in stdout.components(separatedBy: "\n") {
            if !line.hasPrefix("v") && !line.hasPrefix("V") {
                continue
            }
            assignments += line[line.index(after: line.startIndex)..<line.endIndex]
                .trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines)
                .components(separatedBy: " ")
                .flatMap({ Int($0) })
        }
        return assignments
    }
    
    static func executeAndReturnStdout(task: Process) -> String? {
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
}

struct PicoSAT: SatSolver {
    func solve(formula: Logic) -> SatSolverResult? {
        // encode formula
        let dimacsVisitor = DIMACSVisitor(formula: formula)
        let encodedFormula = dimacsVisitor.description
        
        // write to disk
        guard let tempFile = TempFile(suffix: ".dimacs") else {
            return nil
        }
        do {
            try encodedFormula.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        // start task and extract stdout
        let task = Process()
        task.launchPath = "./Tools/picosat"
        task.arguments = [tempFile.path]
        
        guard let stdout = SolverHelper.executeAndReturnStdout(task: task) else {
            return nil
        }
        
        guard let result = SolverHelper.result(from: task.terminationStatus) else {
            return nil
        }
        
        if result == .unsat {
            return .unsat
        }
        let assignments = SolverHelper.getDimacsAssignments(stdout: stdout)
        return .sat(assignment: dimacsVisitor.getAssignment(fromAssignment: assignments))
    }
}

struct CryptoMiniSat: SatSolver {
    func solve(formula: Logic) -> SatSolverResult? {
        // encode formula
        let dimacsVisitor = DIMACSVisitor(formula: formula)
        let encodedFormula = dimacsVisitor.description
        
        // write to disk
        guard let tempFile = TempFile(suffix: ".dimacs") else {
            return nil
        }
        do {
            try encodedFormula.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        // start task and extract stdout and stderr
        let task = Process()
        task.launchPath = "./Tools/cryptominisat5"
        task.arguments = ["--verb", "0", tempFile.path]

        guard let stdout = SolverHelper.executeAndReturnStdout(task: task) else {
            return nil
        }
        
        guard let result = SolverHelper.result(from: task.terminationStatus) else {
            return nil
        }
        
        if result == .unsat {
            return .unsat
        }
        let assignments = SolverHelper.getDimacsAssignments(stdout: stdout)
        return .sat(assignment: dimacsVisitor.getAssignment(fromAssignment: assignments))
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
        
        // write to disk
        guard let tempFile = TempFile(suffix: ".qdimacs") else {
            return nil
        }
        do {
            try encodedFormula.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        // start task and extract stdout and stderr
        let task = Process()
        task.launchPath = "./Tools/rareqs"
        task.arguments = [tempFile.path]

        guard let stdout = SolverHelper.executeAndReturnStdout(task: task) else {
            return nil
        }
        
        guard let result = SolverHelper.result(from: task.terminationStatus) else {
            return nil
        }
        
        if result == .unsat {
            return .unsat
        }
        let assignments = SolverHelper.getDimacsAssignments(stdout: stdout)
        return .sat(assignment: qdimacsVisitor.getAssignment(fromAssignment: assignments))
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
        
        // write to disk
        guard let tempFile = TempFile(suffix: ".qdimacs") else {
            return nil
        }
        do {
            try encodedFormula.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        // start task and extract stdout and stderr
        let task = Process()
        task.launchPath = "./Tools/depqbf"
        task.arguments = ["--qdo", tempFile.path]
        
        guard let stdout = SolverHelper.executeAndReturnStdout(task: task) else {
            return nil
        }
        
        guard let result = SolverHelper.result(from: task.terminationStatus) else {
            return nil
        }
        
        if result == .unsat {
            return .unsat
        }
        let assignments = SolverHelper.getDimacsAssignments(stdout: stdout)
        return .sat(assignment: qdimacsVisitor.getAssignment(fromAssignment: assignments))
    }
}

struct Bloqqer: QbfPreprocessor {
    let preserveAssignments: Bool
    
    init(preserveAssignments: Bool) {
        self.preserveAssignments = preserveAssignments
    }
    
    func preprocess(qbf: String) -> String? {
        guard let tempFile = TempFile(suffix: ".qdimacs") else {
            return nil
        }
        do {
            try qbf.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        let task = Process()
        if !preserveAssignments {
            task.launchPath = "./Tools/bloqqer-031"
            task.arguments = ["--keep=1", tempFile.path]
        } else {
            task.launchPath = "./Tools/bloqqer"
            task.arguments = ["--keep=1", "--partial-assignment=1", tempFile.path]
        }
        
        guard let stdout = SolverHelper.executeAndReturnStdout(task: task) else {
            return nil
        }
        return stdout
    }
}

struct CAQE: QbfSolver {
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
        
        // write to disk
        guard let tempFile = TempFile(suffix: ".qdimacs") else {
            return nil
        }
        do {
            try encodedFormula.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        // start task and extract stdout and stderr
        let task = Process()
        task.launchPath = "./Tools/caqem"
        task.arguments = ["--partial-assignments", "--expansion-refinement=1", tempFile.path]
        
        guard let stdout = SolverHelper.executeAndReturnStdout(task: task) else {
            return nil
        }
        
        guard let result = SolverHelper.result(from: task.terminationStatus) else {
            return nil
        }
        
        if result == .unsat {
            return .unsat
        }
        let assignments = SolverHelper.getDimacsAssignments(stdout: stdout)
        return .sat(assignment: qdimacsVisitor.getAssignment(fromAssignment: assignments))
    }
}

struct QuAbS: CertifyingQbfSolver {
    func solve(formula: Logic) -> QbfSolverResult? {
        let qcirVisitor = QCIRVisitor(formula: formula)
        let encodedFormula = qcirVisitor.description
        
        guard let tempFile = TempFile(suffix: ".qcir") else {
            return nil
        }
        do {
            try encodedFormula.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        let task = Process()
        
        task.launchPath = "./Tools/quabscm"
        task.arguments = ["-c", tempFile.path]
        
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
            //print(String(cString: aiger_error(aiger)))
            return nil
        }
        
        task.waitUntilExit()
        
        guard let result = SolverHelper.result(from: task.terminationStatus) else {
            return nil
        }
        if result != .sat {
            return .unsat
        }
        
        guard let minimizedCertificate = minimizeWithABC(aiger) else {
            Logger.default().error("could not minimize certificate with ABC")
            return nil
        }
        aiger_reset(aiger)
        let functions = qcirVisitor.translate(certificate: minimizedCertificate)
        aiger_reset(minimizedCertificate)
        
        return .sat(functions: functions)
    }
}

func minimizeWithABC(_ aig: UnsafeMutablePointer<aiger>) -> UnsafeMutablePointer<aiger>? {
    let minimized = aiger_init()
    
    guard let inputTempFile = TempFile(suffix: ".aig") else {
        return nil
    }
    guard let outputTempFile = TempFile(suffix: ".aig") else {
        return nil
    }
    aiger_open_and_write_to_file(aig, inputTempFile.path)
    
    var abcCommand = "read \(inputTempFile.path); strash; refactor -zl; rewrite -zl;"
    if aig.pointee.num_ands < 1000000 {
        abcCommand += " strash; refactor -zl; rewrite -zl;"
    }
    if aig.pointee.num_ands < 200000 {
        abcCommand += " strash; refactor -zl; rewrite -zl;"
    }
    if aig.pointee.num_ands < 200000 {
        abcCommand += " dfraig; rewrite -zl; dfraig;"
    }
    abcCommand += " write \(outputTempFile.path);"
    
    let task = Process()
    task.launchPath = "./Tools/abc"
    task.arguments = ["-q", abcCommand]
    task.standardOutput = FileHandle.standardError
    task.launch()
    task.waitUntilExit()
    assert(task.terminationStatus == 0)
    
    let result = aiger_open_and_read_from_file(minimized, outputTempFile.path)
    assert(result == nil)
    
    return minimized
}

struct iDQ: DqbfSolver {
    func solve(formula: Logic) -> SolverResult? {
        // encode formula
        let dqdimacsVisitor = DQDIMACSVisitor(formula: formula)
        let encodedFormula = dqdimacsVisitor.description

        // write to disk
        guard let tempFile = TempFile(suffix: ".dqdimacs") else {
            return nil
        }
        do {
            try encodedFormula.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        // start task and extract stdout and stderr
        let task = Process()
        task.launchPath = "./Tools/idq"
        task.arguments = [tempFile.path]
        
        guard let output = SolverHelper.executeAndReturnStdout(task: task) else {
            return nil
        }
        //print(output)
        if output.contains("UNSAT") {
            return .unsat
        } else if output.contains("SAT") {
            return .sat
        }
        return nil
    }
}

struct Eprover: DqbfSolver {
    func solve(formula: Logic) -> SolverResult? {
        // encode formula
        let dqdimacsVisitor = TPTP3Visitor(formula: formula)
        let encodedFormula = dqdimacsVisitor.description
        
        // write to disk
        guard let tempFile = TempFile(suffix: ".tptp3") else {
            return nil
        }
        do {
            try encodedFormula.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        // start task and extract stdout and stderr
        let task = Process()
        task.launchPath = "./Tools/eprover"
        task.arguments = ["--auto", "--tptp3-format", tempFile.path]
        
        guard let output = SolverHelper.executeAndReturnStdout(task: task) else {
            return nil
        }
        //print(output)
        if output.contains("SZS status Satisfiable") {
            return .sat
        } else if output.contains("SZS status Unsatisfiable") {
            return .unsat
        }
        return nil
    }
}

struct Vampire: DqbfSolver {
    func solve(formula: Logic) -> SolverResult? {
        // encode formula
        let dqdimacsVisitor = TPTP3Visitor(formula: formula)
        let encodedFormula = dqdimacsVisitor.description
        
        // write to disk
        guard let tempFile = TempFile(suffix: ".tptp3") else {
            return nil
        }
        do {
            try encodedFormula.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        // start task and extract stdout and stderr
        let task = Process()
        task.launchPath = "./Tools/vampire"
        task.arguments = ["--mode", "casc", "-t","1200", tempFile.path]
        
        guard let output = SolverHelper.executeAndReturnStdout(task: task) else {
            return nil
        }
        //print(output)
        if output.contains("SZS status Satisfiable") || output.contains("Termination reason: Satisfiable") {
            return .sat
        } else if output.contains("SZS status Unsatisfiable") || output.contains("Termination reason: Refutation") {
            return .unsat
        }

        return nil
    }
}

struct Z3: SmtSolver {
    func solve(formula: String) -> SolverResult? {
        guard let tempFile = TempFile(suffix: ".smt2") else {
            return nil
        }
        do {
            try formula.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        let task = Process()
        task.launchPath = "./Tools/z3"
        task.arguments = [tempFile.path]
        
        guard let output = SolverHelper.executeAndReturnStdout(task: task) else {
            return nil
        }
        
        //print(output)
        if output.contains("error") {
            return nil
        } else if output.contains("unsat") {
            return .unsat
        } else if output.contains("sat") {
            return .sat
        }
        return nil
    }
}

struct CVC4: SmtSolver {
    func solve(formula: String) -> SolverResult? {
        guard let tempFile = TempFile(suffix: ".smt2") else {
            return nil
        }
        do {
            try formula.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
        } catch {
            return nil
        }
        
        let task = Process()
        task.launchPath = "./Tools/cvc4"
        task.arguments = ["--lang", "smt", "--finite-model-find", tempFile.path]
        
        guard let output = SolverHelper.executeAndReturnStdout(task: task) else {
            return nil
        }
        
        //print(output)
        if output.contains("error") {
            return nil
        } else if output.contains("unsat") {
            return .unsat
        } else if output.contains("sat") {
            return .sat
        }
        return nil
    }
}



