import Foundation

import Utils

import CAiger

#if os(Linux)
    class Process: Task {}
#endif

public enum SolverResult: Int {
    case SAT = 10
    case UNSAT = 20
}

/* The following code may be an alternative for the current function calling solver interface.
 
enum SatSolverResult {
    case unsat
    case sat(assignment: [Int])
}

public enum Theory {
    case SAT
    case SMT
    case QBF
    case DQBF
}

public enum SolverFormat {
    case DIMACS
    case QDIMACS
    case DQDIMACS
    case QCIR14
    case TPTP3
    
    func encode(formula: Logic) -> String {
        switch self {
        case .DIMACS:
            return DIMACSVisitor(formula: formula).description
        case .QDIMACS:
            return QDIMACSVisitor(formula: formula).description
        case .DQDIMACS:
            return DQDIMACSVisitor(formula: formula).description
        case .QCIR14:
            return QCIRVisitor(formula: formula).description
        case .TPTP3:
            return TPTP3Visitor(formula: formula).description
        }
    }
}

protocol SolverDefinition {
    var name: String { get }
    var launchPath: String { get }
    var format: SolverFormat { get }
    
    func getArguments(path: String) -> [String]
    func getResult(returnCode: Int, stdout: String, stderr: String) -> SolverResult?
}

class RAReQS: SolverDefinition {
    let name = "RAReQS"
    let launchPath = "./Tools/rareqs"
    let format: SolverFormat = .QDIMACS
    
    func getArguments(path: String) -> [String] {
        return [path]
    }
    
    func getResult(returnCode: Int, stdout: String, stderr: String) -> SolverResult? {
        return SolverResult(rawValue: returnCode)
    }
}

protocol SatSolverDefinition: SolverDefinition {
    func getAssignments(stdout: String, stderr: String) -> [Int]
}

class PicoSAT: SatSolverDefinition {
    let name = "PicoSAT"
    let launchPath = "./Tools/picosat"
    let format: SolverFormat = .DIMACS
    
    func getArguments(path: String) -> [String] {
        return [path]
    }
    
    func getResult(returnCode: Int, stdout: String, stderr: String) -> SolverResult? {
        return SolverResult(rawValue: returnCode)
    }
    
    func getAssignments(stdout: String, stderr: String) -> [Int] {
        var assignments: [Int] = []
        for line in stdout.components(separatedBy: "\n") {
            if !line.hasPrefix("v") {
                continue
            }
            assignments += line[line.index(after: line.startIndex)..<line.endIndex]
                .trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines)
                .components(separatedBy: " ")
                .flatMap({ Int($0) })
        }
        return assignments
    }
}

enum SatSolver {
    case picosat
    
    var solverConfig: SatSolverDefinition {
        switch self {
        case .picosat:
            return PicoSAT()
        }
    }
    
    func solve(formula: Logic) -> SatSolverResult? {
        // encode formula
        let solver = solverConfig
        let encodedFormula = solver.format.encode(formula: formula)
        
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
        task.launchPath = solver.launchPath
        task.arguments = solver.getArguments(path: tempFile.path)
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
        
        let stderrData = stderrPipe.fileHandleForReading.readDataToEndOfFile()
        guard let stderr = String(data: stderrData, encoding: String.Encoding.utf8) else {
            return nil
        }
        
        guard let result = solver.getResult(returnCode: Int(task.terminationStatus), stdout: stdout, stderr: stderr) else {
            return nil
        }
        
        if result == .UNSAT {
            return .unsat
        }
        return .sat(assignment: solver.getAssignments(stdout: stdout, stderr: stderr))
    }
}


struct Solver {
    let solver: SolverDefinition
    
    init(definition: SolverDefinition) {
        solver = definition
    }
    
    func solve(formula: Logic) -> SolverResult? {
        // encode formula
        let encodedFormula = solver.format.encode(formula: formula)
        
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
        task.launchPath = solver.launchPath
        task.arguments = solver.getArguments(path: tempFile.path)
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
        
        let stderrData = stderrPipe.fileHandleForReading.readDataToEndOfFile()
        guard let stderr = String(data: stderrData, encoding: String.Encoding.utf8) else {
            return nil
        }
        
        return solver.getResult(returnCode: Int(task.terminationStatus), stdout: stdout, stderr: stderr)
    }
}*/

public func rareqs(qdimacs: String) -> (SolverResult, [Int]?)? {
    let tempFile = TempFile(suffix: ".qdimacs")!
    try! qdimacs.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
    
    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif
    task.launchPath = "./Tools/rareqs"
    task.arguments = [tempFile.path]
    
    //let stdinPipe = NSPipe()
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    //task.standardInput = stdinPipe
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    /*let stdinHandle = stdinPipe.fileHandleForWriting
    if let data = qdimacs.data(using: NSUTF8StringEncoding) {
        #if os(Linux)
        stdinHandle.writeData(data)
        #else
        stdinHandle.write(data)
        #endif
        stdinHandle.closeFile()
    }*/
    
    task.waitUntilExit()
    guard let result = SolverResult(rawValue: Int(task.terminationStatus)) else {
        return nil
    }
    if result != .SAT {
        return (result, nil)
    }
    let stdoutData = stdoutPipe.fileHandleForReading.readDataToEndOfFile()
    guard let output = String(data: stdoutData, encoding: String.Encoding.utf8) else {
        return nil
    }
    for line in output.components(separatedBy: "\n") {
        if !line.hasPrefix("V") {
            continue
        }
        let assignments = line[line.index(after: line.startIndex)..<line.endIndex]
                          .trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines)
                          .components(separatedBy: " ")
                          .flatMap({ Int($0) })
        return (result, assignments)
    }
    return (result, [])
}

public func bloqqer(qdimacs: String, keepAssignments: Bool) -> String {
    
    let tempFile = TempFile(suffix: ".qdimacs")!
    try! qdimacs.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)

    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif
    if !keepAssignments {
        task.launchPath = "./Tools/bloqqer-031"
        task.arguments = ["--keep=1", tempFile.path]
    } else {
        task.launchPath = "./Tools/bloqqer"
        task.arguments = ["--keep=1", "--partial-assignment=1", tempFile.path]
    }
    
    //let stdinPipe = NSPipe()
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    //task.standardInput = stdinPipe
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    /*let stdinHandle = stdinPipe.fileHandleForWriting
    if let data = qdimacs.data(using: NSUTF8StringEncoding) {
        #if os(Linux)
        stdinHandle.writeData(data)
        #else
        stdinHandle.write(data)
        #endif
        stdinHandle.closeFile()
    }*/
    
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let outputData = StreamHelper.readAllAvailableData(from: stdoutHandle)

    task.waitUntilExit()
    //let stdoutData = stdoutPipe.fileHandleForReading.readDataToEndOfFile()
    let output = String(data: outputData, encoding: String.Encoding.utf8)!
    return output
}

public func depqbf(qdimacs: String) -> SolverResult? {
    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif
    
    task.launchPath = "./Tools/depqbf"
    task.arguments = []
    
    let stdinPipe = Pipe()
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    task.standardInput = stdinPipe
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    let stdinHandle = stdinPipe.fileHandleForWriting
    if let data = qdimacs.data(using: String.Encoding.utf8) {
        stdinHandle.write(data)
        stdinHandle.closeFile()
    }
    
    task.waitUntilExit()
    return SolverResult(rawValue: Int(task.terminationStatus))
}

public func quabs(qcir: String) -> (SolverResult, UnsafeMutablePointer<aiger>?)? {
    let tempFile = TempFile(suffix: ".qcir")!
    try! qcir.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
    
    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif

    task.launchPath = "./Tools/quabsl"
    task.arguments = ["-c", tempFile.path]
    
    //let stdinPipe = NSPipe()
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    //task.standardInput = stdinPipe
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    /*let stdinHandle = stdinPipe.fileHandleForWriting
    if let data = qcir.data(using: NSUTF8StringEncoding) {
        #if os(Linux)
        stdinHandle.writeData(data)
        #else
        stdinHandle.write(data)
        #endif
        stdinHandle.closeFile()
    }*/
    
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
    
    guard let result = SolverResult(rawValue: Int(task.terminationStatus)) else {
        return nil
    }
    if result != .SAT {
        return (result, nil)
    }
    
    return (result, aiger)
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
    
    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif
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

public func picosat(dimacs: String) -> (SolverResult, [Int]?)? {
    let tempFile = TempFile(suffix: ".dimacs")!
    try! dimacs.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
    
    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif
    task.launchPath = "./Tools/picosat"
    task.arguments = [tempFile.path]
    
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    task.waitUntilExit()
    guard let result = SolverResult(rawValue: Int(task.terminationStatus)) else {
        return nil
    }
    if result != .SAT {
        return (result, nil)
    }
    let stdoutData = stdoutPipe.fileHandleForReading.readDataToEndOfFile()
    guard let output = String(data: stdoutData, encoding: String.Encoding.utf8) else {
        return nil
    }
    var assignments: [Int] = []
    for line in output.components(separatedBy: "\n") {
        if !line.hasPrefix("v") {
            continue
        }
        assignments += line[line.index(after: line.startIndex)..<line.endIndex]
            .trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines)
            .components(separatedBy: " ")
            .flatMap({ Int($0) })
    }
    return (result, assignments)
}

public func cryptominisat(dimacs: String) -> (SolverResult, [Int]?)? {
    let tempFile = TempFile(suffix: ".dimacs")!
    try! dimacs.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
    
    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif
    task.launchPath = "./Tools/cryptominisat5"
    task.arguments = ["--verb", "0", tempFile.path]
    
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let outputData = StreamHelper.readAllAvailableData(from: stdoutHandle)
    
    task.waitUntilExit()
    
    guard let result = SolverResult(rawValue: Int(task.terminationStatus)) else {
        return nil
    }
    if result != .SAT {
        return (result, nil)
    }
    
    //let stdoutData = stdoutPipe.fileHandleForReading.readDataToEndOfFile()
    let output = String(data: outputData, encoding: String.Encoding.utf8)!
    
    var assignments: [Int] = []
    for line in output.components(separatedBy: "\n") {
        if !line.hasPrefix("v") {
            continue
        }
        assignments += line[line.index(after: line.startIndex)..<line.endIndex]
            .trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines)
            .components(separatedBy: " ")
            .flatMap({ Int($0) })
    }
    return (result, assignments)
}

func eprover(tptp3: String) -> SolverResult? {
    let tempFile = TempFile(suffix: ".tptp3")!
    try! tptp3.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)

    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif
    task.launchPath = "./Tools/eprover"
    task.arguments = ["--auto", "--tptp3-format", tempFile.path]
    
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let outputData = StreamHelper.readAllAvailableData(from: stdoutHandle)

    task.waitUntilExit()
    let output = String(data: outputData, encoding: String.Encoding.utf8)!
    //print(output)
    if output.contains("SZS status Satisfiable") {
        return .SAT
    } else if output.contains("SZS status Unsatisfiable") {
        return .UNSAT
    }
    return nil
}

func idq(dqdimacs: String) -> SolverResult? {
    let tempFile = TempFile(suffix: ".dqdimacs")!
    try! dqdimacs.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
    
    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif
    task.launchPath = "./Tools/idq"
    task.arguments = [tempFile.path]
    
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let outputData = StreamHelper.readAllAvailableData(from: stdoutHandle)
    
    task.waitUntilExit()
    let output = String(data: outputData, encoding: String.Encoding.utf8)!
    //print(output)
    if output.contains("UNSAT") {
        return .UNSAT
    } else if output.contains("SAT") {
        return .SAT
    }
    return nil
}

func z3(smt2: String) -> SolverResult? {
    let tempFile = TempFile(suffix: ".smt2")!
    try! smt2.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
    
    #if os(Linux)
        let task = Task()
    #else
        let task = Process()
    #endif
    task.launchPath = "./Tools/z3"
    task.arguments = [tempFile.path]
    
    let stdoutPipe = Pipe()
    let stderrPipe = Pipe()
    task.standardOutput = stdoutPipe
    task.standardError = stderrPipe
    task.launch()
    
    let stdoutHandle = stdoutPipe.fileHandleForReading
    let outputData = StreamHelper.readAllAvailableData(from: stdoutHandle)
    
    task.waitUntilExit()
    let output = String(data: outputData, encoding: String.Encoding.utf8)!
    //print(output)
    if output.contains("error") {
        return nil
    } else if output.contains("unsat") {
        return .UNSAT
    } else if output.contains("sat") {
        return .SAT
    }
    return nil
}

