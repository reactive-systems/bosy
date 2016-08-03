import Foundation

import Utils

import CAiger

public enum SolverResult: Int {
    case SAT = 10
    case UNSAT = 20
}

public enum SolverInputFormat {
    case QDIMACS
    case DIMACS
}

public enum SolverCapability {
    case ReturnResult
    case ReturnPartialAssignment
    case ReturnCertificate
}

protocol Solver {
    var format: SolverInputFormat { get }
    
    func solve(input: String) -> SolverResult?
}

public func rareqs(qdimacs: String) -> (SolverResult, [Int]?)? {
    let tempFile = TempFile(suffix: ".qdimacs")!
    try! qdimacs.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
    
    let task = Process()
    task.launchPath = "./rareqs"
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

public func bloqqer(qdimacs: String) -> String {
    
    let tempFile = TempFile(suffix: ".qdimacs")!
    try! qdimacs.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)

    let task = Process()
    task.launchPath = "./bloqqer"
    task.arguments = ["--keep=1", "--partial-assignment=1", tempFile.path]
    
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
    let task = Process()

    task.launchPath = "./depqbf"
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
        #if os(Linux)
        stdinHandle.writeData(data)
        #else
        stdinHandle.write(data)
        #endif
        stdinHandle.closeFile()
    }
    
    task.waitUntilExit()
    return SolverResult(rawValue: Int(task.terminationStatus))
}

public func quabs(qcir: String) -> (SolverResult, UnsafeMutablePointer<aiger>?)? {
    let tempFile = TempFile(suffix: ".qcir")!
    try! qcir.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)
    
    let task = Process()

    task.launchPath = "./quabs"
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
    
    let task = Process()
    task.launchPath = "./abc"
    task.arguments = ["-c", abcCommand]
#if os(Linux)
    task.standardOutput = NSFileHandle.fileHandlestandardError()
#else
    task.standardOutput = FileHandle.standardError
#endif
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
    
    let task = Process()
    task.launchPath = "./picosat"
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

func eprover(tptp3: String) -> SolverResult? {
    let tempFile = TempFile(suffix: ".tptp3")!
    try! tptp3.write(toFile: tempFile.path, atomically: true, encoding: String.Encoding.utf8)

    let task = Process()
    task.launchPath = "./eprover"
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
