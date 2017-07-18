import Foundation

public class Logger {
    
    public enum Verbosity: Int {
        case warning = 0
        case info    = 1
        case debug   = 2
        
        static func < (lhs: Verbosity, rhs: Verbosity) -> Bool {
            return lhs.rawValue < rhs.rawValue
        }
    }
    
    let fileHandle: FileHandle = FileHandle.standardError
    public var verbosity: Verbosity
    
    static let defaultLogger = Logger()
    
    init(verbosity: Verbosity = .info) {
        self.verbosity = verbosity
    }
    
    public static func `default`() -> Logger {
        return defaultLogger
    }
    
    public func error(_ message: String) {
        if let data = "error: \(message)\n".data(using: String.Encoding.utf8) {
            fileHandle.write(data)
        }
        //print("error: \(message)")
    }
    
    public func warning(_ message: String) {
        if let data = "warning: \(message)\n".data(using: String.Encoding.utf8) {
            fileHandle.write(data)
        }
        //print("info: \(message)")
    }
    
    public func info(_ message: String) {
        if verbosity < .info {
            return
        }
        if let data = "info: \(message)\n".data(using: String.Encoding.utf8) {
            fileHandle.write(data)
        }
        //print("info: \(message)")
    }
    
    public func debug(_ message: String) {
        if verbosity < .debug {
            return
        }
        if let data = "debug: \(message)\n".data(using: String.Encoding.utf8) {
            fileHandle.write(data)
        }
        //print("info: \(message)")
    }
}
