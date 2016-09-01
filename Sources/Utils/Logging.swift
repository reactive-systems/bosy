import Foundation

public class Logger {
    
    let fileHandle: FileHandle = FileHandle.standardError
    
    static let defaultLogger = Logger()
    
    public static func `default`() -> Logger {
        return defaultLogger
    }
    
    public func error(_ message: String) {
        if let data = "error: \(message)\n".data(using: String.Encoding.utf8) {
            fileHandle.write(data)
        }
        //print("error: \(message)")
    }
    
    public func info(_ message: String) {
        if let data = "info: \(message)\n".data(using: String.Encoding.utf8) {
            fileHandle.write(data)
        }
        //print("info: \(message)")
    }
}
