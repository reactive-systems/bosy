import Foundation

public class Logger {
    
    #if os(Linux)
    let fileHandle: NSFileHandle = NSFileHandle.fileHandleWithStandardError()
    #else
    let fileHandle: FileHandle = FileHandle.standardError
    #endif
    
    static let defaultLogger = Logger()
    
    public static func `default`() -> Logger {
        return defaultLogger
    }
    
    public func error(_ message: String) {
        if let data = "error: \(message)\n".data(using: String.Encoding.utf8) {
            #if os(Linux)
            fileHandle.writeData(data)
            #else
            fileHandle.write(data)
            #endif
        }
        //print("error: \(message)")
    }
    
    public func info(_ message: String) {
        if let data = "info: \(message)\n".data(using: String.Encoding.utf8) {
            #if os(Linux)
            fileHandle.writeData(data)
            #else
            fileHandle.write(data)
            #endif
        }
        //print("info: \(message)")
    }
}
