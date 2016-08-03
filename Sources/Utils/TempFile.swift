import Foundation

public class TempFile {
    
    let fileURL: URL
    public let path: String
    
    public init?(suffix: String = "") {
        let fileName: String = ProcessInfo.processInfo.globallyUniqueString + suffix
        let tempDirURL = URL(fileURLWithPath: NSTemporaryDirectory())
#if os(Linux)
        fileURL = tempDirURL.URLByAppendingPathComponent(fileName)!
#else
        let fileURL = tempDirURL.appendingPathComponent(fileName)
        self.fileURL = fileURL
#endif
        self.path = fileURL.path
    }
    
    deinit {
        do {
#if os(Linux)
            try NSFileManager.defaultManager().removeItem(at: fileURL)
#else
            try FileManager.default.removeItem(at: fileURL)
#endif
        } catch let e {
            print("cleanup failed \(e)")
            // ...
        }
    }
}
