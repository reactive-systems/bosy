import Foundation

public class TempFile {
    
    let fileURL: URL
    public let path: String
    
    public init?(suffix: String = "") {
        let fileName: String = ProcessInfo.processInfo.globallyUniqueString + suffix
        let tempDirURL = URL(fileURLWithPath: NSTemporaryDirectory())
        let fileURL = tempDirURL.appendingPathComponent(fileName)
        self.fileURL = fileURL
        self.path = fileURL.path
    }
    
    deinit {
        do {
            try FileManager.default.removeItem(at: fileURL)
        } catch let e {
            print("cleanup failed \(e)")
            // ...
        }
    }
}
