import Foundation

public class TempFile {
    
    public let url: URL
    public let path: String
    
    public init?(suffix: String = "") {
        let fileName: String = ProcessInfo.processInfo.globallyUniqueString + suffix
        let tempDirURL = URL(fileURLWithPath: NSTemporaryDirectory())
        let fileURL = tempDirURL.appendingPathComponent(fileName)
        self.url = fileURL
        self.path = fileURL.path
    }
    
    deinit {
        do {
            try FileManager.default.removeItem(at: url)
        } catch let e {
            print("cleanup failed \(e)")
            // ...
        }
    }
}
