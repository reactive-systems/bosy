import Foundation

public enum StreamHelper {
    public static func readAllAvailableData(from handle: FileHandle) -> Data {
        var data = Data()
        var readData = Data()
        repeat {
            readData = handle.availableData
            data.append(readData)
        } while (readData.count > 0)
        
        return data
    }
}
