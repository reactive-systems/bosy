
public func numBitsNeeded(_ x: Int) -> Int {
    if x % 2 != 0 {
        return 1 + numBitsNeeded(x - 1)
    }
    switch x {
    case 0: return 0
    case 1: return 1
    case 2: return 1
    default: return 1 + numBitsNeeded(x / 2)
    }
}

public func binaryFrom(_ n: Int, bits: Int) -> String {
    let binary = String(n, radix: 2)
    // padding on left
    assert(binary.characters.count <= bits)
    if binary.characters.count == bits {
        return binary
    }
    let padding = String(repeating: "0", count: bits - binary.characters.count)
    return padding + binary
}
