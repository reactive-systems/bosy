
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
