protocol Scanner {
    
    func current() -> UnicodeScalar
    
    mutating func next()
    
    func finished() -> Bool
}

public struct ScalarScanner<C: Collection> : Scanner where C.Iterator.Element == UnicodeScalar {
   let scalars: C
   var index: C.Index
   
   init(scalars: C) {
       self.scalars = scalars
       self.index = scalars.startIndex
   }
   
   func current() -> UnicodeScalar {
       precondition(!finished())
       return scalars[index]
   }
   
   mutating func next() {
       index = scalars.index(index, offsetBy: 1)
   }
   
   func finished() -> Bool {
       return index >= scalars.endIndex
   }
}
