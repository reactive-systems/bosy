import Foundation

typealias LTLOperatorPrecedence = Int

extension LTLOperatorPrecedence {
    static let min = 0
    
    func next() -> LTLOperatorPrecedence {
        return self + 1
    }
}

public enum LTLToken: CustomStringConvertible, Equatable, Hashable {
    
    case Proposition(String)
    
    // Literals
    case True, False
    
    // Boolean operators
    case Not, Or, And, Implies, Equivalent
    
    // Temporal Operators
    case Next, Until, WeakUntil, Release, Eventually, Globally
    
    // Parenthesis
    case LParen, RParen
    
    // End of Input
    case EOI
    
    // CustomStringConvertible
    public var description: String {
        switch self {
        case .Proposition(let name):
            return name
        case .True:
            return "true"
        case .False:
            return "false"
        case .Not:
            return "!"
        case .Or:
            return "||"
        case .And:
            return "&&"
        case .Implies:
            return "->"
        case .Equivalent:
            return "<->"
        case .Next:
            return "X"
        case .Until:
            return "U"
        case .WeakUntil:
            return "W"
        case .Release:
            return "R"
        case .Eventually:
            return "F"
        case .Globally:
            return "G"
        case .LParen:
            return "("
        case .RParen:
            return ")"
        case .EOI:
            return "eof"
        }
    }
    
    // Equatable
    public static func == (lhs: LTLToken, rhs: LTLToken) -> Bool {
        switch (lhs, rhs) {
        case (.Proposition(let lhsName), .Proposition(let rhsName)):
            return lhsName == rhsName
        case (.True, .True): return true
        case (.False, .False): return true
        case (.Not, .Not): return true
        case (.Or, .Or): return true
        case (.And, .And): return true
        case (.Implies, .Implies): return true
        case (.Equivalent, .Equivalent): return true
        case (.Next, .Next): return true
        case (.Until, .Until): return true
        case (.WeakUntil, .WeakUntil): return true
        case (.Release, .Release): return true
        case (.Eventually, .Eventually): return true
        case (.Globally, .Globally): return true
        case (.LParen, .LParen): return true
        case (.RParen, .RParen): return true
        case (.EOI, .EOI): return true
        default:
            return false
        }
    }
    
    // Hashable
    public var hashValue: Int {
        return description.hashValue
    }
    
    
    var precedence: LTLOperatorPrecedence {
        switch self {
        case .Equivalent:
            return 0
        case .Implies:
            return 1
        case .Or:
            return 2
        case .And:
            return 3
        case .Until:
            return 4
        case .Release:
            return 4
        case .WeakUntil:
            return 4
        default:
            return -1
        }
    }
    
    var isBinaryOperator: Bool {
        switch self {
        case .Until:
            return true
        case .WeakUntil:
            return true
        case .Release:
            return true
        case .Or:
            return true
        case .And:
            return true
        case .Implies:
            return true
        case .Equivalent:
            return true
        default:
            return false
        }
    }
    
    var isUnaryOperator: Bool {
        switch self {
        case .Next:
            return true
        case .Eventually:
            return true
        case .Globally:
            return true
        case .Not:
            return true
        default:
            return false
        }
    }
    
    var negated: LTLToken {
        switch self {
        case .True:
            return .False
        case .False:
            return .True
        case .Or:
            return .And
        case .And:
            return .Or
        case .Next:
            return .Next
        case .Until:
            return .Release
        case .Release:
            return .Until
        case .Eventually:
            return .Globally
        case .Globally:
            return .Eventually
        default:
            assert(false)
            return .EOI
        }
    }
}

func ~= (pattern: CharacterSet, value: UnicodeScalar) -> Bool {
    return pattern.contains(value)
}

struct LTLLexer {
    
    var scanner: ScalarScanner<String.UnicodeScalarView>
    var readPastInput: Bool = false
    
    init(scanner: ScalarScanner<String.UnicodeScalarView>) {
        self.scanner = scanner
    }
    
    mutating func next() throws -> LTLToken {
        
        while !scanner.finished() && CharacterSet.whitespaces.contains(scanner.current()) {
            scanner.next()
        }
        
        if scanner.finished() {
            if readPastInput {
                throw LexerError.UnexpectedEnd
            }
            readPastInput = true
            return .EOI
        }
        
        switch scanner.current() {
        
        // True/False literals
        case "0":
            scanner.next()
            return .False
        case "1":
            scanner.next()
            return .True
        
        // Not
        case "!":
            scanner.next()
            return .Not
        case "~":
            scanner.next()
            return .Not
        
        // And
        case "*":
            scanner.next()
            return .And
        case "&":
            scanner.next()
            if scanner.current() == "&" {
                scanner.next()
            }
            return .And
        case "/":
            scanner.next()
            try expect("\\")
            return .And
        
        // Or
        case "+":
            scanner.next()
            return .Or
        case "|":
            scanner.next()
            if scanner.current() == "|" {
                scanner.next()
            }
            return .Or
        case "\\":
            scanner.next()
            try expect("/")
            return .Or
        
        // Implication
        case "-":
            scanner.next()
            if scanner.current() == "-" {
                scanner.next()
            }
            try expect(">")
            return .Implies
        case "=":
            scanner.next()
            try expect(">")
            return .Implies
        
        // Equivelence
        case "<":
            scanner.next()
            if scanner.current() == ">" {
                // <> is interpreted as eventually
                scanner.next()
                return .Eventually
            }
            
            if scanner.current() == "-" {
                scanner.next()
            } else if scanner.current() == "=" {
                scanner.next()
                try expect(">")
                return .Equivalent
            }
            if scanner.current() == "-" {
                scanner.next()
            }
            try expect(">")
            return .Equivalent
        
        // Next
        case "X":
            scanner.next()
            return .Next
        // the case "()" is handled below 
        
        // Globally
        case "G":
            scanner.next()
            return .Globally
        case "[":
            scanner.next()
            try expect("]")
            return .Globally
        
        // Eventually
        case "F":
            scanner.next()
            return .Eventually
            // the case "<" is handled by implication above
        
        // Until
        case "U":
            scanner.next()
            return .Until
        
        // Release
        case "R":
            scanner.next()
            return .Release
        case "V":
            scanner.next()
            return .Release
        
        // Weak Until
        case "W":
            scanner.next()
            return .WeakUntil
        
        // Paranthesis
        case "(":
            scanner.next()
            if scanner.current() == ")" {
                scanner.next()
                return .Next
            }
            return .LParen
        case ")":
            scanner.next()
            return .RParen
        
        // Propositions
        case CharacterSet.lowercaseLetters:
            var proposition: String = String(scanner.current())
            scanner.next()
            var allowedCharacters = CharacterSet.alphanumerics
            allowedCharacters.insert("_")
            while !scanner.finished() && allowedCharacters.contains(scanner.current()) {
                proposition.append(String(scanner.current()))
                scanner.next()
            }
            if proposition == "true" {
                return .True
            } else if proposition == "false" {
                return .False
            } else {
                return .Proposition(proposition)
            }
        
        default: 
            throw LexerError.UnknownScalar(scanner.current())
        }
    }
    
    mutating func expect(_ char: UnicodeScalar) throws {
        if scanner.current() != char {
            throw LexerError.ExpectScalar(char)
        }
        scanner.next()
    }
    
}

enum LexerError: Error {
    case UnknownScalar(UnicodeScalar)
    case ExpectScalar(UnicodeScalar)
    case UnexpectedEnd
}
