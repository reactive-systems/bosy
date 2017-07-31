import Foundation
import Dispatch


public enum Phase: CustomStringConvertible {
    case parsing
    case ltl2automaton
    case automatonOptimizations
    case constraintGeneration
    case solving
    case solutionExtraction
    
    public static let allValues: [Phase] = [
        .parsing,
        .ltl2automaton,
        .automatonOptimizations,
        .constraintGeneration,
        .solving,
        .solutionExtraction
    ]
    
    // Conformance to CustomStringConvertible
    public var description: String {
        switch self {
        case .parsing:
            return "Parsing"
        case .ltl2automaton:
            return "LTL2Automaton"
        case .automatonOptimizations:
            return "AutomatonOptimization"
        case .constraintGeneration:
            return "ConstraintGeneration"
        case .solving:
            return "Solving"
        case .solutionExtraction:
            return "SolutionExtraction"
        }
    }
}



public class BoSyStatistics: CustomStringConvertible {
    
    var durations: [Phase:[Double]] = [:]
    
    public struct Timer {
        let statistics: BoSyStatistics
        let phase: Phase
        let begin: UInt64  // nanoseconds
        
        public func stop() {
            let end = DispatchTime.now().uptimeNanoseconds
            let time = Double(end - begin) / 1_000_000_000
            statistics.add(phase: phase, duration: time)
        }
    }
    
    public func startTimer(phase: Phase) -> Timer {
        return Timer(
            statistics: self,
            phase: phase,
            begin: DispatchTime.now().uptimeNanoseconds
        )
    }
    
    func add(phase: Phase, duration: Double) {
        var measurements: [Double] = durations[phase] ?? []
        measurements.append(duration)
        durations[phase] = measurements
    }
    
    // Conformance to CustomStringConvertible
    public var description: String {
        var stat = "\nStatistics\n"
        let maximalName = Phase.allValues.map({ $0.description.characters.count }).reduce(0, { max($0 ,$1) })
        for phase in Phase.allValues {
            guard let measurements = durations[phase] else {
                continue
            }
            let padding = String(repeating: " ", count: maximalName - phase.description.characters.count)
            let total = measurements.reduce(0, +)
            let average = total / Double(measurements.count)
            let totalFormat = String(format: "%.4f", total)
            let averageFormat = String(format: "%.4f", average)
            stat += "  \(phase):\(padding) \(measurements.count) times, \(totalFormat) total, \(averageFormat) average\n"
        }
        return stat
    }
}
