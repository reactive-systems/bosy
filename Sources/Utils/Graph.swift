public protocol GraphRepresentable {
    associatedtype State: Hashable
    var states: Set<State> { get }
    var edges: [State: [State]] { get }
}

public struct Graph: GraphRepresentable {
    public typealias State = String
    public var states: Set<State>
    public var edges: [State: [State]]
    
    public init(states: Set<State>, edges: [State: [State]]) {
        self.states = states
        self.edges = edges
    }
}

public func trajan<T: GraphRepresentable>(graph: T) -> [[T.State]] {
    var index = 0
    var indices: [T.State:Int] = [:]
    var lowlink: [T.State:Int] = [:]
    var stack: [T.State] = []
    
    var components: [[T.State]] = []
    
    func strongconnect(_ graph: T, state: T.State) {
        indices[state] = index
        lowlink[state] = index
        index += 1
        stack.append(state)
        
        if let successors = graph.edges[state] {
            for successor in successors {
                if indices[successor] == nil {
                    // Successor has not yet been visited; recurse on it
                    strongconnect(graph, state: successor)
                    lowlink[state] = min(lowlink[state]!, lowlink[successor]!)
                } else if stack.contains(successor) {
                    // Successor w is in stack S and hence in the current SCC
                    assert(lowlink[successor] != nil)
                    lowlink[state] = min(lowlink[state]!, indices[successor]!)
                }
            }
        }
        
        // If state is a root node, pop the stack and generate an SCC
        if lowlink[state] == indices[state] {
            var component: [T.State] = []
            var state2: T.State
            repeat {
                state2 = stack.removeLast()
                component.append(state2)
            } while (state != state2)
            components.append(component)
        }
    }
    
    for state in graph.states {
        if indices[state] == nil {
            strongconnect(graph, state: state)
        }
    }
    
    return components
}
