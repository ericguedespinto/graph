## Graph 
## 
## A simple graph library aiming at versatility
## 
## base model: weighted nodes and directed, non-weighted edges
## 
##      (from node) -> (to node)
## 
## weighted model: use nodes as edge weights 
## 
##      (from node) -> (weigthed edge) -> (to node)
## 
## advanced models: hypergraph with multiple (from nodes) and / or multiple (to nodes)
## 
##      [(from node 1), (from node 2] -> (edge node) -> [(to node 1), (to node 2)] 
## 
## A graph is made of a sequence of Option\[Node\]. 
## To delete a node without changing the indices: 
## 
##      nodes[index] = none[Node]()
## 
## A graph is also made of a table of a connection (Conn) object for each node. 
## 
## A connection object has an incoming sequence of indices, and an outgoing sequence of indices, and may have any number of incoming or outgoing indices
## 
## A sub graph is a graph with an additional table of connection objects for foreign indices.
## 
## Use a sub graph to do add a sub graph to a graph, or to add two sub graphs
import std/options
import std/tables
import sequtils
import std/sugar

type 
    Node* = string

    Conn* = object
        incoming*: seq[Natural]
        outgoing*: seq[Natural]

    Graph* = object of RootObj
        nodes*: seq[Option[Node]]
        connections*: Table[Natural, Conn]

    SubGraph* = object of Graph
        outter*: Table[Natural, Conn]

    Direction* = enum 
        Downstream,
        Upstream
    
    SearchPredicate = proc(fromNode, toNode: Option[Node]): bool
    SearchPredicate2 = proc(fromNode, toNode: Option[Node], direction: Direction): bool
    SearchPredicateByIndex = proc(fromIndex, toIndex: Natural): bool
    SearchPredicateByIndex2 = proc(fromIndex, toIndex: Natural, direction: Direction): bool

func newGraph*(): Graph = 
    ## creates a new empty graph
    Graph(nodes: @[], connections: initTable[Natural, Conn]())

func newNode*(graph: Graph, weight: Node): Graph =
    ## creates a new node with a weight, adding it to a graph
    let index = graph.nodes.len
    let new_nodes = concat(graph.nodes, @[some(weight)])
    var new_connections = graph.connections
    new_connections[index] = Conn(
        incoming: @[],
        outgoing: @[]
    )
    result = Graph(
        nodes: new_nodes,
        connections: new_connections
    )

func deleteEdge*(graph: Graph, fromNode, toNode: Natural): Graph
    ## Deletes an edge between to nodes (base model)
    ## 
    ## In weighted and advances models, it deletes the connection between a node and the specific edge weight (removes an incoming or outgoing node from an edge)
    
func deleteNode*(graph: Graph, node: Natural) : Graph =
    ## Deletes a node from a graph
    ## 
    ## and removes the node indice from all its incoming or outgoing edges
    var temp_graph = graph
    for k, v in graph.connections:
        if v.incoming.contains(node):
            temp_graph = temp_graph.deleteEdge(node, k)
        elif v.outgoing.contains(node):
            temp_graph = temp_graph.deleteEdge(k, node)
    var new_nodes : seq[Option[Node]] = @[]
    var new_connections = temp_graph.connections
    for k, v in temp_graph.nodes:
        if k == node:
            new_nodes = new_nodes & @[none(Node)]
        else: 
            new_nodes = new_nodes & @[v]
    result = Graph(
        nodes: new_nodes,
        connections: new_connections
    )

func newEdge*(graph: Graph, fromNode, toNode: Natural): Graph =
    ## Creates an edge between an incoming and an outgoing node (base model)
    ## 
    ## In weighted or advanced models, it connects a node to an incoming or outgoing edge
    var new_connections : Table[Natural, Conn]
    var foundFrom, foundTo = false
    for k, v in graph.connections:
        if k == fromNode:
            new_connections[k] = Conn(
                incoming: v.incoming,
                outgoing: concat(v.outgoing, @[toNode])
            )
            foundFrom = true
        elif k == toNode:
            new_connections[k] = Conn(
                incoming: concat(v.incoming, @[fromNode]),
                outgoing: v.outgoing
            )
            foundTo = true
        else:
            new_connections[k] = v
    if foundFrom == false:
        new_connections[fromNode] = Conn(
            incoming: @[],
            outgoing: @[toNode]
        )
    if foundTo == false:
        new_connections[toNode] = Conn(
            incoming: @[fromNode],
            outgoing: @[]
        )
    result = Graph(
        nodes: graph.nodes,
        connections: new_connections
    )

func addConnectedNode*(graph: Graph, parentNode: Natural, weight: Node): Graph =
    ## Creates a new weighted node and connects it to a parent node (base model)
    ## 
    ## In a weighted or advanced model, it creates a node or edge and connects it to an incoming parent node or edge
    let index = graph.nodes.len
    var graph = graph.newNode(weight)
    graph = graph.newEdge(parentNode, index)
    result = graph

func deleteEdge*(graph: Graph, fromNode, toNode: Natural): Graph =
    var new_connections : Table[Natural, Conn]
    for k, v in graph.connections:
        if k == fromNode:
            new_connections[k] = Conn(
                incoming: v.incoming,
                outgoing: filter(v.outgoing, proc(n: Natural): bool = n != toNode)
            )
        elif k == toNode:
            new_connections[k] = Conn(
                incoming: filter(v.incoming, proc(n: Natural): bool = n != fromNode),
                outgoing: v.outgoing
            )
        else:
            new_connections[k] = v
    result = Graph(
        nodes: graph.nodes,
        connections: new_connections
    )
    
func len*(graph: Graph): int = 
    ## length of graph.nodes, including deleted nodes (and edge weights in weighted or advanced models)
    graph.nodes.len

func orphans*(graph: Graph): seq[Natural] =
    ## Returns all the nodes without incoming or outgoing edges
    for k, v in graph.connections:
        if v.incoming.len == 0 and v.outgoing.len == 0:
            result.add([k])

func roots*(graph: Graph): seq[Natural] =
    ## Returns all root nodes (nodes without incoming edges, but not orphans)
    for k, v in graph.connections:
        if v.incoming.len == 0 and v.outgoing.len != 0:
            result.add([k])

func leafs*(graph: Graph): seq[Natural] =
    ## Returns all leaf nodes (nodes without outgoing edges, but not orphans)
    for k, v in graph.connections:
        if v.incoming.len != 0 and v.outgoing.len == 0:
            result.add([k])

func neighbours*(graph: Graph, node: Natural, forward: bool = true): seq[Natural] =
    ## Returns all connected nodes (or edge weights in weighted or advanced models)
    ## 
    ##      neightbours(graph, node, forward = true) for outgoing nodes
    ## 
    ##      neightbours(graph, node, forward = false) for incoming nodes
    if forward:
        result = graph.connections[node].outgoing
    else:
        result = graph.connections[node].incoming
func predecessors*(graph: Graph, node: Natural): seq[Natural] = 
    ## same as 
    ## 
    ##      neightbours(graph, node, forward = false)
    neighbours graph, node, false
func successors*(graph: Graph, node: Natural): seq[Natural] = 
    ## same as 
    ## 
    ##      neightbours(graph, node, forward = true)
    neighbours graph, node

func search*(
        graph: Graph, 
        start: Natural, 
        valid: SearchPredicate = proc(fromNode, toNode: Option[Node]): bool = true): seq[Natural] =
    ## Returns a sequence of indices for a search (DFS) using a predicate function witch receives an incoming and an outgoing node
    func search1(
        graph: Graph, 
        start: Natural, 
        valid: SearchPredicate = proc(fromNode, toNode: Option[Node]): bool = true,
        visited: seq[Natural] = @[],
        queue: seq[Natural] = @[start]
        ): (seq[Natural], seq[Natural]) =
            let pred = filter(predecessors(graph, start), proc(n: Natural): bool = valid(graph.nodes[n], graph.nodes[start]) and (n notin visited))
            let succ = filter(successors(graph, start), proc(n: Natural): bool = valid(graph.nodes[start], graph.nodes[n]) and (n notin visited))
            let neighbours = deduplicate(pred & succ)
            let new_visited = visited & neighbours
            let new_queue = queue[1..^1] & neighbours
            if (queue.len < 2) and (neighbours.len == 0):
                result = (visited, @[])
            else:
                result = search1(graph, new_queue[0], valid, new_visited, new_queue)
    (result, _) = search1(graph, start, valid)
func search2*(
    graph: Graph,
    start: Natural,
    valid: SearchPredicate2 = proc(fromNode, toNode: Option[Node], direction: Direction): bool = true): seq[Natural] =
    ## Returns a sequence of indices for a search (DFS) using a predicate function witch receives an incoming and an outgoing node, and a direction
    func search3(
        graph: Graph,
        start: Natural,
        valid: SearchPredicate2 = proc(fromNode, toNode: Option[Node], direction: Direction): bool = true,
        visited: seq[Natural] = @[],
        queue: seq[Natural] = @[start]
        ): (seq[Natural], seq[Natural]) =
            let pred = filter(predecessors(graph, start), proc(n: Natural): bool = valid(graph.nodes[n], graph.nodes[start], Upstream) and (n notin visited))
            let succ = filter(successors(graph, start), proc(n: Natural): bool = valid(graph.nodes[start], graph.nodes[n], Downstream) and (n notin visited))
            let neighbours = deduplicate(pred & succ)
            let new_visited = visited & neighbours
            let new_queue = queue[1..^1] & neighbours
            if (queue.len < 2) and (neighbours.len == 0):
                result = (visited, @[])
            else:
                result = search3(graph, new_queue[0], valid, new_visited, new_queue)
    (result, _) = search3(graph, start, valid)

func searchByIndex*(
        graph: Graph, 
        start: Natural, 
        valid: SearchPredicateByIndex = proc(fromIndex, toIndex: Natural): bool = true): seq[Natural] =
    ## Returns a sequence of indices for a search (DFS) using a predicate function witch receives an incoming and an outgoing indices
    func search1(
            graph: Graph, 
            start: Natural, 
            valid: SearchPredicateByIndex = proc(fromIndex, toIndex: Natural): bool = true,
            visited: seq[Natural] = @[start],
            queue: seq[Natural] = @[start]
        ): (seq[Natural], seq[Natural]) =
            {.cast(noSideEffect).}:
                let pred = collect:
                    for n in predecessors(graph, start):
                        if valid(n, start) and (n notin visited): n
                let succ = collect:
                    for n in successors(graph, start):
                        if valid(start, n) and (n notin visited): n
                let neighbours = deduplicate(pred & succ)
                let new_visited = visited & neighbours
                let new_queue = queue[1..^1] & neighbours
                if (queue.len < 2) and (neighbours.len == 0):
                    result = (visited, @[])
                else:
                    result = search1(graph, new_queue[0], valid, new_visited, new_queue)
    (result, _) = search1(graph, start, valid)
func searchByIndex2*(
        graph: Graph, 
        start: Natural, 
        valid: SearchPredicateByIndex2 = proc(fromIndex, toIndex: Natural, direction: Direction): bool = true): seq[Natural] =
    ## Returns a sequence of indices for a search (DFS) using a predicate function witch receives an incoming and an outgoing indices, and a direction
    func search3(
            graph: Graph, 
            start: Natural, 
            valid: SearchPredicateByIndex2 = proc(fromIndex, toIndex: Natural, direction: Direction): bool = true,
            visited: seq[Natural] = @[start],
            queue: seq[Natural] = @[start]
        ): (seq[Natural], seq[Natural]) =
            {.cast(noSideEffect).}:
                let pred = collect:
                    for n in predecessors(graph, start):
                        if valid(n, start, Upstream) and (n notin visited): n
                let succ = collect:
                    for n in successors(graph, start):
                        if valid(start, n, DownStream) and (n notin visited): n
                let neighbours = deduplicate(pred & succ)
                let new_visited = visited & neighbours
                let new_queue = queue[1..^1] & neighbours
                if (queue.len < 2) and (neighbours.len == 0):
                    result = (visited, @[])
                else:
                    result = search3(graph, new_queue[0], valid, new_visited, new_queue)
    (result, _) = search3(graph, start, valid)

func getSubGraph*(
    graph: Graph, 
    start: Natural, 
    valid: SearchPredicate = proc(fromNode, toNode: Option[Node]): bool = true,
    ): SubGraph =
        ## Returns a sub graph from a search (DFS) using a predicate function witch receives an incoming and an outgoing nodes
        var table = initTable[Natural, Natural]()
        table[start] = 0
        let nn = search(graph, start, valid)
        var new_nodes : seq[Option[Node]] = @[graph.nodes[start]]
        var new_connections : Table[Natural, Conn]
        var new_outter : Table[Natural, Conn]
        for n in nn:
            if n != start:
                table[n] = new_nodes.len
                new_nodes = new_nodes & @[graph.nodes[n]]
        for n in nn:
            var cc : Conn = Conn(incoming: @[], outgoing: @[])
            var oc : Conn = Conn(incoming: @[], outgoing: @[])
            for i in graph.connections[n].incoming:
                if table.hasKey(i):
                    cc.incoming = cc.incoming & @[table[i]]
                else:
                    oc.incoming = oc.incoming & @[i]
            for o in graph.connections[n].outgoing:
                if table.hasKey(o):
                    cc.outgoing = cc.outgoing & @[table[o]]
                else:
                    oc.outgoing = oc.outgoing & @[o]
            new_connections[table[n]] = cc
            new_outter[table[n]] = oc
        result = SubGraph(
            nodes: new_nodes,
            connections: new_connections,
            outter: new_outter
        )
func getSubGraph2*(
    graph: Graph, 
    start: Natural, 
    valid: SearchPredicate2 = proc(fromNode, toNode: Option[Node], direction: Direction): bool = true,
    ): SubGraph =
        ## Returns a sub graph from a search (DFS) using a predicate function witch receives an incoming and an outgoing nodes and a direction
        var table = initTable[Natural, Natural]()
        table[start] = 0
        let nn = search2(graph, start, valid)
        var new_nodes : seq[Option[Node]] = @[graph.nodes[start]]
        var new_connections : Table[Natural, Conn]
        var new_outter : Table[Natural, Conn]
        for n in nn:
            if n != start:
                table[n] = new_nodes.len
                new_nodes = new_nodes & @[graph.nodes[n]]
        for n in nn:
            var cc : Conn = Conn(incoming: @[], outgoing: @[])
            var oc : Conn = Conn(incoming: @[], outgoing: @[])
            for i in graph.connections[n].incoming:
                if table.hasKey(i):
                    cc.incoming = cc.incoming & @[table[i]]
                else:
                    oc.incoming = oc.incoming & @[i]
            for o in graph.connections[n].outgoing:
                if table.hasKey(o):
                    cc.outgoing = cc.outgoing & @[table[o]]
                else:
                    oc.outgoing = oc.outgoing & @[o]
            new_connections[table[n]] = cc
            new_outter[table[n]] = oc
        result = SubGraph(
            nodes: new_nodes,
            connections: new_connections,
            outter: new_outter
        )

func getSubGraphByIndex*(
    graph: Graph, 
    start: Natural, 
    valid: SearchPredicateByIndex = proc(fromNod, toNode: Natural): bool = true,
    ): SubGraph =
        ## Returns a sub graph from a search (DFS) using a predicate function witch receives an incoming and an outgoing indices
        var table = initTable[Natural, Natural]()
        table[start] = 0
        let nn = searchByIndex(graph, start, valid)
        var new_nodes : seq[Option[Node]] = @[graph.nodes[start]]
        var new_connections : Table[Natural, Conn]
        var new_outter : Table[Natural, Conn]
        for n in nn:
            if n != start:
                table[n] = new_nodes.len 
                new_nodes = new_nodes & @[graph.nodes[n]]
        for n in nn:
            var cc : Conn = Conn(incoming: @[], outgoing: @[])
            var oc : Conn = Conn(incoming: @[], outgoing: @[])
            for i in graph.connections[n].incoming:
                if table.hasKey(i):
                    cc.incoming = cc.incoming & @[table[i]]
                else:
                    oc.incoming = oc.incoming & @[i]
            for o in graph.connections[n].outgoing:
                if table.hasKey(o):
                    cc.outgoing = cc.outgoing & @[table[o]]
                else:
                    oc.outgoing = oc.outgoing & @[o]
            new_connections[table[n]] = cc
            new_outter[table[n]] = oc
        result = SubGraph(
            nodes: new_nodes,
            connections: new_connections,
            outter: new_outter
        )
func getSubGraphByIndex2*(
    graph: Graph, 
    start: Natural, 
    valid: SearchPredicateByIndex2 = proc(fromNode, toNode: Natural, direction: Direction): bool = true,
    ): SubGraph =
        ## Returns a sub graph from a search (DFS) using a predicate function witch receives an incoming and an outgoing indices and a direction
        var table = initTable[Natural, Natural]()
        table[start] = 0
        let nn = searchByIndex2(graph, start, valid)
        var new_nodes : seq[Option[Node]] = @[graph.nodes[start]]
        var new_connections : Table[Natural, Conn]
        var new_outter : Table[Natural, Conn]
        for n in nn:
            if n != start:
                table[n] = new_nodes.len 
                new_nodes = new_nodes & @[graph.nodes[n]]
        for n in nn:
            var cc : Conn = Conn(incoming: @[], outgoing: @[])
            var oc : Conn = Conn(incoming: @[], outgoing: @[])
            for i in graph.connections[n].incoming:
                if table.hasKey(i):
                    cc.incoming = cc.incoming & @[table[i]]
                else:
                    oc.incoming = oc.incoming & @[i]
            for o in graph.connections[n].outgoing:
                if table.hasKey(o):
                    cc.outgoing = cc.outgoing & @[table[o]]
                else:
                    oc.outgoing = oc.outgoing & @[o]
            new_connections[table[n]] = cc
            new_outter[table[n]] = oc
        result = SubGraph(
            nodes: new_nodes,
            connections: new_connections,
            outter: new_outter
        )

func pinSubGraph*(subGraph: SubGraph, indexSG, indexG: Natural): SubGraph =
    ## Returns a sub graph making two indices coincide 
    ## 
    ## To be used after adding two disjoint subgraphs
    var new_nodes: seq[Option[Node]]
    for i, n in subGraph.nodes:
        if n.isSome:
            if i == indexSG:
                new_nodes.add(none[Node]())
            else:
                new_nodes.add(n)
        else:
            new_nodes.add(none[Node]())
    var new_connections = subGraph.connections
    var new_outter = subGraph.outter
    for k, v in new_connections:
        if v.incoming.contains indexSG:
            new_outter[k].incoming.insert indexG
        if v.outgoing.contains indexSG:
            new_outter[k].outgoing.insert indexG
        new_connections[k] = Conn(
            incoming: v.incoming.filterIt(it != indexSG),
            outgoing: v.outgoing.filterIt(it != indexSG)
        )
    new_connections[indexSG] = Conn(incoming: @[], outgoing: @[])
    new_outter[indexSG] = Conn(incoming: @[], outgoing: @[])
    result = SubGraph(
        nodes: new_nodes,
        connections: new_connections,
        outter: new_outter
    )

func `+`*(graph: Graph, subGraph: SubGraph): Graph = 
    ## Returns a graph resulting from the application of adding a sub graph to a graph
    let graphLen = graph.nodes.len
    var new_nodes = graph.nodes
    var new_connections = graph.connections
    for k, v in subGraph.nodes:
        new_nodes.add [v]
        new_connections[graphLen + k] = Conn(
            incoming: subGraph.connections[k].incoming.mapIt(Natural(it + graphLen)),
            outgoing: subGraph.connections[k].outgoing.mapIt(Natural(it + graphLen))
        )
    for k, v in subGraph.outter:
        let incoming = v.incoming
        let outgoing = v.outgoing
        new_connections[graphLen + k] = Conn(
            incoming: new_connections[graphLen + k].incoming & incoming,
            outgoing: new_connections[graphLen + k].outgoing & outgoing
        )
        for v in incoming:
            new_connections[v].outgoing = new_connections[v].outgoing & @[Natural(graphLen + k)]
        for v in outgoing:
            new_connections[v].incoming = new_connections[v].incoming & @[Natural(graphLen + k)]
    result = Graph(
        nodes: new_nodes,
        connections: new_connections
    )
func `+`*(subGraph: SubGraph, graph: Graph): Graph = graph + subGraph

func `+`*(graph1, graph2: Graph): Graph =
    ## Returns a graph resulting from the application of adding a two disjoint graph
    let graphLen = graph1.nodes.len
    var new_nodes = graph1.nodes & graph2.nodes
    var new_connections = graph1.connections
    for k, v in graph2.connections:
        new_connections[graphLen + k] = Conn(
            incoming: v.incoming.mapIt(Natural(it + graphLen)),
            outgoing: v.outgoing.mapIt(Natural(it + graphLen))
        )
    result = Graph(
        nodes: new_nodes,
        connections: new_connections
    )

func `+`*(subGraph1, subGraph2: SubGraph): SubGraph =
    ## Returns a graph resulting from the application of adding two sub graphs
    let subGraphLen = subGraph1.nodes.len
    var new_nodes = subGraph1.nodes & subGraph2.nodes
    var new_connections = subGraph1.connections
    var new_outter = subGraph1.outter
    for k, v in subGraph2.connections:
        new_connections[subGraphLen + k] = Conn(
            incoming: v.incoming.mapIt(Natural(it + subGraphLen)),
            outgoing: v.outgoing.mapIt(Natural(it + subGraphLen))
        )
    for k, v in subGraph2.outter:
        new_outter[subGraphLen + k] = v
    result = SubGraph(
        nodes: new_nodes,
        connections: new_connections,
        outter: new_outter
    )

func select*(graph: Graph, index: Natural, selector: Node, back: bool = false): Option[Natural] =
    ## Returns the possible (Option) index of a node (or edge weight) described by the selector
    ## 
    ## it always returns the last (single) index
    var next : seq[Natural]
    if back:
        next = graph.predecessors index
    else:
        next = graph.successors index
    for k, v in next:
        if graph.nodes[v] == some(selector):
            result = some(v)

func selectAll*(graph: Graph, index: Natural, selector: Node, back: bool = false): seq[Natural] =
    ## Returns a sequence of all possible (Option) indices of nodes (or edge weights) described by the selector
    var next : seq[Natural]
    if back:
        next = graph.predecessors index
    else:
        next = graph.successors index
    for k, v in next:
        if graph.nodes[v] == some(selector):
            result = result & @[v]

func select*(graph: Graph, start: Natural, selectors: openArray[Node], back: bool = false): Option[Natural] =
    ## Returns the possible (Option) index of a node (or edge weight) described by the any of the selectors
    ## 
    ## it always returns the last (single) index
    var start = start
    for v in selectors:
        result = graph.select(start, v, back)
        if result.isNone:
            return result
        else:
            start = result.get

func selectAny*(graph: Graph, start: Natural, selectors: openArray[Node], back: bool = false): seq[Natural] =
    ## Returns a sequence of all the possible (Option) indices of nodes (or edge weights) described by the any of the selectors
    for s in selectors:
        let r = select(graph, start, s, back)
        if r.isSome:
            result.add r.get

proc `$`*(graph: Graph): string =
    ## prints a pretty formatted string describing a graph
    for i, n in graph.nodes:
        result &= $i & ": " & $n & $(graph.connections[i]) & "\n"

proc `$`*(subGraph: SubGraph): string =
    ## prints a pretty formatted string describing a sub graph
    result = $(Graph(subGraph))
    result &= "Outter:\n"
    for i, n in subGraph.outter:
        result &= $i & ": " & $(subGraph.outter[i]) & "\n"

when (isMainModule):
    let g = newGraph()
            .newNode(Node("Ola")) 
            .newNode(Node("tudo?"))
            .newNode(Node("tudo"))
            .newNode(Node("assim assim"))
            .newEdge(0,1)
            .newNode(Node("?"))
            .newEdge(1,2)
            .newEdge(1,3)
            .newEdge(2,4)

    assert g.orphans == @[]
    assert g.roots.mapIt(int(it)) == @[0]
    assert g.leafs.mapIt(int(it)) == @[4, 3]
    assert predecessors(g, 1).mapIt(int(it)) == @[0]
    assert successors(g, 1).mapIt(int(it)) == @[2, 3]
    assert search(g, 0).mapIt(int(it)) == @[1, 0, 2, 3, 4]

    proc validBut(fromNode: Option[Node], toNode: Option[Node]): bool =
        if toNode == some("tudo?"):
            result = false
        else:
            result = true

    assert getSubGraph(g, 4, validBut) + g == g + getSubGraph(g, 4, validBut)
    assert getSubGraph(g, 4, validBut) + getSubGraph(g, 4, validBut) + g == getSubGraph(g, 4, validBut) + g + getSubGraph(g, 4, validBut)
    
    proc validBut2(fromNode: Option[Node], toNode: Option[Node], direction: Direction): bool =
        if toNode == some("tudo?"):
            result = false
        else:
            result = true

    assert getSubGraph2(g, 4, validBut2) + g == g + getSubGraph2(g, 4, validBut2)
    assert getSubGraph2(g, 4, validBut2) + getSubGraph2(g, 4, validBut2) + g == getSubGraph2(g, 4, validBut2) + g + getSubGraph2(g, 4, validBut2)

    assert g.select(4, [Node("tudo"), Node("tudo?"), Node("Ola")], back = true) == some(Natural(0))
    assert g.select(0, [Node("tudo?"), Node("tudo")]) == some(Natural(2))