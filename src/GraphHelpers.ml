open Graph
module EventGraph = Imperative.Digraph.Concrete(struct
  type t = int
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end)
open EventGraph
module EventGraphBuilder = Builder.I(EventGraph)
module EventGraphOps = Oper.Make(EventGraphBuilder)

let transitive_closure edges =
  let g = EventGraph.create () in
  let _ = List.map (fun (l, r) -> EventGraph.add_edge g l r) edges in
  let g = EventGraphOps.transitive_closure g in
  EventGraph.fold_edges (fun l r acc -> (l, r)::acc) g []

let reflexive_closure edges =
  let g = EventGraph.create () in
  let _ = List.map (fun (l, r) ->
      EventGraph.add_edge g l r;
      EventGraph.add_edge g l l;
      EventGraph.add_edge g r r;
    ) edges in
  EventGraph.fold_edges (fun l r acc -> (l, r)::acc) g []

let rtransitive_closure edges =
  let g = EventGraph.create () in
  let _ = List.map (fun (l, r) ->
      EventGraph.add_edge g l r;
      EventGraph.add_edge g l l;
      EventGraph.add_edge g r r;
    ) edges in
  let g = EventGraphOps.transitive_closure g in
  EventGraph.fold_edges (fun l r acc -> (l, r)::acc) g []

let symmetric_closure edges =
  let g = EventGraph.create () in
  let _ = List.map (fun (l, r) -> EventGraph.add_edge g l r) edges in
  let g' = EventGraphOps.mirror g in
  let g = EventGraphOps.union g g' in
  EventGraph.fold_edges (fun l r acc -> (l, r)::acc) g []
