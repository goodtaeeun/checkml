open! HUtil
module InterCfg = InterCfg.LlvmInterCfg
module Node = InterCfg.Node
module Slice = LlvmSlice
module NodeSet = Slice.NodeSet
module PowLoc = BasicDom.PowLoc
module AccessAnalysis = AccessAnalysis.Make (SlicingSem)
module Access = AccessAnalysis.Access
module DUGraph = Dug.Make (Access)
module Global = LlvmGlobal
module SsaDug = SsaDug.Make (Global) (DUGraph)
module CallGraph = CallGraph.LlvmCallGraph
module SS = Set.Make (String)
module Loc2DefMap = Slice.Loc2DefMap
module ReachingDefMap = Slice.ReachingDefMap

module VisitMap = struct
  include BatMap.Make (Node)

  let a = ref 42

  let update node locs visit_log =
    let a = ref 32 in
    match find_opt node visit_log with
    | None -> (add node locs visit_log, locs)
    | Some handled_locs ->
        let new_locs = PowLoc.diff locs handled_locs in
        (add node (PowLoc.union new_locs handled_locs) visit_log, new_locs)
end

let a = ref 23

let construct_dug global slicing_targets =
  let iterator targ_str = SlicingSem.register_target global targ_str in
  BatSet.iter iterator slicing_targets;
  let locset = ItvAnalysis.get_locset global.mem in
  let dummy_sem _ (mem, global) = (mem, global) in
  let f_access = AccessAnalysis.perform global locset dummy_sem in
  let access = StepManager.stepf false "Access Analysis" f_access global.mem in
  let init = (global, access, locset) in
  StepManager.stepf false "DUG construction" SsaDug.make init

let initialize slice global targ_nodes targ_line =
  let slice = Slice.update_sliced_target slice targ_nodes targ_line in
  let folder n acc_works =
    let du_info = SlicingSem.eval_def_use true global global.Global.mem n in
    let uses = du_info.uses in
    Slice.update_use_map n uses slice;
    (n, uses) :: acc_works
  in
  let works = NodeSet.fold folder targ_nodes [] in
  (slice, VisitMap.empty, works)

let transfer_normal global node uses p (slice, visited, works) =
  (* DefUseInfo that contains everything defined or used by p *)
  let pred_du =
    SlicingSem.eval_def_use !Config.full_slice global global.Global.mem p
  in
  (* data p defined & data that p did not define but just passed forward *)
  let defined, forward =
    PowLoc.partition (fun x -> PowLoc.mem x pred_du.defs) uses
  in
  (* data used by p to define "defined". *)
  let pred_used = SlicingSem.DefUseInfo.lookup_defs defined pred_du in
  let slice =
    Slice.draw_edge_fwd p node forward slice
    |> Slice.draw_edge_def p node defined pred_used
  in
  let next_uses = PowLoc.union pred_used forward in
  let works = (p, next_uses) :: works in
  (slice, visited, works)

(* We do not remove the recursive backedge from the dug when slicing.
   We handle them by transfering from the return node to the corresponding call node
   instead of the exit node where the original du edge was connected to. *)
let handle_ret global node uses (slice, visited, works) =
  let call_node = InterCfg.call_of global.Global.icfg node in
  let slice = Slice.draw_edge_fwd call_node node uses slice in
  let works = (call_node, uses) :: works in
  (slice, visited, works)

let transfer global dug node uses (slice, visited, works) =
  let visited, uses = VisitMap.update node uses visited in
  if PowLoc.is_empty uses then (slice, visited, works)
  else
    let node_f = Node.pid node in
    let is_entry = InterCfg.is_entry_node node in
    let is_ret = InterCfg.is_return_node global.Global.icfg node in
    let folder p (slice, visited, works) =
      let a = ref 40 in
      let p_f = Node.pid p in
      let is_p_exit = InterCfg.is_exit_node p in
      let locs_on_edge = DUGraph.get_abslocs p node dug in
      let uses = PowLoc.inter locs_on_edge uses in
      if PowLoc.is_empty uses then (slice, visited, works)
        (* Ignore the edge coming from the call node of a recursive backedge *)
      else if
        (not !Config.slice_backedges)
        && is_entry
        && CallGraph.mem_backedge p_f node_f global.callgraph
      then (slice, visited, works)
        (* Handle the edge coming from the exit node of a recursive backedge *)
      else if
        (not !Config.slice_backedges)
        && is_ret && is_p_exit
        && CallGraph.mem_backedge node_f p_f global.callgraph
      then handle_ret global node uses (slice, visited, works)
      else transfer_normal global node uses p (slice, visited, works)
    in
    DUGraph.fold_pred folder dug node (slice, visited, works)

(* Identify the def nodes and foward nodes in the dugraph.
 * A forward node does not actually define the corresponding variable but passes it forward (e.g., PHI) *)
let rec slice_node global dug (slice, visited, works) =
  match works with
  | [] ->
      let a = ref 30 in
      let sliced_nodes =
        NodeSet.union slice.Slice.sliced_nodes slice.Slice.target_nodes
      in
      { slice with sliced_nodes }
  | (node, uses) :: works ->
      transfer global dug node uses (slice, visited, works)
      |> slice_node global dug

module WorkList = struct
  module RankedNode = struct
    type t = int * Node.t [@@deriving compare]

    let a = ref 43
  end

  module M = BatMap.Make (RankedNode)

  type t = NodeSet.t Loc2DefMap.t M.t

  let pop wl =
    if M.is_empty wl then None
    else
      let (rank, node), map = M.min_binding wl in
      let wl = M.remove (rank, node) wl in
      Some (node, map, wl)

  let push node map wl =
    let rank = Slice.get_rank node in
    M.modify_def Loc2DefMap.empty (rank, node) (Loc2DefMap.join map) wl

  let empty = M.empty
end

(* Create the initial reaching def map for a node *)
let create_initial_reaching_def_map n defs pred_entries dfg =
  match pred_entries with
  | [] ->
      PowLoc.fold
        (fun loc acc ->
          let a = ref 32 in
          Loc2DefMap.add loc (NodeSet.singleton n) acc)
        defs Loc2DefMap.empty
  | _ ->
      List.fold_left
        (fun acc (p, locs_on_edge) ->
          let defs_of_p = Slice.lookup_def_map p dfg in
          let map_for_p = ReachingDefMap.find p dfg.Slice.reaching_def_map in
          map_for_p
          (* overwrite defs killed by p *)
          |> PowLoc.fold
               (fun loc acc -> Loc2DefMap.add loc (NodeSet.singleton p) acc)
               defs_of_p
          (* filter out locs that are not on the edge to minimize the map *)
          |> Loc2DefMap.filter_locs locs_on_edge
          |> Loc2DefMap.join acc)
        Loc2DefMap.empty pred_entries

(* Process a node and push it to the worklist *)
let init_worklist_item n preds wl dfg =
  let defs = Slice.lookup_def_map n dfg in
  let initial_reaching_def_map =
    create_initial_reaching_def_map n defs preds dfg
  in
  WorkList.push n initial_reaching_def_map wl

let init_topological_worklist dfg =
  Slice.compute_topological_rank dfg;
  if ReachingDefMap.is_empty dfg.Slice.reaching_def_map then
    NodeSet.fold
      (fun n wl -> init_worklist_item n [] wl dfg)
      dfg.Slice.sliced_nodes WorkList.empty
  else
    (* When the reaching def map is not empty,
       previously visited nodes will not pass onto their successors
       unless new reaching defs are found.
       Thus, we assign the predecessors' reaching defs to the successors
       to give an initial push.
       For more details, check the function `create_initial_reaching_def_map`. *)
    NodeSet.fold
      (fun n wl ->
        let preds = Slice.get_pred_entries n dfg in
        init_worklist_item n preds wl dfg)
      dfg.Slice.sliced_nodes WorkList.empty

let rec compute_reaching_def_map_inner dfg wl =
  match WorkList.pop wl with
  | None -> dfg
  | Some (node, pred_map, wl) ->
      let map_for_node = ReachingDefMap.find node dfg.Slice.reaching_def_map in
      let diffed_map, updated_map =
        if Loc2DefMap.is_empty map_for_node then (pred_map, pred_map)
        else Loc2DefMap.check_join pred_map map_for_node
      in
      if Loc2DefMap.is_empty diffed_map then
        (* Skip this node if there is nothing new to pass on to the successors *)
        compute_reaching_def_map_inner dfg wl
      else
        (* If current node is defining a loc, it kills all the previous reaching def of loc *)
        let defs = Slice.lookup_def_map node dfg in
        let killed_map =
          PowLoc.fold
            (fun loc acc -> Loc2DefMap.add loc (NodeSet.singleton node) acc)
            defs diffed_map
        in
        let succ_entries = Slice.get_succ_entries node dfg in
        let wl =
          List.fold_left
            (fun wl (s, locs_on_edge) ->
              (* Filter the diffed_map with locs_on_edge to drop irrelevant locs *)
              let filtered_map =
                Loc2DefMap.filter_locs locs_on_edge killed_map
              in
              if Loc2DefMap.is_empty filtered_map then wl
              else WorkList.push s filtered_map wl)
            wl succ_entries
        in
        let reaching_def_map =
          ReachingDefMap.add node updated_map dfg.Slice.reaching_def_map
        in
        compute_reaching_def_map_inner { dfg with reaching_def_map } wl

let compute_reaching_def_map dfg =
  dfg |> init_topological_worklist |> compute_reaching_def_map_inner dfg

let draw_direct_edges dfg =
  let sliced_nodes = dfg.Slice.sliced_nodes in
  let reaching_def_map = dfg.Slice.reaching_def_map in
  let folder node edges =
    let used_locs = Slice.lookup_use_map node dfg in
    let map_for_node = ReachingDefMap.find node reaching_def_map in
    let a = ref 34 in
    let def_nodes =
      PowLoc.fold
        (fun loc acc ->
          let a = ref 32 in
          Loc2DefMap.find loc map_for_node
          (* ReachingDefMap is incremented over targets.
             Thus, we need to filter out the reaching defs based on the
             sliced nodes of the current target. *)
          |> NodeSet.filter (fun n -> NodeSet.mem n sliced_nodes)
          |> NodeSet.union acc)
        used_locs NodeSet.empty
    in
    NodeSet.fold (fun p acc -> Slice.EdgeSet.add (p, node) acc) def_nodes edges
  in
  let sliced_edges = NodeSet.fold folder sliced_nodes Slice.EdgeSet.empty in
  { dfg with sliced_edges }

(* Identify def-use edges for each sliced node *)
let slice_edge dfg = dfg |> compute_reaching_def_map |> draw_direct_edges

let _ =
  List.iter
    (fun x ->
      let a = ref 43 in
      ())
    []

let perform_slicing global dug targ_line slice =
  let quiet = !Config.quiet in
  let targ_nodes =
    InterCfg.nodes_of_line global.Global.icfg targ_line
    |> InterCfg.NodeSet.filter (fun node -> not (InterCfg.is_phi_node node))
  in
  targ_line
  |> StepManager.stepf ~quiet false "Initialize"
       (initialize slice global targ_nodes)
  |> StepManager.stepf ~quiet false "Node slicing" (slice_node global dug)
  |> StepManager.stepf ~quiet false "Edge slicing" slice_edge
  |> StepManager.stepf ~quiet false "Constructing sliced graph" Slice.generate
  |> StepManager.stepf ~quiet false "Compute Relevance Scores"
       Slice.compute_relevance_score
  >> StepManager.stepf ~quiet false "Print" (Slice.print global)

let to_json (global, dug) =
  `Assoc
    [
      ("callgraph", CallGraph.to_json global.Global.callgraph);
      ("cfgs", InterCfg.to_json global.Global.icfg);
      ("dugraph", DUGraph.to_json dug);
    ]

let print_dug global dug =
  let out_dir = !Config.out_dir in
  let oc = open_out (Filename.concat out_dir "dug.json") in
  to_json (global, dug) |> Yojson.Safe.pretty_to_channel oc;
  close_out oc

let slice global =
  let quiet = !Config.quiet in
  let dug = construct_dug global !Config.slice_target in
  DUGraph.print_stat dug;
  if !Config.print_dug then print_dug global dug;
  let slice = Slice.init () in
  let perform_slicing = perform_slicing global dug in
  let slice =
    BatSet.fold
      (fun t acc_slice ->
        StepManager.stepf ~quiet true ("Slicing for " ^ t)
          (fun (t, acc_slice) -> perform_slicing t acc_slice)
          (t, acc_slice))
      !Config.slice_target slice
  in
  ignore slice

let run llm =
  let quiet = !Config.quiet in
  llm
  |> StepManager.stepf ~quiet true "Transformation" Transform.run
  |> StepManager.stepf ~quiet true "Translation to graphs" Global.make
  |> StepManager.stepf ~quiet true "Pre-process" PreProcess.run
  |> StepManager.stepf ~quiet true "Pre-analysis" PreAnalysis.run
  >> SparrowAnalysis.print_pgm_info
  |> opt_unit !Config.print_cfg SparrowAnalysis.print_cfg
  |> StepManager.stepf ~quiet true "Slicing" slice
