
open Core.Std
open Utils
open Paramecium
open Formula
open InvFinder




type flowpath =
  | FlowPath of string * string * formula

let flowPath form rname branch = FlowPath(form, rname, branch)


(*  key: string of the formula state
    value: tuple of
      id,
      formula,
      components of the formula,
      string format of the components,
      flowpath of states called enders which are endstate of this state
    -- means that the initial state has only enders, and terminate state has nothing
*)
let state_table = Hashtbl.create ~hashable:String.hashable ()

let discovered = Queue.create ()




let component_is_parameterized form =
  match form with
  | Chaos
  | Miracle -> false
  | Eqn(Var(Arr(ls1)), Var(Arr(ls2)))
  | Neg(Eqn(Var(Arr(ls1)), Var(Arr(ls2)))) ->
    List.exists (ls1@ls2) ~f:(fun (_, ps) -> not (List.is_empty ps))
  | Eqn(Var(Arr(ls)), _)
  | Eqn(_, Var(Arr(ls)))
  | Neg(Eqn(Var(Arr(ls)), _))
  | Neg(Eqn(_, Var(Arr(ls)))) ->
    List.exists ls ~f:(fun (_, ps) -> not (List.is_empty ps))
  | _ -> raise Empty_exception


let find_repeat_state core_var_strs new_state parent_state_str =
  let (_, _, _, p_com_strs, _) =
    Hashtbl.find_exn state_table parent_state_str
  in
  let new_state_com_strs = List.filter_map (flat_and_to_list new_state) ~f:(fun com ->
    let com_str = ToStr.Smv.form_act com in
    let paramed = component_is_parameterized com in
    let is_new = (List.for_all p_com_strs ~f:(fun ps -> not (ps = com_str))) in
    let contains_core =
      match com with
      | Chaos
      | Miracle -> false
      | Eqn(Var(v1), Var(v2))
      | Neg(Eqn(Var(v1), Var(v2))) ->
        List.exists core_var_strs ~f:(fun vs ->
          vs = ToStr.Smv.var_act v1 || vs = ToStr.Smv.var_act v2
        )
      | Eqn(Var(v), _)
      | Eqn(_, Var(v))
      | Neg(Eqn(Var(v), _))
      | Neg(Eqn(_, Var(v))) ->
        List.exists core_var_strs ~f:(fun vs -> vs = ToStr.Smv.var_act v)
      | _ -> raise Empty_exception
    in
    if (paramed && is_new) || contains_core then Some com_str else None
  ) in
  let rec wrapper queue accessed =
    match queue with
    | [] -> None
    | q::queue' ->
      let (_, _, _, com_strs, paths) = Hashtbl.find_exn state_table q in
      if List.exists com_strs ~f:(fun cs ->
        List.exists new_state_com_strs ~f:(fun ncs -> cs = ncs)
      ) then
        Some q
      else begin
        let accessed' = String.Set.add accessed q in
        let new_parents = List.filter_map paths ~f:(fun (FlowPath(form, _, _)) ->
          if String.Set.exists accessed' ~f:(fun a -> a = form) then None else Some form
        ) in
        wrapper (queue'@new_parents) accessed'
      end
  in
  match wrapper [parent_state_str] String.Set.empty with
  | None -> List.find (Hashtbl.keys state_table) ~f:(fun s -> s = ToStr.Smv.form_act new_state)
  | Some(s) -> Some s


let add_new_state state paths =
  let id = Hashtbl.length state_table in
  let coms = flat_and_to_list state in
  let com_strs = List.map coms ~f:ToStr.Smv.form_act in
  let data = (id, state, coms, com_strs, paths) in
  let key = ToStr.Smv.form_act state in
  print_endline (sprintf "%d: %s" id key);
  Hashtbl.add_exn state_table ~key ~data


let access_rule core_var_strs startF endF r =
  let endF_str = ToStr.Smv.form_act endF in
  let Rule(rn, _, g, s) = r in
  let assigns = statement_2_assigns s in
  let endF' = pre_cond endF assigns in
  let useful = List.filter endF' ~f:(fun (branch, end_form) ->
    let changed = not (endF_str = ToStr.Smv.form_act end_form) in
    let form_to_check = neg (simplify (andList [g; branch; end_form])) in
    let is_sat = not (Smv.is_inv (ToStr.Smv.form_act form_to_check)) in
    changed && is_sat
  ) in
  let rec wrapper ends =
    match ends with
    | [] -> ()
    | (branch, end_form)::ends' ->
      let startF_str = ToStr.Smv.form_act startF in
      if is_tautology (imply (andList [g; branch]) startF) then
        let (id, f, coms, com_strs, enders) = Hashtbl.find_exn state_table startF_str in
        let data = (id, f, coms, com_strs, enders@[flowPath endF_str rn branch]) in
        (*print_endline ("bingo!!! rule: "^rn^"; end - "^endF_str);*)
        Hashtbl.replace state_table ~key:startF_str ~data
      else begin
        let new_state = simplify (andList [g; branch; end_form]) in
        let new_state_str = ToStr.Smv.form_act new_state in
        match find_repeat_state core_var_strs new_state endF_str with
        | None ->
          (*print_endline ("path!!! rule: "^rn^"; new - "^new_state_str^"; end - "^endF_str);*)
          Queue.enqueue discovered new_state_str;
          add_new_state new_state [flowPath endF_str rn branch]
        | Some(p) ->
          (*print_endline ("path!!! rule: "^rn^"; old - "^new_state_str^"; end - "^endF_str);*)
          let (id, f, coms, com_strs, enders) = Hashtbl.find_exn state_table p in
          let data = (id, f, coms, com_strs, enders@[flowPath endF_str rn branch]) in
          Hashtbl.replace state_table ~key:p ~data
      end;
      wrapper ends'
  in
  wrapper useful


let remove_unreachable table startF =
  let startF_str = ToStr.Smv.form_act startF in
  let res_table = Hashtbl.create ~hashable:String.hashable () in
  let q = Queue.create () in
  Queue.enqueue q startF_str;
  while not (Queue.is_empty q) do
    let state = Queue.dequeue_exn q in
    let (_, state_form, coms, com_strs, paths) = Hashtbl.find_exn table state in
    let data = (Hashtbl.length res_table, state_form, coms, com_strs, paths) in
    Hashtbl.add_exn res_table ~key:state ~data;
    List.fold ~init:() paths ~f:(fun res (FlowPath(form_str, _, _)) ->
      if List.exists (Hashtbl.keys res_table) ~f:(fun s -> s = form_str) then
        res
      else begin
        Queue.enqueue q form_str; res
      end
    )
  done;
  res_table


let bfs core_vars startF endF rs =
  add_new_state startF [];
  add_new_state endF [];
  Queue.enqueue discovered (ToStr.Smv.form_act endF);
  let core_var_strs = List.map core_vars ~f:ToStr.Smv.var_act in
  while not (Queue.is_empty discovered) do
    let state = Queue.dequeue_exn discovered in
    let (_, state_form, _, _, _) = Hashtbl.find_exn state_table state in
    List.fold ~init:() rs ~f:(fun res r -> access_rule core_var_strs startF state_form r; res)
  done;
  remove_unreachable state_table startF


let table_to_dot table =
  let content = Hashtbl.fold table ~init:"" ~f:(fun ~key:_ ~data:(id, _, _, _, paths) res ->
    let part = String.concat (List.map paths ~f:(fun (FlowPath(form, rn, branch)) ->
      let (dest_id, _, _, _, _) = Hashtbl.find_exn table form in
      let label = sprintf "%s, %s" rn (ToStr.Smv.form_act branch) in
      let state_type = if dest_id = 1 then "doublecircle" else "circle" in
      sprintf "node [shape = %s]; %d -> %d [label = \"%s\"];\n  " state_type id dest_id label
    )) in
    res^part
  ) in
  sprintf "
digraph finite_state_machine {
  rankdir = LR;
  size = \"16, 12\";
  %s
}
" content





