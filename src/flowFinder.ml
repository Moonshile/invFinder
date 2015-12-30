
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
  | Eqn(Var(Arr(ls)), _)
  | Neg(Eqn(Var(Arr(ls)), _)) -> List.exists ls ~f:(fun (_, ps) -> not (List.is_empty ps))
  | _ -> raise Empty_exception



let find_repeat_state new_state parent_state_str =
  let (p_state, p_coms, p_com_strs, paths) =
    Hashtbl.find_exn state_table parent_state_str
  in
  let new_state_com_strs = List.filter_map (flat_and_to_list new_state) ~f:(fun com ->
    let com_str = ToStr.Smv.form_act com in
    let paramed = component_is_parameterized com in
    let is_new = (List.for_all p_com_strs ~f:(fun ps -> not (ps = com_str))) in
    if paramed && is_new then Some com_str else None
  ) in
  let rec wrapper queue accessed =
    match queue with
    | [] -> None
    | q::queue' ->
      let (state, coms, com_strs, paths) = Hashtbl.find_exn state_table q in
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
  let coms = flat_and_to_list state in
  let com_strs = List.map coms ~f:ToStr.Smv.form_act in
  let data = (state, coms, com_strs, paths) in
  Hashtbl.add_exn state_table ~key:(ToStr.Smv.form_act state) ~data


let access_rule startF endF r =
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
        let (f, coms, com_strs, enders) = Hashtbl.find_exn state_table startF_str in
        let data = (f, coms, com_strs, enders@[flowPath endF_str rn branch]) in
        print_endline ("bingo!!! rule: "^rn^"; end - "^endF_str);
        Hashtbl.replace state_table ~key:startF_str ~data
      else begin
        let new_state = simplify (andList [g; branch; end_form]) in
        let new_state_str = ToStr.Smv.form_act new_state in
        match find_repeat_state new_state endF_str with
        | None ->
          print_endline ("path!!! rule: "^rn^"; new - "^new_state_str^"; end - "^endF_str);
          Queue.enqueue discovered new_state_str;
          add_new_state new_state [flowPath endF_str rn branch]
        | Some(p) ->
          print_endline ("path!!! rule: "^rn^"; old - "^new_state_str^"; end - "^endF_str);
          let (f, coms, com_strs, enders) = Hashtbl.find_exn state_table p in
          let data = (f, coms, com_strs, enders@[flowPath endF_str rn branch]) in
          Hashtbl.replace state_table ~key:p ~data
      end;
      wrapper ends'
  in
  wrapper useful


let bfs startF endF rs =
  add_new_state startF [];
  add_new_state endF [];
  Queue.enqueue discovered (ToStr.Smv.form_act endF);
  while not (Queue.is_empty discovered) do
    let state = Queue.dequeue_exn discovered in
    let (state_form, _, _, _) = Hashtbl.find_exn state_table state in
    List.fold ~init:() rs ~f:(fun res r -> access_rule startF state_form r; res)
  done;
  state_table











(*
(*  key: string of the formula
    value: tuple of
      formula,
      flowpath of states called enders which are endstate of this state
    -- means that the initial state has only enders, and terminate state has nothing
*)
let state_table = Hashtbl.create ~hashable:String.hashable ()

let accessed = Hash_set.create ~hashable:String.hashable ()

let discovered = Queue.create ()

(*  key: string of a formula
    value: string of the formula that represents all of the formulae equals to it
*)
let eqn_table = Hashtbl.create ~hashable:String.hashable ()

let state_tbl_str_imply fs1 f2 =
  match Hashtbl.find state_table fs1 with
  | None -> false
  | Some(f1, _) -> 
    can_imply f2 f1 = 0

let access_rule startF endF r ~types =
  let endF_str = ToStr.Smv.form_act endF in
  let Rule(rn, _, g, s) = r in
  let assigns = statement_2_assigns s in
  let endF' = pre_cond endF assigns in
  let useful = List.filter endF' ~f:(fun (branch, end_form) ->
    let changed = not (endF = end_form) in
    let form_to_check = neg (normalize (simplify (andList [g; branch; end_form])) ~types) in
    let is_sat = not (Smv.is_inv (ToStr.Smv.form_act form_to_check)) in
    changed && is_sat
  ) in
  let rec wrapper ends =
    match ends with
    | [] -> ()
    | (branch, end_form)::ends' ->
      let startF_str = ToStr.Smv.form_act startF in
      if is_tautology (imply (andList [g; branch]) startF) then
        let (f, enders) = Hashtbl.find_exn state_table startF_str in
        let data = (f, enders@[flowPath (ToStr.Smv.form_act endF) r branch]) in
        print_endline ("bingo!!! rule: "^rn^"; end - "^endF_str);
        Hashtbl.replace state_table ~key:startF_str ~data
      else begin
        let new_state = normalize (simplify (andList [g; branch; end_form])) ~types in
        let new_state_str = ToStr.Smv.form_act new_state in
        let real_new_state_str =
          match Hashtbl.find eqn_table new_state_str with
          | Some(s) -> s
          | None -> begin
            match List.find (Hashtbl.keys state_table) ~f:(fun s -> state_tbl_str_eqn s new_state) with
            | Some(s) -> s
            | None -> new_state_str
          end
        in
        print_endline ("path!!! rule: "^rn^"; new - "^real_new_state_str^"; end - "^endF_str);
        let exists_in_accessed = Hash_set.exists accessed ~f:(fun s -> s = real_new_state_str) in
        let exists_in_discovered = Queue.exists discovered ~f:(fun s -> s = real_new_state_str) in
        if exists_in_accessed && not (symmetry_form new_state startF = 0) then
          Prt.warning "Circle detected!!!" 
        else begin 
          ()
        end;
        if exists_in_accessed || exists_in_discovered then
          let (f, enders) = Hashtbl.find_exn state_table real_new_state_str in
          let data = (f, enders@[flowPath (ToStr.Smv.form_act endF) r branch]) in
          Hashtbl.replace state_table ~key:real_new_state_str ~data
        else begin
          Queue.enqueue discovered real_new_state_str;
          let data = (new_state, [flowPath (ToStr.Smv.form_act endF) r branch]) in
          Hashtbl.add_exn state_table ~key:real_new_state_str ~data
        end
      end;
      wrapper ends'
  in
  wrapper useful

let bfs startF endF rs ~types =
  let startF_str = ToStr.Smv.form_act startF in
  Hashtbl.add_exn state_table ~key:startF_str ~data:(startF, []);
  let endF_str = ToStr.Smv.form_act endF in
  Queue.enqueue discovered endF_str;
  Hashtbl.add_exn state_table ~key:endF_str ~data:(endF, []);
  while not (Queue.is_empty discovered) do
    let state = Queue.dequeue_exn discovered in
    Hash_set.add accessed state;
    let (state_form, _) = Hashtbl.find_exn state_table state in
    List.fold ~init:() rs ~f:(fun res r -> access_rule startF state_form r ~types; res)
  done;
  state_table
*)
