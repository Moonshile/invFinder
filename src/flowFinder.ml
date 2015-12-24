
open Core.Std
open Utils
open Paramecium
open Formula
open InvFinder




type flowpath =
  | FlowPath of string * rule * formula

let flowPath form r branch = FlowPath(form, r, branch)


(*  key: string of the formula
    value: tuple of
      formula,
      flowpath of states called enders which are endstate of this state
    -- means that the initial state has only enders, and terminate state has nothing
*)
let state_table = Hashtbl.create ~hashable:String.hashable ()

let accessed = Hash_set.create ~hashable:String.hashable ()

let discovered = Queue.create ()

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
      if is_tautology (imply (andList [g; branch]) startF) then
        let startF_str = ToStr.Smv.form_act startF in
        let (f, enders) = Hashtbl.find_exn state_table startF_str in
        let data = (f, enders@[flowPath (ToStr.Smv.form_act endF) r branch]) in
        print_endline ("bingo!!! rule: "^rn^"; end - "^endF_str);
        Hashtbl.replace state_table ~key:startF_str ~data
      else begin
        let new_state = normalize (simplify (andList [g; branch; end_form])) ~types in
        let new_state_str = ToStr.Smv.form_act new_state in
        print_endline ("path!!! rule: "^rn^"; new - "^new_state_str^"; end - "^endF_str);
        let exists_in_accessed = Hash_set.exists accessed ~f:(fun s -> s = new_state_str) in
        let exists_in_discovered = Queue.exists discovered ~f:(fun s -> s = new_state_str) in
        if exists_in_accessed && not (new_state = startF) then Prt.warning "Circle detected!!!" else begin () end;
        if exists_in_accessed || exists_in_discovered then
          let (f, enders) = Hashtbl.find_exn state_table new_state_str in
          let data = (f, enders@[flowPath (ToStr.Smv.form_act endF) r branch]) in
          Hashtbl.replace state_table ~key:new_state_str ~data
        else begin
          Queue.enqueue discovered new_state_str;
          let data = (new_state, [flowPath (ToStr.Smv.form_act endF) r branch]) in
          Hashtbl.add_exn state_table ~key:new_state_str ~data
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
    let (state_form, _) = Hashtbl.find_exn state_table state in
    List.fold ~init:() rs ~f:(fun res r -> access_rule startF state_form r ~types; res)
  done;
  state_table

