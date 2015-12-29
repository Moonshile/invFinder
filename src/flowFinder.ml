
open Core.Std
open Utils
open Paramecium
open Formula
open InvFinder




type flowpath =
  | FlowPath of string * string * formula

let flowPath form rname branch = FlowPath(form, rname, branch)


(*  key: parameterized form component
    value: formula states that contain this component represented by the key
*)
let ctable = Hashtbl.create ~hashable:String.hashable ()

(*  key: string of the formula state
    value: tuple of
      formula,
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


let add_path_to_component end_state component rname branch =
  match component_is_parameterized component with
  | false -> ()
  | true ->
    let start_state_strs = Hashtbl.find_exn ctable (ToStr.Smv.form_act component) in
    let end_state_str = ToStr.Smv.form_act end_state in
    let path = flowPath end_state_str rname branch in
    List.fold start_state_strs ~init:() ~f:(fun res x ->
      let (f, enders) = Hashtbl.find_exn state_table x in
      Hashtbl.replace state_table ~key:x ~data:(f, enders@[path]);
      res
    )


let add_path_to_components end_state components rname branch =
  List.fold components ~init:() ~f:(fun res x ->
    add_path_to_component end_state x rname branch; res
  )


let add_components_in_form form =
  let ands = flat_and_to_list form in
  let form_str = ToStr.Smv.form_act form in
  List.fold ands ~init:() ~f:(fun res x ->
    if component_is_parameterized x then
      let key = ToStr.Smv.form_act x in
      Hashtbl.replace ctable ~key ~data:[form_str]; res
    else begin
      res
    end
  )



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
        let (f, enders) = Hashtbl.find_exn state_table startF_str in
        let data = (f, enders@[flowPath endF_str rn branch]) in
        print_endline ("bingo!!! rule: "^rn^"; end - "^endF_str);
        Hashtbl.replace state_table ~key:startF_str ~data
      else begin
        let new_state = simplify (andList [g; branch; end_form]) in
        let new_state_str = ToStr.Smv.form_act new_state in
        let new_state_components = flat_and_to_list new_state in
        let discovered_components = List.filter new_state_components ~f:(fun nsc ->
          let nsc_str = ToStr.Smv.form_act nsc in
          List.exists (Hashtbl.keys ctable) ~f:(fun c -> nsc_str = c)
        ) in
        print_endline ("path!!! rule: "^rn^"; new - "^new_state_str^"; end - "^endF_str);
        if List.is_empty discovered_components then
          (add_components_in_form new_state;
          Queue.enqueue discovered new_state_str;
          let data = (new_state, [flowPath endF_str rn branch]) in
          Hashtbl.replace state_table ~key:new_state_str ~data)
        else begin
          add_path_to_components endF discovered_components rn branch
        end
      end;
      wrapper ends'
  in
  wrapper useful


let bfs startF endF rs =
  let startF_str = ToStr.Smv.form_act startF in
  Hashtbl.add_exn state_table ~key:startF_str ~data:(startF, []);
  let endF_str = ToStr.Smv.form_act endF in
  Queue.enqueue discovered endF_str;
  Hashtbl.add_exn state_table ~key:endF_str ~data:(endF, []);
  add_components_in_form startF;
  add_components_in_form endF;
  while not (Queue.is_empty discovered) do
    let state = Queue.dequeue_exn discovered in
    let (state_form, _) = Hashtbl.find_exn state_table state in
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
