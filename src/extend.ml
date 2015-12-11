
open Core.Std
open Utils
open Structure

(* unwind all for statements *)
let rec eliminate_for statement ~types =
  match statement with
  | Assign(_) -> statement
  | Parallel(sl) -> parallel (List.map sl ~f:(eliminate_for ~types))
  | IfStatement(f, s) -> ifStatement f (eliminate_for s ~types)
  | IfelseStatement(f, s1, s2) ->
    ifelseStatement f (eliminate_for s1 ~types) (eliminate_for s2 ~types)
  | ForStatement(s, pd) ->
    let pfs = cart_product_with_paramfix pd types in
    let s' = eliminate_for s ~types in
    parallel (List.map pfs ~f:(fun p -> apply_statement s' ~p))

let rec eliminate_quant_in_exp e ~types =
  match e with
  | Const(_)
  | Var(_)
  | Param(_) -> e
  | Ite(f, e1, e2) -> 
    ite (eliminate_quant_in_form f ~types) (eliminate_quant_in_exp e1 ~types) (eliminate_quant_in_exp e2 ~types)
  | UIPFun(n, el) -> uipFun n (List.map el ~f:(eliminate_quant_in_exp ~types))
and eliminate_quant_in_form form ~types =
  match form with
  | Chaos
  | Miracle -> form
  | Eqn(e1, e2) ->
    eqn (eliminate_quant_in_exp e1 ~types) (eliminate_quant_in_exp e2 ~types)
  | UIPPred(n, el) ->
    uipPred n (List.map el ~f:(eliminate_quant_in_exp ~types))
  | Neg(f) -> neg (eliminate_quant_in_form f ~types)
  | AndList(fl) -> andList (List.map fl ~f:(eliminate_quant_in_form ~types))
  | OrList(fl) -> orList (List.map fl ~f:(eliminate_quant_in_form ~types))
  | Imply(f1, f2) -> imply (eliminate_quant_in_form f1 ~types) (eliminate_quant_in_form f2 ~types)
  | ForallFormula(paramdefs, f) -> 
    let ps = cart_product_with_paramfix paramdefs types in
    let f' = eliminate_quant_in_form f ~types in
    andList (List.map ps ~f:(fun p -> apply_form ~p f'))
  | ExistFormula(paramdefs, f) -> 
    let ps = cart_product_with_paramfix paramdefs types in
    let f' = eliminate_quant_in_form f ~types in
    orList (List.map ps ~f:(fun p -> apply_form ~p f'))

let rec eliminate_quant statement ~types =
  match statement with
  | Assign(v, e) -> assign v (eliminate_quant_in_exp e ~types)
  | Parallel(sl) -> parallel (List.map sl ~f:(eliminate_quant ~types))
  | IfStatement(f, s) -> ifStatement (eliminate_quant_in_form f ~types) (eliminate_quant s ~types)
  | IfelseStatement(f, s1, s2) ->
    ifelseStatement (eliminate_quant_in_form f ~types) (eliminate_quant s1 ~types) (eliminate_quant s2 ~types)
  | ForStatement(s, pds) -> forStatement (eliminate_quant s ~types) pds


(* eliminate if statements, must eliminate all for statements before *)
let rec eliminate_ifelse_wrapper statement =
  match statement with
  | Assign(v, e) -> [(v, e)]
  | Parallel(sl) -> List.concat (List.map sl ~f:eliminate_ifelse_wrapper)
  | IfStatement(f, s) ->
    let pairs = eliminate_ifelse_wrapper s in
    List.map pairs ~f:(fun (v, e) -> (v, ite f e (var v)))
  | IfelseStatement(f, s1, s2) ->
    let pairs1 = eliminate_ifelse_wrapper s1 in
    let pairs2 = eliminate_ifelse_wrapper s2 in
    let res_part1 = List.map pairs1 ~f:(fun (v1, e1) ->
      match List.find pairs2 ~f:(fun (v2, _) -> v1 = v2) with
      | Some((v, e2)) -> (v, ite f e1 e2)
      | None -> (v1, ite f e1 (var v1))
    ) in
    let res_part2 = List.filter_map pairs2 ~f:(fun (v2, e2) ->
      match List.find pairs1 ~f:(fun (v1, _) -> v1 = v2) with
      | Some(_) -> None
      | None -> Some((v2, ite f (var v2) e2))
    ) in
    res_part1@res_part2
  | ForStatement(_) -> raise Empty_exception

let eliminate_ifelse statement =
  let statement' = eliminate_ifelse_wrapper statement in
  parallel (List.map statement' ~f:(fun (v, e) -> assign v e))










let rec exp_symbolic_simp ~f e =
  match e with
  | Const(_)
  | Param(_)
  | Var(_) -> e
  | Ite(g, e1, e2) ->
    let g' = form_symbolic_simp ~f g in
    if Formula.is_tautology (imply f g') then
      exp_symbolic_simp ~f e1
    else if Formula.is_tautology (imply f (neg g')) then
      exp_symbolic_simp ~f e2
    else
      let e1' = exp_symbolic_simp ~f:(andList [f; g']) e1 in
      let e2' = exp_symbolic_simp ~f:(andList [f; neg g']) e2 in
      ite g' e1' e2'
  | UIPFun(n, el) -> uipFun n (List.map el ~f:(exp_symbolic_simp ~f))
and form_symbolic_simp ~f form =
  match form with
  | Chaos
  | Miracle -> form
  | Eqn(e1, e2) -> eqn (exp_symbolic_simp ~f e1) (exp_symbolic_simp ~f e2)
  | UIPPred(n, el) -> uipPred n (List.map el ~f:(exp_symbolic_simp ~f))
  | Neg(g) -> neg (form_symbolic_simp ~f g)
  | AndList(gl) -> andList (List.map gl ~f:(form_symbolic_simp ~f))
  | OrList(gl) -> orList (List.map gl ~f:(form_symbolic_simp ~f))
  | Imply(g1, g2) -> imply (form_symbolic_simp ~f g1) (form_symbolic_simp ~f g2)
  | ForallFormula(_)
  | ExistFormula(_) -> raise Empty_exception










(* process execution of exp *)
let rec exec_exp e ~pairs =
  match e with
  | Const(_)
  | Param(_) -> e
  | Var(v) ->
    begin
      match List.find pairs ~f:(fun (v', _) -> Equal.in_var v v') with
      | Some((_, e')) -> e'
      | None -> e
    end
  | Ite(f, e1, e2) -> ite (exec_formula f ~pairs) (exec_exp e1 ~pairs) (exec_exp e2 ~pairs)
  | UIPFun(n, el) -> uipFun n (List.map el ~f:(exec_exp ~pairs))
and exec_formula form ~pairs =
  match form with
  | Chaos
  | Miracle -> form
  | Eqn(e1, e2) -> eqn (exec_exp e1 ~pairs) (exec_exp e2 ~pairs)
  | UIPPred(n, el) -> uipPred n (List.map el ~f:(exec_exp ~pairs))
  | Neg(f) -> neg (exec_formula f ~pairs)
  | AndList(fl) -> andList (List.map fl ~f:(exec_formula ~pairs))
  | OrList(fl) -> orList (List.map fl ~f:(exec_formula ~pairs))
  | Imply(f1, f2) -> imply (exec_formula f1 ~pairs) (exec_formula f2 ~pairs)
  | ForallFormula(pds, f) -> forallFormula pds (exec_formula f ~pairs)
  | ExistFormula(pds, f) -> existFormula pds (exec_formula f ~pairs)

(* process sequence execution of statements, must eliminate all for/if statements before *)
(* WARNING: deprecated *)
let exec_sequence assign_pairs =
  let rec wrapper pairs res =
    match pairs with
    | [] -> res
    | (v, e)::pairs' ->
      let e' = exec_exp e ~pairs:res in
      let rec update_list ls pre =
        match ls with
        | [] -> pre@[(v, e')]
        | (v', e_of_v')::ls' ->
          if Equal.in_var v v' then
            pre@((v, e')::ls')
          else
            update_list ls' (pre@[(v', e_of_v')])
      in
      wrapper pairs' (update_list res [])
  in
  wrapper assign_pairs []

(*  process execution of statements and eliminate ifelse,
    must eliminate all for statements before
*)
let rec flatten_exec ?(env=chaos) statement =
  match statement with
  | Assign(v, e) ->
    [(v, e)]
  | Parallel(sl) ->
    let res = List.fold sl ~init:[] ~f:(fun res s ->
      (*print_endline (String.concat ~sep:", " (List.map res ~f:(fun (v, _) ->
        ToSMV.var_act v
      )));*)
      let new_env = andList (env::(List.map res ~f:(fun (v, e) -> eqn (var v) e))) in
      let x = flatten_exec ~env:new_env s in
      let x' = List.map x ~f:(fun (vx, ex) -> 
        (vx, exec_exp ex ~pairs:res)
      ) in
      let missed = List.filter res ~f:(fun (v, _) ->
        List.for_all x' ~f:(fun (v', _) -> not (Equal.in_var v v'))
      ) in
      missed@x'
    ) in
    res
  | IfStatement(f, s) ->
    print_endline (if Formula.is_tautology (imply env f) then (ToSMV.form_act (imply env f)) else "...");
    if Formula.is_tautology (imply env f) then
      flatten_exec ~env s
    else if Formula.is_tautology (imply env (neg f)) then
      []
    else
      let pairs = flatten_exec ~env:(andList [env; f]) s in
      let res = List.map pairs ~f:(fun (v, e) -> 
        (v, if Equal.in_exp e (var v) then e else ite f e (var v))
      ) in
      res
  | IfelseStatement(f, s1, s2) ->
    if Formula.is_tautology (imply env f) then
      flatten_exec ~env s1
    else if Formula.is_tautology (imply env (neg f)) then
      flatten_exec ~env s2
    else
      let pairs1 = flatten_exec ~env:(andList [env; f]) s1 in
      let pairs2 = flatten_exec ~env:(andList [env; neg f]) s2 in
      let part1 = List.map pairs1 ~f:(fun (v, e) ->
        match List.find pairs2 ~f:(fun (v', _) -> Equal.in_var v v') with
        | Some(_, e') ->
          (v, if Equal.in_exp e e' then e else ite f e e')
        | None ->
          (v, if Equal.in_exp e (var v) then e else ite f e (var v))
      ) in
      let part2 =
        List.filter pairs2 ~f:(fun (v', _) ->
          List.for_all pairs1 ~f:(fun (v, _) -> not (Equal.in_var v v'))
        )
        |> List.map ~f:(fun (v', e') -> 
          (v', if Equal.in_exp (var v') e' then e' else ite f (var v') e')
        )
      in
      part1@part2
  | ForStatement(_) -> raise Empty_exception
















(* perform return operation in function definitions *)
let return v s ~types =
  let no_for = eliminate_for s ~types in
  let no_quant = eliminate_quant no_for ~types in
  let pairs = flatten_exec no_quant in
  let (_, res) = List.find_exn pairs ~f:(fun (v', _) -> Equal.in_var v v') in
  res

(* perform read operation of a var whose params have been changed *)
let read_param v params_exp ~pds ~types =
  let useful_pds = List.map params_exp ~f:(fun pe ->
    match pe with
    | Arr([(n, [])]) -> List.find_exn pds ~f:(fun (Paramdef(n', _)) -> n = n')
    | _ -> raise Empty_exception
  ) in
  let ps = cart_product_with_paramfix useful_pds types in
  let rec perform_read ps =
    match ps with
    | [] -> var v
    | [p] -> var (apply_array v ~p)
    | p::ps' ->
      let form = andList (List.map2_exn p params_exp ~f:(fun pf pe ->
        eqn (param pf) (var pe)
      )) in
      ite form (var (apply_array v ~p)) (perform_read ps')
  in
  perform_read ps

(* perform write operation to a var whose params have been changed *)
let write_param v params_exp e ~pds =
  let useful_pds = List.map params_exp ~f:(fun pe ->
    match pe with
    | Arr([(n, [])]) -> List.find_exn pds ~f:(fun (Paramdef(n', _)) -> n = n')
    | _ -> raise Empty_exception
  ) in
  let useful_prs = List.map useful_pds ~f:(fun (Paramdef(n, _)) -> paramref n) in
  forStatement (
    ifStatement (
      andList (List.map2_exn useful_prs params_exp ~f:(fun pr pe ->
        match pe with
        | Arr([(_, [])]) -> eqn (param pr) (var pe)
        | _ -> raise Empty_exception
      ))
    ) (
      assign v e
    )
  ) useful_pds


