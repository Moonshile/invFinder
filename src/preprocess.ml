
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
    parallel (List.map pfs ~f:(fun p -> apply_statement s ~p))

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





(* process execution of exp *)
let rec exec_exp e ~pairs =
  match e with
  | Const(_)
  | Param(_) -> e
  | Var(v) ->
    begin
      match List.find pairs ~f:(fun (v', _) -> v' = v) with
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
          if v' = v then
            pre@((v, e')::ls')
          else
            update_list ls' (pre@[(v', e_of_v')])
      in
      wrapper pairs' (update_list res [])
  in
  wrapper assign_pairs []





module Act = struct

  let rec exp_act e ~types =
    match e with
    | Const(_)
    | Var(_)
    | Param(_) -> e
    | Ite(f, e1, e2) -> ite (form_act f ~types) (exp_act e1 ~types) (exp_act e2 ~types)
    | UIPFun(n, el) -> uipFun n (List.map el ~f:(exp_act ~types))
  and form_act form ~types =
    match form with
    | Chaos
    | Miracle -> form
    | Eqn(e1, e2) -> eqn (exp_act e1 ~types) (exp_act e2 ~types)
    | UIPPred(n, el) -> uipPred n (List.map el ~f:(exp_act ~types))
    | Neg(f) -> neg (form_act f ~types)
    | AndList(fl) -> andList (List.map fl ~f:(form_act ~types))
    | OrList(fl) -> orList (List.map fl ~f:(form_act ~types))
    | Imply(f1, f2) -> imply (form_act f1 ~types) (form_act f2 ~types)
    | ForallFormula(paramdefs, f) -> 
      let ps = cart_product_with_paramfix paramdefs types in
      let f' = form_act f ~types in
      andList (List.map ps ~f:(fun p -> apply_form ~p f'))
    | ExistFormula(paramdefs, f) -> 
      let ps = cart_product_with_paramfix paramdefs types in
      let f' = form_act f ~types in
      orList (List.map ps ~f:(fun p -> apply_form ~p f'))

  let statement_act s ~types =
    let s' = eliminate_for s ~types in
    let pairs = eliminate_ifelse_wrapper s' in
    let pairs' = exec_sequence pairs in
    parallel (List.map pairs' ~f:(fun (v, e) -> assign v (exp_act e ~types)))

  let rule_act (Rule(name, pds, form, s)) ~types =
    rule name pds (form_act form ~types) (statement_act s ~types)

  let property_act (Prop(name, pds, form)) ~types =
    prop name pds (form_act form ~types)

  let protocol_act {name; types; vardefs; init; rules; properties} =
    { 
      name = name;
      types = types;
      vardefs = vardefs;
      init = statement_act init ~types;
      rules = List.map rules ~f:(rule_act ~types);
      properties = List.map properties ~f:(property_act ~types)
    }

end



