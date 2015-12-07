
open Core.Std
open Utils
open Structure

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
  let no_forall_exist = List.map pairs ~f:(fun (v, e) -> (v, exp_act e ~types)) in
  let pairs' = exec_sequence no_forall_exist in
  parallel (List.map pairs' ~f:(fun (v, e) -> assign v e))

let rule_act (Rule(name, pds, form, s)) ~types =
  print_endline (sprintf "rule: %s" name);
  rule name pds (form_act form ~types) (statement_act s ~types)

let property_act (Prop(name, pds, form)) ~types =
  prop name pds (form_act form ~types)

let protocol_act {name; types; vardefs; init; rules; properties} =
  print_endline "========== Start to preprocess ==========";
  { 
    name = name;
    types = types;
    vardefs = vardefs;
    init = statement_act init ~types;
    rules = List.map rules ~f:(rule_act ~types);
    properties = List.map properties ~f:(property_act ~types)
  }




