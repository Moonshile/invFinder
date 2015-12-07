(** The most fundamental language for this tool

    @author Yongjian Li <lyj238@gmail.com>
    @author Kaiqiang Duan <duankq@ios.ac.cn>
*)

open Core.Std
open Utils

(*------------------------------ Types ---------------------------------*)

(** Constants *)
type const =
  | Intc of int
  | Strc of string
  | Boolc of bool
with sexp

let intc i = Intc i
let strc s = Strc s
let boolc b = Boolc b

(** Convert a int list to const list *)
let int_consts ints = List.map ints ~f:intc
(** Convert a string list to const list *)
let str_consts strs = List.map strs ~f:strc
(** Convert a boolean list to const list *)
let bool_consts bools = List.map bools ~f:boolc

(** Basic types available, including integers and enumerations.
    Types are defined by their names and range.
*)
type typedef =
  | Enum of string * const list
with sexp

let enum name letues = Enum(name, letues)

(** Parameter definitions
    + Paramdef, name and typename
*)
type paramdef =
  | Paramdef of string * string
with sexp

let paramdef name typename = Paramdef(name, typename)

(** Parameter references
    + Paramref, var name
    + Paramfix, var name, typename, value
*)
type paramref =
  | Paramref of string
  | Paramfix of string * string * const
with sexp

let paramref name = Paramref name
let paramfix vname tname value = Paramfix (vname, tname, value)

(** Variable definitions, each with its name and name of its type
    + Array var: name, param definitions, type name
*)
type vardef =
  | Arrdef of (string * paramdef list) list * string
with sexp

let arrdef ls typename = Arrdef(ls, typename)

(** Record definition *)
let record_def name paramdefs vardefs =
  List.map vardefs ~f:(fun vardef ->
    let Arrdef(ls, t) = vardef in
    arrdef ((name, paramdefs)::ls) t
  )

(** Variable reference *)
type var =
  | Arr of (string * paramref list) list
with sexp

let arr ls = Arr(ls)

(** Global variable *)
let global name = arr [(name, [])]

(** Record *)
let record vars =
  arr (List.concat (List.map vars ~f:(fun (Arr(ls)) -> ls)))

(** Represents expressions, including
    + Constants
    + Variable references
    + Parameter
    + Ite exp
    + UIPFun: Uninterpreted function, such as + - * /
*)
type exp =
  | Const of const
  | Var of var
  | Param of paramref
  | Ite of formula * exp * exp
  | UIPFun of string * exp list
(** Boolean expressions, including
    + Boolean constants, Chaos as True, Miracle as false
    + Equation expression
    + Other basic logical operations, including negation,
      conjuction, disjuction, and implication
    + Uninterpreted predications, such as > >= < <=
*)
and formula =
  | Chaos
  | Miracle
  | Eqn of exp * exp
  | UIPPred of string * exp list
  | Neg of formula
  | AndList of formula list
  | OrList of formula list
  | Imply of formula * formula
  | ForallFormula of paramdef list * formula
  | ExistFormula of paramdef list * formula
with sexp

let const c = Const c
let var v = Var v
let param paramref = Param(paramref)
let ite f e1 e2 = Ite(f, e1, e2)
let uipFun name args = UIPFun(name, args)

let chaos = Chaos
let miracle = Miracle
let eqn e1 e2 = Eqn(e1, e2)
let uipPred name args = UIPPred(name, args)
let neg f = Neg f
let andList fs = AndList fs
let orList fs = OrList fs
let imply f1 f2 = Imply(f1, f2)
let forallFormula paramdefs form = ForallFormula(paramdefs, form)
let existFormula paramdefs form = ExistFormula(paramdefs, form)

(** Assignment statements, including
    + Single assignment
    + Parallel assignment
*)
type statement =
  | Assign of var * exp
  | Parallel of statement list
  | IfStatement of formula * statement
  | IfelseStatement of formula * statement * statement
  | ForStatement of statement * paramdef list
with sexp

let assign v e = Assign(v, e)
let parallel statements = Parallel statements
let ifStatement form statement = IfStatement(form, statement)
let ifelseStatement form s1 s2 = IfelseStatement(form, s1, s2)
let forStatement s paramdefs = ForStatement(s, paramdefs)

(** Represents rules which consists of guard and assignments
    + Rule: name, parameters, guard, assignments
*)
type rule = 
  | Rule of string * paramdef list * formula * statement
with sexp

let rule name paramdef f s = Rule(name, paramdef, f, s)

(** Represents properties
    + Prop: name, parameters, formula
*)
type prop =
  | Prop of string * paramdef list * formula
with sexp

let prop name paramdef f = Prop(name, paramdef, f)

(** Represents the whole protocol *)
type protocol = {
  name: string;
  types: typedef list;
  vardefs: vardef list;
  init: statement;
  rules: rule list;
  properties: prop list;
}
with sexp

(** The actual parameters can't match with their definitions *)
exception Unmatched_parameters

(** Unexhausted instantiation
    This exception should never be raised. Once raised, There should be a bug in this tool.
*)
exception Unexhausted_inst









(** Find the letues range of a type by its name
*)
let name2type ~tname ~types =
  let op_t = List.find types ~f:(fun (Enum(n, _)) -> n = tname) in
  match op_t with
  | None -> raise (Cannot_find (sprintf "type %s" tname))
  | Some (Enum(_, consts)) -> consts

(* Generate Cartesian production of all possible values of a `paramdef` set
    Result is like [[Boolc true; Intc 1]; [Boolc false; Intc 1]]
*)
let cart_product paramdefs types =
  paramdefs
  |> List.map ~f:(fun (Paramdef(_, tname)) -> name2type ~tname ~types)
  |> cartesian_product

(* Generate Cartesian production of all possible values of a `paramdef` set
    Each value in each set with its index name
    Result is like [[("x", Boolc true); ("n", Intc 1)]; [("x", Boolc false); ("n", Intc 1)]]
*)
let cart_product_with_name paramdefs types =
  paramdefs
  |> List.map ~f:(fun (Paramdef(n, tname)) -> (n, name2type ~tname ~types))
  |> List.map ~f:(fun (n, t) -> List.map t ~f:(fun x -> (n, x)))
  |> cartesian_product

(* Generate Cartesian production of all possible values of a `paramdef` set
    Each value in each set is index name with its associated paramfix
    Result is like [
      [Paramfix("x", "bool", Boolc true); Paramfix("n", "int", Intc 1)]; 
      [Paramfix("x", "bool", Boolc false); Paramfix("n", "int", Intc 1)]
    ]
*)
let cart_product_with_paramfix paramdefs types =
  paramdefs
  |> List.map ~f:(fun (Paramdef(n, tname)) -> (n, (tname, name2type ~tname ~types)))
  |> List.map ~f:(fun (n, (tname, trange)) -> List.map trange ~f:(fun x -> paramfix n tname x))
  |> cartesian_product

(** Get the name of parameter
    e.g., For parameter Paramfix("x", "bool", Boolc true)), generate "x"
    For parameter Paramref("n"), generate "n"
*)
let name_of_param pr =
  match pr with
  | Paramref(n)
  | Paramfix(n, _, _) -> n

let set_param_name pr name =
  match pr with
  | Paramref(_) -> paramref name
  | Paramfix(_, tn, c) -> paramfix name tn c

let typename_of_paramfix pf =
  match pf with
  | Paramref(_) -> raise Unexhausted_inst
  | Paramfix(_, tn, _) -> tn

let find_paramfix pfs name =
  List.find pfs ~f:(fun pr -> name = (name_of_param pr))

let find_paramdef pds name =
  List.find pds ~f:(fun (Paramdef(n, _)) -> name = n)











(* attach const i to string name *)
let attach name i =
  match i with
  | Strc(x) -> sprintf "%s[%s]" name x
  | Intc(x) -> sprintf "%s[%d]" name x
  | Boolc(x) -> sprintf "%s[%b]" name x

(** attach consts i to string name *)
let attach_list name i_list =
  List.fold i_list ~init:name ~f:attach

(** Apply a paramref with param, i.e., cast it to consts *)
let apply_paramref pr ~p =
  match pr with
  | Paramref(s) -> (
      match find_paramfix p s with
      | None -> pr (* raise (Cannot_find (sprintf "parameter reference for %s" s)) *)
      | Some pf -> pf
    )
  | Paramfix(_) -> pr

(** Apply array with param *)
let apply_array (Arr(ls)) ~p =
  arr (List.map ls ~f:(fun (name, params) ->
    name, List.map params ~f:(apply_paramref ~p)
  ))

(** Apply exp with param *)
let rec apply_exp exp ~p =
  match exp with
  | Var(x) -> var (apply_array x ~p)
  | Param(pr) -> param (apply_paramref pr ~p)
  | Const(_) -> exp
  | Ite(f, e1, e2) -> ite (apply_form f ~p) (apply_exp e1 ~p) (apply_exp e2 ~p)
  | UIPFun(name, el) -> uipFun name (List.map el ~f:(apply_exp ~p))
(** Apply formula with param *)
and apply_form f ~p =
  match f with
  | Chaos
  | Miracle -> f
  | Eqn(e1, e2) -> eqn (apply_exp e1 ~p) (apply_exp e2 ~p)
  | UIPPred(name, el) -> uipPred name (List.map el ~f:(apply_exp ~p))
  | Neg(form) -> neg (apply_form form ~p)
  | AndList(fl) -> andList (List.map fl ~f:(apply_form ~p))
  | OrList(fl) -> orList (List.map fl ~f:(apply_form ~p))
  | Imply(f1, f2) -> imply (apply_form f1 ~p) (apply_form f2 ~p)
  | ForallFormula(pds, f) -> forallFormula pds (apply_form f ~p)
  | ExistFormula(pds, f) -> existFormula pds (apply_form f ~p)

(** Apply statement with param *)
let rec apply_statement statement ~p =
  match statement with
  | Assign(v, e) -> assign (apply_array v ~p) (apply_exp e ~p)
  | Parallel(sl) -> parallel (List.map sl ~f:(apply_statement ~p))
  | IfStatement(f, s) -> ifStatement (apply_form f ~p) (apply_statement s ~p)
  | IfelseStatement(f, s1, s2) ->
    ifelseStatement (apply_form f ~p) (apply_statement s1 ~p) (apply_statement s2 ~p)
  | ForStatement(_) -> raise Empty_exception

(* Check if a given parameter matches with the paramdef *)
let name_match params defs =
  if List.length params = List.length defs then
    let same_name pr (Paramdef(n2, _)) = (name_of_param pr) = n2 in
    List.map2_exn params defs ~f:same_name
    |> List.fold ~init:true ~f:(fun res x -> res && x)
  else
    false

(** Apply rule with param *)
let apply_rule r ~p =
  let Rule(n, paramdefs, f, s) = r in
  print_endline n;
  let name =
    if p = [] then n
    else begin
      let const_act c =
        match c with
        | Intc(i) -> Int.to_string i
        | Strc(s) -> String.lowercase s
        | Boolc(b) -> String.uppercase (Bool.to_string b)
      in
      let paramref_act pr =
        match pr with
        | Paramfix(_, _, c) -> sprintf "[%s]" (const_act c)
        | Paramref(_) -> raise Unexhausted_inst
      in
      sprintf "%s%s" n (String.concat (List.map p ~f:paramref_act))
    end
  in
  if name_match p paramdefs then
    let f' = apply_form f ~p in
    let s' = apply_statement s ~p in
    rule name [] f' s'
  else
    raise Unmatched_parameters

(** Apply property with param *)
let apply_prop property ~p =
  let Prop(name, paramdefs, f) = property in
  print_endline name;
  if name_match p paramdefs then
    prop name [] (apply_form f ~p)
  else
    raise Unmatched_parameters

let rule_to_insts r ~types =
  let Rule(_, pds, _, _) = r in
  let ps = cart_product_with_paramfix pds types in
  if pds = [] then
    [r]
  else
    List.map ps ~f:(fun p -> apply_rule r ~p)

let prop_to_insts property ~types =
  let Prop(_, pds, _) = property in
  let ps = cart_product_with_paramfix pds types in
  if pds = [] then
    [property]
  else
    List.map ps ~f:(fun p -> apply_prop property ~p)







(*********************************** Module Variable Names, with Param values *****************)

(** Get variable names in the components *)
module VarNamesWithParam = struct
  
  open String.Set

  (** Names of exp *)
  let rec of_exp ~of_var e =
    match e with
    | Const(_)
    | Param(_) -> of_list []
    | Var(v) -> of_var v
    | Ite(f, e1, e2) -> union_list [of_form ~of_var f; of_exp ~of_var e1; of_exp ~of_var e2]
    | UIPFun(_, el) -> union_list (List.map el ~f:(of_exp ~of_var))
  (** Names of formula *)
  and of_form ~of_var f =
    match f with
    | Chaos
    | Miracle -> of_list []
    | Eqn(e1, e2) -> union_list [of_exp ~of_var e1; of_exp ~of_var e2]
    | UIPPred(_, el) -> union_list (List.map el ~f:(of_exp ~of_var))
    | Neg(form) -> of_form ~of_var form
    | AndList(fl)
    | OrList(fl) -> union_list (List.map fl ~f:(of_form ~of_var))
    | Imply(f1, f2) -> union_list [of_form ~of_var f1; of_form ~of_var f2]
    | ForallFormula(_)
    | ExistFormula(_) -> raise Empty_exception


  let rec of_statement ~of_var s =
    match s with
    | Assign(v, e) -> union_list [of_var v; of_exp ~of_var e]
    | Parallel(slist) -> union_list (List.map slist ~f:(of_statement ~of_var))
    | ForStatement(_)
    | IfStatement(_)
    | IfelseStatement(_) -> raise Empty_exception

  let of_rule ~of_var r = 
    match r with
    | Rule(_, _, f, s) -> union_list [of_form ~of_var f; of_statement ~of_var s]
end









module Equal = struct

  let in_paramref pr1 pr2 =
    match (pr1, pr2) with
    | (Paramref(n1), Paramref(n2)) -> n1 = n2
    | (Paramfix(_, t1, c1), Paramfix(_, t2, c2)) -> t1 = t2 && c1 = c2
    | _ -> false

  let in_var v1 v2 =
    let Arr(ls1) = v1 in
    let Arr(ls2) = v2 in
    match List.zip ls1 ls2 with
    | None -> false
    | Some(ls_pairs) ->
      List.fold ls_pairs ~init:true ~f:(fun res ((n1, ps1), (n2, ps2)) ->
        match List.zip ps1 ps2 with
        | None -> false
        | Some(p_pairs) ->
          let pairs_res =
            List.fold p_pairs ~init:true ~f:(fun res (p1, p2) -> res && in_paramref p1 p2)
          in
          res && n1 = n2 && pairs_res
      )
  
end










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






(************************************ Candies **********************************)

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

(* perform return operation in function definitions *)
let return v s ~types =
  let s' = eliminate_for s ~types in
  let pairs = eliminate_ifelse_wrapper s' in
  let pairs' = exec_sequence pairs in
  let (_, res) = List.find_exn pairs' ~f:(fun (v', _) -> Equal.in_var v v') in
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








