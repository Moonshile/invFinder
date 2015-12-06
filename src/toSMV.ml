
open Core.Std
open Utils
open Structure

let strc_to_lower = ref true
let varnames_ref = ref []

(* Translate a const to smv const *)
let const_act c =
  match c with
  | Intc(i) -> Int.to_string i
  | Strc(s) -> if (!strc_to_lower) then String.lowercase s else begin s end
  | Boolc(b) -> String.uppercase (Bool.to_string b)

let type_act ~types name =
  let Enum(_, consts) = List.find_exn types ~f:(fun (Enum(n, _)) -> n = name) in
  let range =
    List.map consts ~f:const_act
    |> String.concat ~sep:", "
  in
  if range = "TRUE, FALSE" || range = "FALSE, TRUE" then "boolean"
  else begin sprintf "{%s}" range end

(** Translate a paramref to smv string *)
let paramref_act pr =
  match pr with
  | Paramfix(_, _, c) -> sprintf "[%s]" (const_act c)
  | Paramref(name) -> Prt.error ("Unexhausted_inst param: "^name);raise Unexhausted_inst

let vardef_act ~types vd =
  let Arrdef(ls, t) = vd in
  let type_str = type_act ~types t in
  let parts = List.map ls ~f:(fun (n, pds) ->
    match pds with
    | [] -> [n]
    | _ ->
      let ps = cart_product_with_paramfix pds types in
      let const_strs = List.map ps ~f:(fun group -> 
        List.map group ~f:(fun pr -> paramref_act pr)
        |> String.concat
      ) in
      List.map const_strs ~f:(fun cstr -> sprintf "%s%s" n cstr)
  ) in
  let full_parts = cartesian_product parts in
  let full_names = List.map full_parts ~f:(fun parts -> String.concat ~sep:"." parts) in
  varnames_ref := full_names; print_endline (String.concat ~sep:", " full_names);
  String.concat ~sep:"\n" (List.map full_names ~f:(fun n -> sprintf "%s : %s;" n type_str))

(* Translate a variable to smv variable *)
let var_act v =
  let Arr(ls) = v in
  String.concat ~sep:"." (List.map ls ~f:(fun (n, prs) ->
    match prs with
    | [] -> n
    | _ -> sprintf "%s%s" n (String.concat (List.map prs ~f:paramref_act))
  ))

(* Translate an exp to smv exp *)
let rec exp_act exp =
  match exp with
  | Const(c) -> const_act c
  | Var(v) -> var_act v
  | Param(pr) -> (
      match pr with
      | Paramfix(_, _, c) -> sprintf "%s" (const_act c)
      | Paramref(_) -> raise Unexhausted_inst
    )
  | Ite(f, e1, e2) ->
    sprintf "case\n%s : %s; TRUE : %s;\nesac" (form_act f) (exp_act e1) (exp_act e2)
  | UIPFun(n, el) ->
    List.reduce_exn (List.map el ~f:exp_act) ~f:(fun res x -> sprintf "%s %s %s" res n x)
    |> sprintf "(%s)"
(** Translate formula to smv string

    @param form the formula to be translated
    @return the smv string
*)
and form_act form =
  match form with
  | Chaos -> "TRUE"
  | Miracle -> "FALSE"
  | Eqn(e1, e2) -> sprintf "(%s = %s)" (exp_act e1) (exp_act e2)
  | UIPPred(n, el) ->
    List.reduce_exn (List.map el ~f:exp_act) ~f:(fun res x -> sprintf "%s %s %s" res n x)
    |> sprintf "(%s)"
  | Neg(form) -> sprintf "(!%s)" (form_act form)
  | AndList(fl) ->
    List.map fl ~f:(form_act)
    |> reduce ~default:"TRUE" ~f:(fun res x -> sprintf "%s & %s" res x)
    |> sprintf "(%s)"
  | OrList(fl) ->
    List.map fl ~f:(form_act)
    |> reduce ~default:"FALSE" ~f:(fun res x -> sprintf "%s | %s" res x)
    |> sprintf "(%s)"
  | Imply(f1, f2) -> sprintf "(%s -> %s)" (form_act f1) (form_act f2)
  | ForallFormula(_)
  | ExistFormula(_) -> raise Empty_exception

let rec statement_act ?(is_init=false) s guard_str =
  match s with
  | Assign(v, e) ->
    let var_str = var_act v in
    if List.exists (!varnames_ref) ~f:(fun n -> n = var_str) then
      let exp_str = exp_act e in
      if is_init then
        sprintf "init(%s) := case\nTRUE : %s;\nesac;" var_str exp_str
      else begin
        sprintf "next(%s) := case\n%s : %s;\nTRUE : %s;\nesac;" var_str guard_str exp_str var_str
      end
    else begin
      print_endline (sprintf "ignore local var: %s" var_str); ""
    end
  | Parallel(ss) ->
    if ss = [] then "" else begin
      List.map ss ~f:(fun s' -> statement_act ~is_init s' guard_str)
      |> String.concat ~sep:"\n"
    end
  | IfStatement(_)
  | IfelseStatement(_)
  | ForStatement(_) -> raise Empty_exception

let init_act s = statement_act ~is_init:true s "TRUE"

let rule_act r =
  let escape n =
    String.substr_replace_all n ~pattern:"[" ~with_:"__"
    |> String.substr_replace_all ~pattern:"]" ~with_:""
    |> String.substr_replace_all ~pattern:"." ~with_:"__"
  in
  let vars = String.Set.to_list (VarNamesWithParam.of_rule r ~of_var:(fun v ->
    String.Set.of_list [var_act v]
  )) in
  let vars_str = String.concat vars ~sep:", " in
  (* rule process instance *)
  let Rule(n, _, f, s) = r in
  let name = escape n in
  let rule_proc_inst = sprintf "%s : process Proc__%s(%s);" name name vars_str in
  (* rule process *)
  let guard_str = form_act f in
  let statement_str = escape (statement_act s guard_str) in
  let rule_proc = 
    sprintf "MODULE Proc__%s(%s)\nASSIGN\n%s" name (escape vars_str) statement_str
  in
  (* result *)
  (rule_proc_inst, rule_proc)

let prop_act property =
  let Prop(_, _, f) = property in
  sprintf "SPEC\n  AG (%s)" (form_act f)

let protocol_act {name=_; types; vardefs; init; rules; properties} =
  let vardef_str = 
    sprintf "VAR\n%s" (String.concat ~sep:"\n" (List.map vardefs ~f:(vardef_act ~types)))
  in
  let rule_insts =
    List.concat (List.map rules ~f:(rule_to_insts ~types))
    |> List.map ~f:(fun (Rule(n, pds, f, s)) ->
      let s' =
        exec_sequence (eliminate_ifelse_wrapper s)
        |> List.map ~f:(fun (v, e) -> assign v e)
      in
      rule n pds f (parallel s')
    )
  in
  let rule_proc_insts, rule_procs = List.unzip (List.map rule_insts ~f:rule_act) in
  let rule_proc_insts_str = String.concat ~sep:"\n\n" rule_proc_insts in
  let init_str = sprintf "ASSIGN\n%s" (init_act init) in
  let property_strs = 
    List.concat (List.map properties ~f:(prop_to_insts ~types))
    |> List.map ~f:prop_act
  in
  let prop_str = String.concat ~sep:"\n\n" property_strs in
  let rule_procs_str = String.concat ~sep:"\n\n---------\n\n" rule_procs in
  let strs = [vardef_str; rule_proc_insts_str; init_str; prop_str] in
  let main_module = 
    sprintf "MODULE main\n%s" (String.concat ~sep:"\n\n--------------------\n\n" strs)
  in
  sprintf "%s\n\n--------------------\n\n%s" main_module rule_procs_str
