(** Generate Isabelle code

    @author Yongjian Li <lyj238@gmail.com>
    @author Kaiqiang Duan <duankq@ios.ac.cn>
*)


open Utils
open Core.Std
open Re2
open Paramecium
open Loach
open InvFinder

exception Unsupported of string

let types_ref = ref []

let analyze_rels_among_pfs pfs_lists =
  let rec wrapper pfs_lists res =
    match pfs_lists with
    | [] -> raise Empty_exception (*TODO*)
    | [_] -> res
    | pfs_list::pfs_lists' ->
      let parts = List.map pfs_list ~f:(fun (Paramfix(vn, tn, c)) ->
        let related =
          List.filter (List.concat pfs_lists') ~f:(fun (Paramfix(_, tn', _)) -> tn = tn')
        in
        let equals = List.filter related ~f:(fun (Paramfix(_, _, c')) -> c = c') in
        if List.is_empty equals then
          String.concat ~sep:"\\<and>" (List.map related ~f:(fun (Paramfix(vn', _, _)) ->
            sprintf "%s~=%s" vn vn'
          ))
        else begin
          String.concat ~sep:"\\<and>" (List.map equals ~f:(fun (Paramfix(vn', _, _)) ->
            sprintf "%s=%s" vn vn'
          ))
        end
      ) in
      let r = String.concat ~sep:"\\<and>" (List.filter parts ~f:(fun s -> not (s = ""))) in
      wrapper pfs_lists' (res@[r])
  in
  List.filter (wrapper pfs_lists []) ~f:(fun s -> not (s = ""))
  |> String.concat ~sep:"\\<and>"

let get_pf_name_list pfs =
  String.concat ~sep:" " (List.map pfs ~f:(fun pf ->
    let Paramfix(vn, _, _) = pf in vn
  ))

let analyze_rels_in_pfs t name pfs =
  let pfs_str_of_a_type pfs =
    let part1 = List.map pfs ~f:(fun pf ->
      let Paramfix(vn, _, _) = pf in sprintf "%s\\<le>N" vn
    ) in
    let pairs = combination pfs 2 in
    let part2 = List.map pairs ~f:(fun [pf1; pf2] ->
      let Paramfix(vn1, _, _), Paramfix(vn2, _, _) = pf1, pf2 in sprintf "%s~=%s" vn1 vn2
    ) in
    String.concat ~sep:"\\<and>" (part1@part2)
  in
  let param_str_part =
    partition pfs ~f:(fun (Paramfix(_, tn, _)) -> tn)
    |> List.map ~f:pfs_str_of_a_type
    |> String.concat ~sep:"\\<and>"
  in
  if List.is_empty pfs then
    sprintf "%s=%s %s" t name (get_pf_name_list pfs)
  else
    sprintf "%s\\<and>%s=%s %s" param_str_part t name (get_pf_name_list pfs)

let get_pd_name_list pds =
  String.concat ~sep:" " (List.map pds ~f:(fun pd ->
    let Paramdef(vn, _) = pd in vn
  ))

let analyze_rels_in_pds t name pds =
  let pds_str_of_a_type pds =
    let part1 = List.map pds ~f:(fun pd ->
      let Paramdef(vn, _) = pd in sprintf "%s\\<le>N" vn
    ) in
    let pairs = combination pds 2 in
    let part2 = List.map pairs ~f:(fun [pd1; pd2] ->
      let Paramdef(vn1, _), Paramdef(vn2, _) = pd1, pd2 in sprintf "%s~=%s" vn1 vn2
    ) in
    String.concat ~sep:"\\<and>" (part1@part2)
  in
  let param_str_part =
    partition pds ~f:(fun (Paramdef(_, tn)) -> tn)
    |> List.map ~f:pds_str_of_a_type
    |> String.concat ~sep:"\\<and>"
  in
  if List.is_empty pds then
    sprintf "%s=%s %s" t name (get_pd_name_list pds)
  else
    sprintf "%s\\<and>%s=%s %s" param_str_part t name (get_pd_name_list pds)

let gen_tmp_vars n =
  let nums = up_to n in
  List.map nums ~f:(fun i -> sprintf "i%d" i)









let quant_in_rule = ref false

let const_act c =
  match c with
  | Boolc(b) ->
    Some (sprintf "definition %b::\"scalrValueType\" where [simp]: \"%b\\<equiv> boolV %s\""
      b b (if b then "True" else "False")
    )
  | Strc(s) ->
    Some (sprintf "definition %s::\"scalrValueType\" where [simp]: \"%s\\<equiv> enum ''control'' ''%s''\""
      s s s
    )
  | Intc(i) -> None

let const_to_str c =
  match c with
  | Boolc(b) -> sprintf "%b" b
  | Strc(s) -> s
  | Intc(i) -> sprintf "%d" i

let type_act (Enum(name, consts)) =
  let const_strs = List.filter_map consts ~f:const_act in
  match const_strs with
  | [] -> None
  | _ -> Some (String.concat ~sep:"\n" const_strs)

let var_act (Arr(name_with_prs)) =
  let cast_to_string init prs =
    List.fold prs ~init ~f:(fun res x -> sprintf "(Para %s %s)" res (name_of_param x))
  in
  match name_with_prs with
  | [] -> raise Empty_exception
  | (name, prs)::name_with_prs' ->
    let ident = sprintf "(Ident ''%s'')" name in
    let init = cast_to_string ident prs in
    List.fold name_with_prs' ~init ~f:(fun res (name, prs) ->
      cast_to_string (sprintf "(Field %s ''%s'')" res name) prs
    )

let paramref_to_index pr =
  match pr with
  | Paramref(name) -> name
  | Paramfix(_, _, c) -> (
    match c with
    | Intc(i) -> sprintf "%d" i
    | _ -> raise (Unsupported("Non-integer indexes are not supported yet"))
  )

let rec exp_act e =
  match e with
  | Const(c) -> sprintf "(Const %s)" (const_to_str c)
  | Var(v) -> sprintf "(IVar %s)" (var_act v)
  | Param(pr) -> sprintf "(Const (index %s))" (paramref_to_index pr)
  | Ite(f, e1, e2) -> sprintf "(iteForm %s %s %s)"
    (formula_act f) (exp_act e1) (exp_act e2)
and formula_act f =
  match f with
  | Chaos -> "chaos"
  | Miracle -> "miracle"
  | Eqn(e1, e2) -> sprintf "(eqn %s %s)" (exp_act e1) (exp_act e2)
  | Neg(g) -> sprintf "(neg %s)" (formula_act g)
  | AndList(fl) -> (
    match fl with
    | [] -> formula_act chaos
    | [g] -> formula_act g
    | f1::f2::fl' -> 
      let init = sprintf "(andForm %s %s)" (formula_act f1) (formula_act f2) in
      List.fold fl' ~init ~f:(fun res x -> sprintf "(andForm %s %s)" res (formula_act x))
  )
  | OrList(fl) -> (
    match fl with
    | [] -> formula_act miracle
    | [g] -> formula_act g
    | f1::f2::fl' -> 
      let init = sprintf "(orForm %s %s)" (formula_act f1) (formula_act f2) in
      List.fold fl' ~init ~f:(fun res x -> sprintf "(orForm %s %s)" res (formula_act x))
  )
  | Imply(f1, f2) -> sprintf "(implyForm %s %s)" (formula_act f1) (formula_act f2)
  | ForallFormula(paramdefs, form) ->
    quant_in_rule := true;
    begin
      match paramdefs with
      | [] -> raise Empty_exception
      | [Paramdef(name, tname)] ->
        let form_str = formula_act form in
        sprintf "(forallForm (down N) (\\<lambda>%s. %s))" name form_str
      | _ -> raise (Unsupported "More than 1 paramters in forall are not supported yet")
    end
  | ExistFormula(paramdefs, form) ->
    quant_in_rule := true;
    begin
      match paramdefs with
      | [] -> raise Empty_exception
      | [Paramdef(name, tname)] ->
        let form_str = formula_act form in
        sprintf "(existsForm (down N) (\\<lambda>%s. %s))" name form_str
      | _ -> raise (Unsupported "More than 1 paramters in exists are not supported yet")
    end

let statement_act statement =
  let Parallel(ite_formed) = eliminate_ifelse statement in
  let rec trans bs =
    match bs with
    | Assign(v, e) -> sprintf "(assign (%s, %s))" (var_act v) (exp_act e)
    | ForStatement(s, pd) ->
      quant_in_rule := true;
      begin
        match pd with
        | [] -> raise Empty_exception
        | [Paramdef(name, tname)] ->
          let type_range = name2type ~tname ~types:(!types_ref) in
          let s_str = trans s in
          sprintf "(forallSent (down N) (\\<lambda>%s. %s))" name s_str
        | _ -> raise (Unsupported "More than 1 paramters in for statement are not supported yet")
      end
    | _ -> raise Empty_exception
  in
  sprintf "(parallelList [%s])" (String.concat ~sep:", " (List.map ite_formed ~f:trans))

let rule_quant_table = Hashtbl.create ~hashable:String.hashable ()

let rule_act r =
  quant_in_rule := false;
  let Rule(name, pds, f, s) = r in
  let pd_count_t = List.map pds ~f:(fun _ -> "nat") in
  let pd_str = String.concat ~sep:" \\<Rightarrow> " pd_count_t in
  let rule_type =
    if pd_str = "" then "rule" else sprintf "%s \\<Rightarrow> rule" pd_str
  in
  let pd_names = String.concat ~sep:" " (List.map pds ~f:(fun (Paramdef(n, _)) -> n)) in
  let guard = formula_act f in
  let statements = statement_act s in
  let quant = if (!quant_in_rule) then " N" else "" in
  let quant_type = if (!quant_in_rule) then "nat \\<Rightarrow> " else "" in
  let constraints =
    if List.is_empty pds then
      sprintf "(%s%s)" (analyze_rels_in_pds "r" name pds) quant
    else
      sprintf "(\\<exists> %s. %s%s)" (get_pd_name_list pds) (analyze_rels_in_pds "r" name pds) quant
  in
  Hashtbl.replace rule_quant_table ~key:name ~data:quant;
  constraints,
  sprintf "definition %s::\"%s%s\" where [simp]:
\"%s %s%s\\<equiv>\nlet g = %s in\nlet s = %s in\nguard g s\""
    name quant_type rule_type name pd_names quant guard statements

let rules_act rs =
  let rule_inst_strs, rules_strs = List.unzip (List.map rs ~f:rule_act) in
  let rstrs = String.concat ~sep:"\n\n" rules_strs in
  let r_insts_str = String.concat ~sep:" \\<or>\n" rule_inst_strs in
  sprintf "%s\n\ndefinition rules::\"nat \\<Rightarrow> rule set\" where [simp]:
\"rules N \\<equiv> {r.\n%s\n}\"" rstrs r_insts_str

let rec paramecium_exp_to_loach e =
  match e with
  | Paramecium.Const(c) -> const c
  | Var(v) -> var v
  | Param(pr) -> param pr
  | Ite(f, e1, e2) ->
    ite (paramecium_form_to_loach f) (paramecium_exp_to_loach e1) (paramecium_exp_to_loach e2)
and paramecium_form_to_loach form =
  match form with
  | Paramecium.Chaos -> chaos
  | Paramecium.Miracle -> miracle
  | Paramecium.Eqn(e1, e2) -> eqn (paramecium_exp_to_loach e1) (paramecium_exp_to_loach e2)
  | Paramecium.Neg(f) -> neg (paramecium_form_to_loach f)
  | Paramecium.AndList(fl) -> andList (List.map fl ~f:paramecium_form_to_loach)
  | Paramecium.OrList(fl) -> orList (List.map fl ~f:paramecium_form_to_loach)
  | Paramecium.Imply(f1, f2) -> imply (paramecium_form_to_loach f1) (paramecium_form_to_loach f2)

let inv_act cinv =
  let InvFinder.ConcreteProp(Paramecium.Prop(name, pds, gened_inv), pfs) = cinv in
  let gened_inv' = paramecium_form_to_loach gened_inv in
  let has_not_sym = List.exists pfs ~f:(fun (Paramfix(_, _, c)) -> c = intc 0) in
  let pds' =
    if has_not_sym then
      let Paramfix(name, _, _) = List.find_exn pfs ~f:(fun (Paramfix(_, _, c)) -> c = intc 0) in
      List.filter pds ~f:(fun (Paramdef(n, _)) -> not (n = name))
    else begin pds end
  in
  let gened_inv'' =
    if has_not_sym then
      let not_sym_pf = List.find_exn pfs ~f:(fun (Paramfix(_, _, c)) -> c = intc 0) in
      apply_form gened_inv' ~p:[not_sym_pf]
    else begin gened_inv' end
  in
  let pd_count_t = List.map pds' ~f:(fun _ -> "nat") in
  let pd_str = String.concat ~sep:" \\<Rightarrow> " pd_count_t in
  let inv_type =
    if pd_str = "" then "formula" else sprintf "%s \\<Rightarrow> formula" pd_str
  in
  let pd_names = String.concat ~sep:" " (List.map pds' ~f:(fun (Paramdef(n, _)) -> n)) in
  name, List.length pds', sprintf "definition %s::\"%s\" where [simp]:
\"%s %s \\<equiv>\n%s\"" name inv_type name pd_names (formula_act (neg gened_inv''))

let invs_act cinvs =
  let invs_with_pd_count = List.map cinvs ~f:inv_act in
  let inv_strs = String.concat ~sep:"\n\n" (List.map invs_with_pd_count ~f:(fun (_, _, s) -> s)) in
  let inv_insts_str = String.concat ~sep:" \\<or>\n" (
    List.map cinvs ~f:(fun (ConcreteProp(Prop(name, pds, _), _)) ->
      if List.is_empty pds then
        sprintf "(%s)" (analyze_rels_in_pds "f" name pds)
      else
        sprintf "(\\<exists> %s. %s)" (get_pd_name_list pds) (analyze_rels_in_pds "f" name pds)
    )
  ) in
  sprintf "%s\n\ndefinition invariants::\"nat \\<Rightarrow> formula set\" where [simp]:
\"invariants N \\<equiv> {f.\n%s\n}\"" inv_strs inv_insts_str









let init_act statement i =
  let quant, body =
    match statement with
    | Assign(v, e) -> "", sprintf "(eqn %s %s)" (exp_act (var v)) (exp_act e)
    | IfelseStatement(f, Assign(v, e1), Assign(_, e2)) ->
      "", sprintf "(eqn %s (iteForm %s %s %s))" (exp_act (var v)) (formula_act f) (exp_act e1) (exp_act e2)
    | ForStatement(Assign(v, e), pd) ->
      begin
        match pd with
        | [] -> raise Empty_exception
        | [Paramdef(name, tname)] ->
          let type_range = name2type ~tname ~types:(!types_ref) in
          let s_str = sprintf "(eqn %s %s)" (exp_act (var v)) (exp_act e) in
          "N", sprintf "(forallForm (down N) (%% %s . %s))" name s_str
        | _ -> raise (Unsupported "More than 1 paramters in exists are not supported yet")
      end
    | ForStatement(IfelseStatement(f, Assign(v, e1), Assign(_, e2)), pd) ->
      begin
        match pd with
        | [] -> raise Empty_exception
        | [Paramdef(name, tname)] ->
          let type_range = name2type ~tname ~types:(!types_ref) in
          let s_str = sprintf "(eqn %s (iteForm %s %s %s))"
            (exp_act (var v)) (formula_act f) (exp_act e1) (exp_act e2) in
          "N", sprintf "(forallForm (down N) (%% %s . %s))" name s_str
        | _ -> raise (Unsupported "More than 1 paramters in exists are not supported yet")
      end
    | _ -> raise Empty_exception
  in
  let init_type_str = if quant = "" then "formula" else begin "nat \\<Rightarrow> formula" end in
  quant, sprintf "definition initSpec%d::\"%s\" where [simp]:
\"initSpec%d %s \\<equiv> %s\"" i init_type_str i quant body

let inits_act statements =
  let balanced = balance_ifstatement statements in
  let init_no = up_to (List.length balanced) in
  let init_strs_with_quant = List.map2_exn balanced init_no ~f:init_act in
  let init_strs = String.concat ~sep:"\n\n" (List.map init_strs_with_quant ~f:(fun (_, s) -> s)) in
  let init_insts_str = String.concat ~sep:",\n" (
    List.map2_exn init_no (List.map init_strs_with_quant ~f:(fun (q, _) -> q)) ~f:(fun i q ->
      sprintf "(initSpec%d %s)" i q
    )
  ) in
  sprintf "%s\n\ndefinition allInitSpecs::\"nat \\<Rightarrow> formula list\" where [simp]:
\"allInitSpecs N \\<equiv> [\n%s\n]\"" init_strs init_insts_str







module ToIsabelle = struct

  let const_act c =
    match c with
    | Intc(i) -> sprintf "%d" i
    | Strc(s) -> s
    | Boolc(b) -> sprintf "%b" b

  let paramref_act pr =
    match pr with
    | Paramref(name) -> name
    | Paramfix(_, _, c) -> const_act c

  let var_act (Arr(vs)) =
    String.concat ~sep:"_" (List.map vs ~f:(fun (name, prs) ->
      sprintf "%s%s" name (String.concat (List.map prs ~f:(fun pr ->
        sprintf "[%s]" (paramref_act pr)
      )))
    ))
  
  let exp_act e =
    match e with
    | Paramecium.Const(c) -> const_act c
    | Var(v) -> var_act v
    | Param(pr) -> paramref_act pr
    | Ite(_) -> raise Empty_exception

  let rec form_act f =
    match f with
    | Paramecium.Chaos -> "True"
    | Miracle -> "False"
    | Eqn(e1, e2) -> sprintf "%s=%s" (exp_act e1) (exp_act e2)
    | Neg(f) -> sprintf "\\<not>(%s)" (form_act f)
    | AndList(fl) ->
      String.concat ~sep:"\\<and>" (List.map fl ~f:(fun f -> sprintf "(%s)" (form_act f)))
    | OrList(fl) -> 
      String.concat ~sep:"\\<or>" (List.map fl ~f:(fun f -> sprintf "(%s)" (form_act f)))
    | Imply(f1, f2) -> sprintf "(%s)\\<rightarrow>(%s)" (form_act f1) (form_act f2)

end









let gen_case_1 =
"    have \"?P1 s\"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have \"invHoldForRule' s f r (invariants N)\" by auto"

let gen_case_2 =
"    have \"?P2 s\"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have \"invHoldForRule' s f r (invariants N)\" by auto"

let gen_case_3 (ConcreteProp(Prop(_, _, f), _)) =
  let f = paramecium_form_to_loach f in
  sprintf
"    have \"?P3 s\"
    by (cut_tac a1 a2 b1 c1, simp, rule_tac x=\"%s\" in exI, auto)
    then have \"invHoldForRule' s f r (invariants N)\" by auto" (formula_act (neg f))

let gen_branch branch case =
  sprintf "  moreover {\n    assume c1: \"%s\"\n%s\n  }" branch case

let gen_inst relations condition =
  let analyze_branch {rule; inv; branch; relation} =
    let ConcreteProp(Prop(_, _, g), pfs) = branch in
    let ConcreteRule(_, pfs_rule) = rule in
    let ConcreteProp(_, pfs_prop) = inv in
    let pfs_current = pfs_rule@pfs_prop in
    let branch_constraint =
      let overflow = List.filter pfs ~f:(fun (Paramfix(_, tn, c)) ->
        not (List.exists pfs_current ~f:(fun (Paramfix(_, tn', c')) -> tn = tn' && c = c'))
      ) in
      let param_rels = String.concat ~sep:"\\<and>" (List.map overflow ~f:(fun (Paramfix(vn, _, _)) ->
        String.concat ~sep:"\\<and>" (List.map pfs_current ~f:(fun (Paramfix(vn', _, _)) ->
          sprintf "%s~=%s" vn vn'
        ))
      )) in
      match overflow with
      | [] -> ""
      | _ -> sprintf "\\<exists> %s. %s\\<and>" (get_pf_name_list overflow) param_rels
    in
    let branch_str = sprintf "(%s%s)" branch_constraint (ToIsabelle.form_act g) in
    let case_str =
      match relation with
      | InvHoldForRule1 -> gen_case_1
      | InvHoldForRule2 -> gen_case_2
      | InvHoldForRule3(cp) -> gen_case_3 cp
    in
    branch_str, gen_branch branch_str case_str
  in
  let branches, moreovers = List.unzip (List.map relations ~f:analyze_branch) in
  sprintf 
"moreover {
  assume b1: \"%s\"
  have \"%s\" by auto
%s
  ultimately have \"invHoldForRule' s f r (invariants N)\" by auto
}" condition (String.concat ~sep:"\\<or>" branches) (String.concat ~sep:"\n" moreovers)

let analyze_lemma rels pfs_prop =
  let pfs =
    match rels with
    | [] -> raise Empty_exception
    | {rule; inv=_; branch=_; relation=_}::_ ->
      let ConcreteRule(_, pfs) = rule in
      pfs
  in
  let condition = analyze_rels_among_pfs [pfs; pfs_prop] in
  let moreovers = gen_inst rels (if condition = "" then "True" else condition) in
  condition, moreovers

let gen_lemma relations rules =
  let crule, cinv =
    match relations with
    | ({rule; inv; branch=_; relation=_}::_)::_ -> rule, inv
    | _ -> raise Empty_exception
  in
  let ConcreteProp(Prop(pn, _, _), pfs_prop) = cinv in
  let prop_constraint =
    if List.is_empty pfs_prop then
      sprintf "%s" (analyze_rels_in_pfs "f" pn pfs_prop)
    else
      sprintf "\\<exists> %s. %s"
        (get_pf_name_list pfs_prop) (analyze_rels_in_pfs "f" pn pfs_prop)
  in
  match crule with
  | ConcreteRule(rn, pfs_r) ->
    let rn = get_rname_of_crname rn in
    let res = List.map relations ~f:(fun rels -> analyze_lemma rels pfs_prop) in
    let conditions, moreovers = List.unzip res in
    let rule_constraint =
      if List.is_empty pfs_r then
        sprintf "%s%s"
          (analyze_rels_in_pfs "r" rn pfs_r)
          (Hashtbl.find_exn rule_quant_table rn)
      else
        sprintf "\\<exists> %s. %s%s"
          (get_pf_name_list pfs_r)
          (analyze_rels_in_pfs "r" rn pfs_r)
          (Hashtbl.find_exn rule_quant_table rn)
    in
    let conditions = List.filter conditions ~f:(fun s -> not (s = "")) in
    sprintf
"lemma %sVs%s:
assumes a1: \"%s\" and
a2: \"%s\"
shows \"invHoldForRule' s f r (invariants N)\" (is \"?P1 s \\<or> ?P2 s \\<or> ?P3 s\")
proof -
%s
%s
have %s by auto
%s
ultimately show \"invHoldForRule' s f r (invariants N)\" by auto
qed"
    rn pn
    rule_constraint
    prop_constraint
    (if List.is_empty pfs_r then "" else
      sprintf "from a1 obtain %s where a1:\"%s\" by blast"
        (get_pf_name_list pfs_r)
        (analyze_rels_in_pfs "r" rn pfs_r)
    )
    (if List.is_empty pfs_prop then "" else
      sprintf "from a2 obtain %s where a2:\"%s\" by blast"
        (get_pf_name_list pfs_prop)
        (analyze_rels_in_pfs "f" pn pfs_prop)
    )
    (if conditions = [] then "True" else "\""^String.concat ~sep:"\\<or>" conditions^"\"")
    (String.concat ~sep:"\n" moreovers)
  | AllRuleInst(rn) ->
    let rn = get_rname_of_crname rn in
    match List.find rules ~f:(fun (Rule(n, _, _, _)) -> rn = n) with
    | None -> Prt.error (sprintf "can't find rule %s" rn); raise Empty_exception
    | Some(the_rule) ->
      let Rule(_, pds, _, _) = the_rule in
      let rule_constraint =
        if List.is_empty pds then
          sprintf "%s%s"
            (analyze_rels_in_pds "r" rn pds)
            (Hashtbl.find_exn rule_quant_table rn)
        else
          sprintf "\\<exists> %s. %s%s"
            (get_pd_name_list pds)
            (analyze_rels_in_pds "r" rn pds)
            (Hashtbl.find_exn rule_quant_table rn)
      in
      sprintf
  "lemma %sVs%s:
  assumes a1: \"%s\" and
  a2: \"%s\"
  shows \"invHoldForRule f r (invariants N)\"
  by auto
  "
      rn pn
      rule_constraint
      prop_constraint







let gen_lemma_invs_on_ini invs =
  let do_work (Paramecium.Prop(name, pds, _)) =
    sprintf
"lemma iniImply_%s:
assumes a1: \"%s\"
and a2: \"formEval (andList (allInitSpecs N)) s\"
shows \"formEval f s\"
using a1 a2 by auto"
      name
      (sprintf "(\\<exists> %s. %s)" (get_pd_name_list pds) (analyze_rels_in_pds "f" name pds))
  in
  String.concat ~sep:"\n\n" (List.map invs ~f:do_work)







let analyze_rules_invs rules invs =
  let inv_param_constraints =
    List.map invs ~f:(fun (Paramecium.Prop(name, pds, _)) -> 
      sprintf "(\\<exists> %s. %s)" (get_pd_name_list pds) (analyze_rels_in_pds "f" name pds)
    )
    |> String.concat ~sep:" \\<or>\n      "
  in
  let analyze_rule_invs (Rule(rname, pds, _, _)) =
    let analyze_rule_inv (Paramecium.Prop(pname, pds, _)) =
      sprintf
"    moreover {
      assume f1: \"%s\"
      have \"invHoldForRule' s f r (invariants N)\"
      by (cut_tac b1 b2 d1 f1, metis %sVs%s)
    }"
        (sprintf "(\\<exists> %s. %s)" (get_pd_name_list pds) (analyze_rels_in_pds "f" pname pds))
        rname pname
    in
    sprintf
"  moreover {
    assume d1: \"\\<exists> %s. %s\"
    have e1: \"%s\"
    by (cut_tac b1, auto)
%s
    ultimately have \"invHoldForRule' s f r (invariants N)\"
    by blast
  }"
      (get_pd_name_list pds) (analyze_rels_in_pds "r" rname pds)
      inv_param_constraints
      (String.concat ~sep:"\n" (List.map invs ~f:(analyze_rule_inv)))
  in
  String.concat ~sep:"\n" (List.map rules ~f:(analyze_rule_invs))

let gen_main rules invs =
  let rule_param_constraints =
    List.map rules ~f:(fun (Rule(name, pds, _, _)) ->
      if List.is_empty pds then
        sprintf "(%s%s)"
          (analyze_rels_in_pds "r" name pds)
          (Hashtbl.find_exn rule_quant_table name)
      else
        sprintf "(\\<exists> %s. %s%s)"
          (get_pd_name_list pds)
          (analyze_rels_in_pds "r" name pds)
          (Hashtbl.find_exn rule_quant_table name)
    )
    |> String.concat ~sep:" \\<or>\n    "
  in
  let inv_param_constraints =
    List.map invs ~f:(fun (Paramecium.Prop(name, pds, _)) ->
      if List.is_empty pds then
        sprintf "(%s)" (analyze_rels_in_pds "f" name pds)
      else
        sprintf "(\\<exists> %s. %s)" (get_pd_name_list pds) (analyze_rels_in_pds "f" name pds)
    )
    |> String.concat ~sep:" \\<or>\n      "
  in
  let analyze_inv_on_ini (Paramecium.Prop(name, pds, _)) =
    sprintf
"    moreover {
      assume d1: \"%s\"
      have \"formEval f s\"
      apply (rule iniImply_%s)
      apply (cut_tac d1, assumption)
      by (cut_tac b4, simp)
    }"
      (sprintf "(\\<exists> %s. %s)" (get_pd_name_list pds) (analyze_rels_in_pds "f" name pds))
      name
  in
  sprintf
"lemma main:
assumes a1: \"s \\<in> reachableSet {andList (allInitSpecs N)} (rules N)\"
and a2: \"0 < N\"
shows \"\\<forall> f. f \\<in> (invariants N) --> formEval f s\"
proof (rule newconsistentLemma)
show \"newconsistent (invariants N) {andList (allInitSpecs N)} (rules N)\"
proof (cut_tac a1, unfold newconsistent_def, rule conjI)
show \"\\<forall> f ini s. f \\<in> (invariants N) --> ini \\<in> {andList (allInitSpecs N)} \
--> formEval ini s --> formEval f s\"
proof ((rule allI)+, (rule impI)+)
  fix f ini s
  assume b1: \"f \\<in> (invariants N)\" and b2: \"ini \\<in> {andList (allInitSpecs N)}\" \
and b3: \"formEval ini s\"
  have b4: \"formEval (andList (allInitSpecs N)) s\"
  by (cut_tac b2 b3, simp)
  show \"formEval f s\"
  proof -
    have c1: \"%s\"
    by (cut_tac b1, simp)
%s
  ultimately show \"formEval f s\"
  by auto
qed
qed
next show \"\\<forall> f r s. f \\<in> invariants N --> r \\<in> rules N --> \
invHoldForRule' s f r (invariants N)\"
proof ((rule allI)+, (rule impI)+)
  fix f r s
  assume b1: \"f \\<in> invariants N\" and b2: \"r \\<in> rules N\"
  have c1: \"%s\"
  by (cut_tac b2, auto)
  %s
  ultimately show \"invHoldForRule' s f r (invariants N)\" by blast
qed
qed
next show \"s \\<in> reachableSet {andList (allInitSpecs N)} (rules N)\"
  by (metis a1)
qed"
  inv_param_constraints
  (String.concat ~sep:"\n" (List.map invs ~f:analyze_inv_on_ini))
  rule_param_constraints
  (analyze_rules_invs rules invs)









let protocol_act {name; types; vardefs; init; rules; properties} cinvs_with_varnames relations =
  types_ref := types;
  let types_str = String.concat ~sep:"\n" (List.filter_map types ~f:type_act) in
  let rules_str = rules_act rules in
  let (cinvs, _) = List.unzip cinvs_with_varnames in
  let invs_str = invs_act cinvs in
  let inits_str = inits_act init in
  let lemmas_str = 
    String.concat ~sep:"\n\n" (List.map relations ~f:(fun rel -> gen_lemma rel rules))
  in
  let invs = List.map cinvs ~f:(fun (ConcreteProp(p, _)) -> p) in
  let lemma_invs_on_ini = gen_lemma_invs_on_ini invs in
  let main_lemma = gen_main rules invs in
  sprintf "\
theory %s imports paraTheory
begin
section{*Main definitions*}
%s\n
%s\n
%s\n
%s\n
%s\n
%s\n
%s\n
end\n" name types_str rules_str invs_str inits_str lemmas_str lemma_invs_on_ini main_lemma
