(** For find invariants and causal relations based on Paramecium

    @author Yongjian Li <lyj238@gmail.com>
    @author Kaiqiang Duan <duankq@ios.ac.cn>
*)

open Utils
open Formula
open Paramecium

open Core.Std

(** Raised when parallel statements haven't been cast to assign list *)
exception Unexhausted_flat_parallel

(** Raised when circular parallel assignments detected *)
exception Circular_parallel_assign

(** Raised when require to check a inv has too many paramters *)
exception Parameter_overflow

(** Concrete rule

    + ConcreteRule: instantiated rule, concrete param list
*)
type concrete_rule =
  | ConcreteRule of string * paramref list
with sexp

let concrete_rule r ps =
  let Rule(name, _, _, _) = r in
  ConcreteRule(name, ps)

(** Concrete property

    + ConcreteProp: property, concrete param list
*)
type concrete_prop =
  | ConcreteProp of prop * paramref list
with sexp

let concrete_prop property ps = ConcreteProp(property, ps)

(** Causal relations

  + InvHoldForRule1
  + InvHoldForRule2
  + InvHoldForRule3: the new concrete invariant found
*)
type relation =
  | InvHoldForRule1
  | InvHoldForRule2
  | InvHoldForRule3 of concrete_prop
with sexp

let invHoldForRule1 = InvHoldForRule1
let invHoldForRule2 = InvHoldForRule2
let invHoldForRule3 p = InvHoldForRule3 p

(** InvFinder type, i.e., causal relation table *)
type t = {
  rule: concrete_rule;
  inv: concrete_prop;
  branch: formula;
  relation: relation;
}
with sexp

let type_defs = ref []
let protocol_name = ref ""
let rule_table = Hashtbl.create ~hashable:String.hashable ()

(* Convert statements to a list of assignments *)
let rec statement_2_assigns statement =
  match statement with
  | Parallel(sl) -> List.concat (List.map sl ~f:statement_2_assigns)
  | Assign(v, e) -> [(v, e)]

let simplify_inst_guard r =
  let Rule(n, p, f, s) = r in
  rule n p (simplify f) s

(* Convert rule to concrete rules *)
let rule_2_concrete r ps =
  let r_insts =
    if List.length ps = 0 then [(simplify_inst_guard r, [])]
    else List.map ps ~f:(fun p -> simplify_inst_guard (apply_rule r ~p), p)
  in
  let rec store_rules rs =
    match rs with
    | [] -> ()
    | (ri, p)::rs' ->
      let Rule(name, _, guard, statement) = ri in
      let guards = flat_and_to_list (guard) in
      let assigns = statement_2_assigns statement in
      Hashtbl.replace rule_table ~key:name ~data:(ri, concrete_rule ri p, guards, assigns);
      store_rules rs'
  in
  store_rules r_insts;;

(* Convert concrete rule to rule instances *)
let concrete_rule_2_rule_inst cr =
  let ConcreteRule(rname, _) = cr in
  match Hashtbl.find rule_table rname with
  | Some(r) -> r
  | None ->
    Prt.error (sprintf "%s not in [%s]" rname (String.concat ~sep:", " (Hashtbl.keys rule_table)));
    raise Empty_exception

(* Convert concrete property to formula *)
let concrete_prop_2_form cprop =
  let ConcreteProp(property, pfs) = cprop in
  let Prop(_, _, form) = property in
  apply_form form ~p:pfs

(* Convert formula to concrete property *)
let form_2_concreate_prop ?(id=0) form =
  let new_inv_name_base = "inv__" in
  (* Generate names for new invariants found *)
  let next_inv_name id = sprintf "%s%d" new_inv_name_base id in
  let normalized = normalize form ~types:!type_defs in
  let (pds, pfs, form') = Generalize.form_act normalized in
  let property = prop (next_inv_name id) pds form' in
  concrete_prop property pfs

(** Convert relation to a string *)
let relation_2_str relation =
  match relation with
  | InvHoldForRule1 -> "invHoldForRule1"
  | InvHoldForRule2 -> "invHoldForRule2"
  | InvHoldForRule3(cp) -> 
    let form = (concrete_prop_2_form cp) in
    sprintf "invHoldForRule3-%s" (ToStr.Smv.form_act form)

(** Convert t to a string *)
let to_str {rule; inv; branch; relation} =
  let ConcreteRule(rname, _) = rule in
  let inv_str = ToStr.Smv.form_act (concrete_prop_2_form inv) in
  let branch_str = ToStr.Smv.form_act branch in
  let rel_str = relation_2_str relation in
  sprintf "rule: %s; inv: %s; g: %s; rel: %s" rname inv_str branch_str rel_str





let get_rule_inst_name rname pfs =
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
  sprintf "%s%s" rname (String.concat (List.map pfs ~f:paramref_act))

let sort_pfs pds pfs = List.map pds ~f:(fun (Paramdef(name, _)) ->
  List.find_exn pfs ~f:(fun pr ->
    match pr with
    | Paramfix(n, _, _) -> n = name
    | _ -> raise Empty_exception
  )
)




(* Evaluate exp with assignments
    Result has format (condition, value)
*)
let rec exp_eval exp ~assigns =
  match exp with
  | Const(_) -> [(chaos, exp)]
  | Param(Paramref _) -> raise Unexhausted_inst
  | Param(_) -> [(chaos, exp)]
  | Var(v) ->
    let value = List.Assoc.find assigns v ~equal:(fun x y ->
      ToStr.Smv.var_act x = ToStr.Smv.var_act y
    ) in (
      match value with
      | None -> [(chaos, var v)]
      | Some(e) ->
        let rec analyze_exp e =
          match e with
          | Ite(f, e1, e2) ->
            let f1 =
              let ff = simplify f in
              match ff with | OrList(fl) -> fl | _ -> [ff]
            in
            let f2 =
              let ff = simplify (neg f) in
              match ff with | OrList(fl) -> fl | _ -> [ff]
            in
            let res1 = List.concat (List.map (analyze_exp e1) ~f:(fun (g, e) ->
              List.map f1 ~f:(fun f -> andList [g; f], e)
            )) in
            let res2 = List.concat (List.map (analyze_exp e2) ~f:(fun (g, e) ->
              List.map f2 ~f:(fun f -> andList [g; f], e)
            )) in
            res1@res2
          | _ -> [(chaos, e)]
        in
        List.map (analyze_exp e) ~f:(fun (g, e) -> simplify g, e)
    )
  | Ite(f, e1, e2) -> raise Empty_exception
(* Evaluate formula with assignments
    Result has format (condition, form)
*)
and form_eval form ~assigns =
  match form with
  | Chaos
  | Miracle -> [(chaos, form)]
  | Eqn(e1, e2) ->
    let res1 = exp_eval e1 ~assigns in
    let res2 = exp_eval e2 ~assigns in
    let mixed = cartesian_product [res1; res2] in
    List.map mixed ~f:(fun [(g1, e1); (g2, e2)] ->
      simplify (andList [g1; g2]), eqn e1 e2
    )
  | Neg(f) -> List.map (form_eval f ~assigns) ~f:(fun (g, f) -> g, neg f)
  | AndList(fl) ->
    let mixed = cartesian_product (List.map fl ~f:(form_eval ~assigns)) in
    List.map mixed ~f:(fun pairs ->
      let gs, fl' = List.unzip pairs in
      simplify (andList gs), andList fl'
    )
  | OrList(fl) ->
    let mixed = cartesian_product (List.map fl ~f:(form_eval ~assigns)) in
    List.map mixed ~f:(fun pairs ->
      let gs, fl' = List.unzip pairs in
      simplify (andList gs), orList fl'
    )
  | Imply(ant, cons) ->
    let res1 = form_eval ant ~assigns in
    let res2 = form_eval cons ~assigns in
    let mixed = cartesian_product [res1; res2] in
    List.map mixed ~f:(fun [(g1, ant'); (g2, cons')] ->
      simplify (andList [g1; g2]), imply ant' cons'
    )

(* pre_cond *)
let pre_cond f assigns = form_eval f ~assigns



(* Minify inv by remove useless components one by one *)
let minify_inv_desc inv =
  let rec wrapper necessary parts =
    match parts with
    | [] ->
      if Smv.is_inv (ToStr.Smv.form_act (neg (andList necessary))) then
        necessary
      else begin raise Empty_exception end
    | p::parts' ->
      if Smv.is_inv (ToStr.Smv.form_act (neg (andList (necessary@parts')))) then
        wrapper necessary parts'
      else begin
        wrapper (p::necessary) parts'
      end
  in
  let ls = match inv with | AndList(fl) -> fl | _ -> [inv] in
  andList (wrapper [] ls)

(* Minify inv by add useful components gradually *)
let minify_inv_inc inv =
  let rec wrapper components =
    match components with
    | [] -> 
      Prt.error ("Not invariant: "^ToStr.Smv.form_act inv);
      raise Empty_exception
    | parts::components' ->
      let piece = normalize (andList parts) ~types:(!type_defs) in
      (*let (_, pfs, _) = Generalize.form_act piece in
      Prt.info ("parts: "^ToStr.Smv.form_act (andList parts)^
        "\nnormalized: "^ToStr.Smv.form_act piece^"Res: "^
        (if List.length pfs <= 3 then
          (if Smv.is_inv (ToStr.Smv.form_act (neg piece)) then "true" else "false")
          else begin "unknown" end
        )
      );*)
      let check_inv_res =
        let (_, pfs, _) = Generalize.form_act piece in
        (* TODO *)
        let over = List.filter pfs ~f:(fun pr ->
          match pr with
          | Paramfix(_, _, Intc(i)) -> i > 3
          | _ -> false
        ) in
        let check_with_murphi form =
          let form_str = ToStr.Smv.form_act ~lower:false (neg form) in
          let res = Murphi.is_inv form_str in
          print_endline (sprintf "Check by mu: %s, %b" form_str res); res
        in
        if List.is_empty over then
          try Smv.is_inv (ToStr.Smv.form_act (neg piece)) with
          | Client.Smv.Cannot_check -> check_with_murphi piece
          | _ -> raise Empty_exception
        else begin
          check_with_murphi piece
        end
      in
      if check_inv_res then piece
      else begin wrapper components' end
  in
  let ls = match inv with | AndList(fl) -> fl | _ -> [inv] in
  let components = combination_all ls in
  wrapper components







module InvLib = struct
  
  let index = ref 0

  let pairs = ref []

  let add inv =
    match List.find (!pairs) ~f:(fun (p, _) -> symmetry_form p inv = 0) with
    | Some(_, cinv) -> cinv
    | None ->
      let cinv = form_2_concreate_prop ~id:(!index) inv in
      incr index;
      pairs := ((inv, cinv)::(!pairs));
      cinv

  let add_many invs = List.dedup (List.map invs ~f:add)

  let get_all_cinvs () = List.map (!pairs) ~f:(fun (_, cinv) -> cinv)

  let any_can_be_implied_by inv =
    let rec wrapper invs =
      match invs with
      | [] -> None
      | (old, c_old)::invs' ->
        let res = can_imply inv old in
        if res = None then wrapper invs' else begin Some c_old end
    in
    wrapper (!pairs)


end







(********************************** Module Choose **************************************)

(* Choose a true invariant *)
module Choose = struct

  type level =
    | Tautology of formula
    | Implied of concrete_prop
    | New_inv of formula
    | Not_inv

  let tautology form = Tautology(form)
  let implied old = Implied(old)
  let new_inv form = New_inv(form)
  let not_inv = Not_inv

  (* Check the level of an optional invariant *)
  let check_level ?(must_new=false) inv =
    let inv = simplify inv in
    if is_tautology inv then
      tautology inv
    else begin
      try
        let inv = minify_inv_inc inv in
        (* Because invs are in form of negation, so inv -> old means neg old -> neg inv *)
        let implied_by_old = InvLib.any_can_be_implied_by inv in
        match implied_by_old with
        | Some(old) -> implied old
        | None ->
          let normalized = normalize inv ~types:(!type_defs) in
          if must_new || Smv.is_inv (ToStr.Smv.form_act (neg normalized)) then
            new_inv inv
          else begin
            not_inv
          end
      with
      | _ -> not_inv
    end

  (* choose new inv *)
  let choose guards assigns cons =
    check_level ~must_new:true (simplify (andList (cons::guards)))

end










module SemiPerm = struct

  let semi_table = Hashtbl.create ~hashable:String.hashable ()

  let equal_int a b m n = not ((a <= m - n) && (not (a = b)))

  let equal_list ls1 ls2 m n =
    if List.length ls1 = List.length ls2 && List.length ls1 > 0 then
      let flags = List.map (List.zip_exn ls1 ls2) ~f:(fun (x, y) -> equal_int x y m n) in
      all flags ~f:(fun flag -> flag = true)
    else begin false end

  let equal ls1 ls2 m n =
    (equal_list ls1 ls2 m n) || (equal_list (List.rev ls1) (List.rev ls2) m n)

  let rec semi ls m n =
    match ls with
    | [] -> []
    | ele::ls' ->
      let not_equal = List.filter ls' ~f:(fun x -> not (equal ele x m n)) in
      ele::(semi not_equal m n)

  let semi_perm m n =
    match (m, n) with
    | (m, 0) -> [[]]
    | (0, n) -> []
    | _ -> 
      let nums = List.map (up_to m) ~f:(fun x -> x + 1) in
      semi (combination_permutation nums n) m n

  let gen_of_a_type inv_pds rule_pds =
    match rule_pds with
    | [] -> raise Empty_exception
    | (Paramdef(_, tname))::_ ->
      let trange = name2type ~tname ~types:(!type_defs) in
      let n_inv = List.length inv_pds in
      let n_rule = List.length rule_pds in
      let semi_list = semi_perm (n_inv + n_rule) n_rule in
      let semi_consts = List.map semi_list ~f:(fun ls -> List.map ls ~f:(fun x -> intc x)) in
      let valid_consts = List.filter semi_consts ~f:(fun ls ->
        all ls ~f:(fun x -> List.exists trange ~f:(fun t -> t = x))
      ) in
      List.map valid_consts ~f:(fun ls ->
        List.map2_exn ls rule_pds ~f:(fun c (Paramdef(name, _)) -> paramfix name tname c)
      )


  let gen_paramfixes inv_pds rule_pds =
    let key = String.concat ~sep:";" (List.map (inv_pds@rule_pds) ~f:(fun (Paramdef(name, tname)) ->
      sprintf "%s:%s" name tname
    )) in
    match Hashtbl.find semi_table key with
    | None ->
      let inv_parts = partition_with_label inv_pds ~f:(fun (Paramdef(_, tname)) -> tname) in
      let rule_parts = partition_with_label rule_pds ~f:(fun (Paramdef(_, tname)) -> tname) in
      let paramfixes = 
        List.map rule_parts ~f:(fun (tname, rpds) ->
          let ipds = 
            match List.Assoc.find inv_parts tname with
            | None -> []
            | Some(ls) -> ls
          in
          gen_of_a_type ipds rpds
        )
        |> cartesian_product
        |> List.map ~f:List.concat
      in
      let pf_unsym =
        let all_pfs = cart_product_with_paramfix rule_pds (!type_defs) in
        (* TODO *)
        let has_unsym pfs = List.exists pfs ~f:(fun pr -> 
          match pr with 
          | Paramfix(_, _, c) -> c = intc 0
          | _ -> raise Empty_exception
        ) in
        List.filter all_pfs ~f:has_unsym
      in
      let res = List.map (paramfixes@pf_unsym) ~f:(sort_pfs rule_pds) in
      Hashtbl.replace semi_table ~key ~data:res; res
    | Some(res) -> res

end





module Storage = struct

  let append_file fn lines =
    let f = Out_channel.create fn ~append:true in
    Out_channel.output_lines f lines;
    Out_channel.close f;;
  
  let add_many filename key values convertor =
    let name = sprintf "%s.%s.cache" filename key in
    let strs =
      values
      |> List.map ~f:convertor
      |> List.map ~f:Sexp.to_string
    in
    append_file name strs

  let add filename key value convertor = add_many filename key [value] convertor

  let replace_many filename key values convertor =
    let name = sprintf "%s.%s.cache" filename key in
    let strs =
      values
      |> List.map ~f:convertor
      |> List.map ~f:Sexp.to_string
    in
    Out_channel.write_lines name strs

  let replace filename key value convertor =
    let name = sprintf "%s.%s.cache" filename key in
    let str = Sexp.to_string (convertor value) in
    Out_channel.write_all name str

  let get_many filename key default convertor =
    let name = sprintf "%s.%s.cache" filename key in
    try
      In_channel.read_lines name
      |> List.map ~f:Sexp.of_string
      |> List.map ~f:convertor
    with
    | Sys_error(_) -> default
    | e -> raise e

  let get filename key default convertor =
    let name = sprintf "%s.%s.cache" filename key in
    try
      convertor (Sexp.of_string (In_channel.read_all name))
    with
    | Sys_error(_) -> default
    | e -> raise e

end







  


(* Deal with case invHoldForRule1 *)
let deal_with_case_1 crule cinv g =
  { rule = crule;
    inv = cinv;
    branch = g;
    relation = invHoldForRule1;
  }

(* Deal with case invHoldForRule2 *)
let deal_with_case_2 crule cinv g =
  { rule = crule;
    inv = cinv;
    branch = g;
    relation = invHoldForRule2;
  }

(* Deal with case invHoldForRule3 *)
let deal_with_case_3 crule cinv cons g =
  let Rule(name, _, guard, statement), _, guards, assigns = concrete_rule_2_rule_inst crule in
  let level = Choose.choose (g::guards) assigns cons in
  let (new_inv, causal_cinv) =
    match level with
    | Choose.Tautology(_) -> ([], form_2_concreate_prop chaos)
    | Choose.Implied(old) -> ([], old)
    | Choose.New_inv(inv) ->
      let new_inv_str = ToStr.Smv.form_act inv in
      let old_inv_str = ToStr.Smv.form_act (concrete_prop_2_form cinv) in
      print_endline (sprintf "rule %s, new %s, old %s" name new_inv_str old_inv_str);
      ([inv], form_2_concreate_prop inv)
    | Choose.Not_inv ->
      let ConcreteRule(n, ps) = crule in
      let cp_2_str pr =
        match pr with
        | Paramref(_) -> raise Empty_exception
        | Paramfix(n, _, _) -> sprintf "%s:%s" n (ToStr.Smv.paramref_act pr)
      in
      let params_str = String.concat (List.map ps ~f:cp_2_str) ~sep:", " in
      let inv_str = ToStr.Smv.form_act (concrete_prop_2_form cinv) in
      let guard_str = ToStr.Smv.form_act guard in
      Prt.error (sprintf "\n\n%s, %s\nguard: %s\n%s\n" n params_str guard_str inv_str);
      raise Empty_exception
  in
  (new_inv, { rule = crule;
    inv = cinv;
    branch = g;
    relation = invHoldForRule3 causal_cinv;
  })


(* Find new inv and relations with concrete rule and a concrete invariant *)
let tabular_expans (Rule(_name, _, form, _), crule, _, assigns) ~cinv =
  let inv_inst = simplify (concrete_prop_2_form cinv) in
  (* pre_cond *)
  let obligations =
    pre_cond inv_inst assigns
    |> List.map ~f:(fun (g, o) -> g, simplify o)
  in
  (*Prt.warning (_name^": "^ToStr.Smv.form_act obligation^", "^ToStr.Smv.form_act inv_inst^"\n");*)
  let rec deal_with_case obligations relations =
    match obligations with
    | [] -> relations
    | (g, obligation)::obligations' ->
      let relation = 
        (* case 2 *)
        if obligation = inv_inst || symmetry_form obligation inv_inst = 0 then
          ([], deal_with_case_2 crule cinv g)
        (* case 1 *)
        else if is_tautology (imply form (neg obligation)) then
          ([], deal_with_case_1 crule cinv g)
        (* case 3 *)
        else begin
          deal_with_case_3 crule cinv obligation g
        end
      in
      deal_with_case obligations' (relation::relations)
  in
  deal_with_case obligations []


let compute_rule_inst_names rname_paraminfo_pairs prop_pds =
  List.concat (List.map rname_paraminfo_pairs ~f:(fun (rname, rpds) ->
    match rpds with
    | [] -> [rname]
    | _ ->
      SemiPerm.gen_paramfixes prop_pds rpds
      |> List.map ~f:(fun pfs -> get_rule_inst_name rname pfs)
  ))

let fix_relations_with_cinvs cinvs relations =
  let pairs = List.map cinvs ~f:(fun cinv -> concrete_prop_2_form cinv, cinv) in
  if pairs = [] then () else begin
    print_endline (String.concat ~sep:"\n" (
      List.map pairs ~f:(fun (f, _) -> "NewInv: "^ToStr.Smv.form_act f)
    ))
  end;
  let rec wrapper relations res =
    match relations with
    | [] -> res
    | relation::relations' ->
      let fixed = 
        match relation with
        | {rule; inv; branch; relation=InvHoldForRule3(rel_cinv)} ->
          begin
            let rel_inv = concrete_prop_2_form rel_cinv in
            match List.find pairs ~f:(fun (inv, _) ->
              symmetry_form inv rel_inv = 0
            ) with
            | Some(_, cinv) -> {rule; inv; branch; relation = invHoldForRule3 cinv}
            | None -> Prt.warning ("implied by old:"^(ToStr.Smv.form_act rel_inv)); relation
          end
        | _ -> relation
      in
      wrapper relations' (res@[fixed])
  in
  wrapper relations []

let get_res_of_cinv cinv rname_paraminfo_pairs =
  let (ConcreteProp(Prop(_, prop_pds, _), _)) = cinv in
  let rule_inst_names = compute_rule_inst_names rname_paraminfo_pairs prop_pds in
  let crules = 
    List.map rule_inst_names ~f:(fun n -> 
      match Hashtbl.find rule_table n with
      | None -> Prt.error n; raise Empty_exception
      | Some(cr) -> cr
    )
  in
  let new_invs, new_relations =
    List.map crules ~f:(tabular_expans ~cinv)
    |> List.concat
    |> List.unzip
  in
  let cinvs = InvLib.add_many (List.concat new_invs) in
  cinvs, fix_relations_with_cinvs cinvs new_relations

let read_res_cache cinvs =
  let cinvs' = Storage.get (!protocol_name) "cinvs" cinvs (List.t_of_sexp concrete_prop_of_sexp) in
  let inv_cinv_pairs =
    let default = List.map cinvs ~f:(fun cinv -> Tuple2.create (concrete_prop_2_form cinv) cinv) in
    let convertor = List.t_of_sexp (Tuple2.t_of_sexp formula_of_sexp concrete_prop_of_sexp) in
    let tuple2s = Storage.get (!protocol_name) "invlib" default convertor in
    List.map tuple2s ~f:(fun t -> Tuple2.get1 t, Tuple2.get2 t)
  in
  let relations = Storage.get_many (!protocol_name) "relations" [] t_of_sexp in
  InvLib.pairs := inv_cinv_pairs;
  InvLib.index := List.length inv_cinv_pairs;
  (cinvs', relations)

let write_res_cache cinvs new_relations =
  let tuple2s = List.map (!InvLib.pairs) ~f:(fun (f, cinv) -> Tuple2.create f cinv) in
  let convertor = List.sexp_of_t (Tuple2.sexp_of_t sexp_of_formula sexp_of_concrete_prop) in
  Storage.replace (!protocol_name) "cinvs" cinvs (List.sexp_of_t sexp_of_concrete_prop);
  Storage.replace (!protocol_name) "invlib" tuple2s convertor;
  Storage.add_many (!protocol_name) "relations" new_relations sexp_of_t;;

(* Find new inv and relations with concrete rules and a concrete invariant *)
let tabular_rules_cinvs rname_paraminfo_pairs cinvs =
  let rec wrapper cinvs relations =
    match cinvs with
    | [] -> (InvLib.get_all_cinvs (), relations)
    | cinv::cinvs' ->
      let (new_cinvs, new_relations) = get_res_of_cinv cinv rname_paraminfo_pairs in
      let cinvs'' = cinvs'@new_cinvs in
      write_res_cache new_cinvs new_relations;
      wrapper cinvs'' (relations@new_relations)
  in
  let cinvs, relations = read_res_cache cinvs in
  Prt.warning ("initial invs:\n"^String.concat ~sep:"\n" (
    List.map cinvs ~f:(fun cinv -> ToStr.Smv.form_act (concrete_prop_2_form cinv))
  ));
  wrapper cinvs relations



let simplify_prop property =
  let Prop(_, pds, f) = property in
  let orList_items =
    if List.length pds > 0 then
      let ps = cart_product_with_paramfix pds (!type_defs) in
      List.map ps ~f:(fun p -> simplify (neg (apply_form f ~p)))
    else begin
      [simplify (neg f)]
    end
  in
  orList_items
  |> List.map ~f:(fun form -> match form with | OrList(fl) -> fl | _ -> [form])
  |> List.concat
  |> List.filter ~f:(fun x -> match x with | Miracle -> false | _ -> true)
  |> List.dedup ~compare:symmetry_form

let result_to_str (cinvs, relations) =
  let invs_str =
    cinvs
    |> List.map ~f:concrete_prop_2_form
    |> List.map ~f:simplify
    |> List.map ~f:ToStr.Smv.form_act
  in
  let relations_str = List.map relations ~f:to_str in
  String.concat ~sep:"\n" (relations_str@invs_str)

(** Find invs and causal relations of a protocol

    @param protocol the protocol
    @param prop_params property parameters given
    @return causal relation table
*)
let find ?(smv="") ?(smv_bmc="") ?(murphi="") protocol =
  let {name; types; vardefs; init=_init; rules; properties} = Loach.Trans.act ~loach:protocol in
  let _smt_context = Smt.set_context name (ToStr.Smt2.context_of ~types ~vardefs) in
  let _mu_context = Murphi.set_context name murphi in
  let _smv_bmc_context =
    if smv_bmc = "" then
      SmvBmc.set_context name (Loach.ToSmv.protocol_act ~limit_param:false protocol)
    else begin SmvBmc.set_context name smv_bmc end
  in
  let _smv_context =
    if smv = "" then Smv.set_context name (Loach.ToSmv.protocol_act protocol)
    else begin Smv.set_context name smv end
  in
  (type_defs := types; protocol_name := name);
  let cinvs =
    let invs = List.concat (List.map properties ~f:simplify_prop) in
    let indice = up_to (List.length invs) in
    List.map2_exn invs indice ~f:(fun f id -> form_2_concreate_prop ~id f)
  in
  let get_rulename_param_pair r =
    let Paramecium.Rule(rname, paramdefs, _, _) = r in
    let ps = cart_product_with_paramfix paramdefs (!type_defs) in
    rule_2_concrete r ps;
    (rname, paramdefs)
  in
  let rname_paraminfo_pairs = List.map rules ~f:get_rulename_param_pair in
  let result = tabular_rules_cinvs rname_paraminfo_pairs cinvs in
  printf "%s\n" (result_to_str result); result
