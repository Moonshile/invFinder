(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _I = strc "I"
let _T = strc "T"
let _C = strc "C"
let _E = strc "E"
let _True = boolc true
let _False = boolc false

let types = [
  enum "state" [_I; _T; _C; _E];
  enum "client" (int_consts [1; 2]);
  enum "boolean" [_True; _False];
]



let vardefs = List.concat [
  [arrdef [("n", [paramdef "i0" "client"])] "state"];
  [arrdef [("x", [])] "boolean"]
]

let init = (parallel [(forStatement (assign (arr [("n", [paramref "i"])]) (const _I)) [paramdef "i" "client"]); (assign (global "x") (const (boolc true)))])

let n_Try =
  let name = "n_Try" in
  let params = [paramdef "i" "client"] in
  let formula = (eqn (var (arr [("n", [paramref "i"])])) (const _I)) in
  let statement = (assign (arr [("n", [paramref "i"])]) (const _T)) in
  rule name params formula statement

let n_Crit =
  let name = "n_Crit" in
  let params = [paramdef "i" "client"] in
  let formula = (andList [(eqn (var (arr [("n", [paramref "i"])])) (const _T)); (eqn (var (global "x")) (const (boolc true)))]) in
  let statement = (parallel [(assign (arr [("n", [paramref "i"])]) (const _C)); (assign (global "x") (const (boolc false)))]) in
  rule name params formula statement

let n_Exit =
  let name = "n_Exit" in
  let params = [paramdef "i" "client"] in
  let formula = (eqn (var (arr [("n", [paramref "i"])])) (const _C)) in
  let statement = (assign (arr [("n", [paramref "i"])]) (const _E)) in
  rule name params formula statement

let n_Idle =
  let name = "n_Idle" in
  let params = [paramdef "i" "client"] in
  let formula = (eqn (var (arr [("n", [paramref "i"])])) (const _E)) in
  let statement = (parallel [(assign (arr [("n", [paramref "i"])]) (const _I)); (assign (global "x") (const (boolc true)))]) in
  rule name params formula statement

let rules = [n_Try; n_Crit; n_Exit; n_Idle]

let n_coherence =
  let name = "n_coherence" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("n", [paramref "i"])])) (const _C)) (neg (eqn (var (arr [("n", [paramref "j"])])) (const _C))))) in
  prop name params formula

let properties = [n_coherence]


let protocol = {
  name = "n_mutualEx";
  types;
  vardefs;
  init;
  rules;
  properties;
}

open Paramecium

let () = run_with_cmdline (fun () ->
  let name = "n_mutualEx" in
  let protocol = preprocess_rule_guard ~loach:protocol in
  let _smt_context = Smt.set_context name (ToStr.Smt2.context_of ~types ~vardefs) in
  (*let _mu_context = Murphi.set_context name (In_channel.read_all "n_g2k.m") in*)
  let _smv_context = Smv.set_context ~escape:(fun s -> s) name (Loach.ToSmv.protocol_act protocol) in
  let protocol = Loach.Trans.act ~loach:protocol in
  let simp_inst_guard r =
    let Rule(n, p, f, s) = r in
    rule n p (simplify f) s
  in
  let {name; types; vardefs; init; rules; properties} = protocol in
  let rule_insts = List.concat (List.map rules ~f:(fun r ->
    let Rule(_, pds, _, _) = r in
    let ps = cart_product_with_paramfix pds types in
    if List.length ps = 0 then [simp_inst_guard r]
    else List.map ps ~f:(fun p -> simp_inst_guard (apply_rule r ~p))
  )) in
  let endF = eqn (var (arr [("n", [paramfix "i" "client" (intc 1)])])) (const _E) in
  let startF = eqn (var (arr [("n", [paramfix "i" "client" (intc 1)])])) (const _I) in
  let core_vars = [
    arr [("n", [paramfix "i" "client" (intc 1)])]
  ] in
  let table = FlowFinder.bfs core_vars startF endF rule_insts in
  let dot_str = FlowFinder.table_to_dot table endF in
  Out_channel.write_all (name^".dot") dot_str
)
