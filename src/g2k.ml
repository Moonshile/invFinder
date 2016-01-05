
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _I = strc "I"
let _S = strc "S"
let _E = strc "E"
let _Empty = strc "Empty"
let _ReqS = strc "ReqS"
let _ReqE = strc "ReqE"
let _Inv = strc "Inv"
let _InvAck = strc "InvAck"
let _GntS = strc "GntS"
let _GntE = strc "GntE"
let _True = boolc true
let _False = boolc false

let types = [
  enum "CACHE_STATE" [_I; _S; _E];
  enum "MSG_CMD" [_Empty; _ReqS; _ReqE; _Inv; _InvAck; _GntS; _GntE];
  enum "NODE" (int_consts [1; 2]);
  enum "DATA" (int_consts [1; 2]);
  enum "boolean" [_True; _False];
]

let _CACHE = List.concat [
  [arrdef [("State", [])] "CACHE_STATE"];
  [arrdef [("Data", [])] "DATA"]
]

let _MSG = List.concat [
  [arrdef [("Cmd", [])] "MSG_CMD"];
  [arrdef [("Data", [])] "DATA"]
]

let vardefs = List.concat [
  record_def "Cache" [paramdef "i0" "NODE"] _CACHE;
  record_def "Chan1" [paramdef "i1" "NODE"] _MSG;
  record_def "Chan2" [paramdef "i2" "NODE"] _MSG;
  record_def "Chan3" [paramdef "i3" "NODE"] _MSG;
  [arrdef [("ShrSet", [paramdef "i4" "NODE"])] "boolean"];
  [arrdef [("InvSet", [paramdef "i5" "NODE"])] "boolean"];
  [arrdef [("ExGntd", [])] "boolean"];
  [arrdef [("CurCmd", [])] "MSG_CMD"];
  [arrdef [("CurPtr", [])] "NODE"];
  [arrdef [("MemData", [])] "DATA"];
  [arrdef [("AuxData", [])] "DATA"]
]

let init = (parallel [(forStatement (parallel [(assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Chan1", [paramref "i"])]; global "Data"]) (param (paramfix "d" "DATA" (intc 1)))); (assign (record [arr [("Chan2", [paramref "i"])]; global "Data"]) (param (paramfix "d" "DATA" (intc 1)))); (assign (record [arr [("Chan3", [paramref "i"])]; global "Data"]) (param (paramfix "d" "DATA" (intc 1)))); (assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _I)); (assign (record [arr [("Cache", [paramref "i"])]; global "Data"]) (param (paramfix "d" "DATA" (intc 1)))); (assign (arr [("ShrSet", [paramref "i"])]) (const (boolc false))); (assign (arr [("InvSet", [paramref "i"])]) (const (boolc false)))]) [paramdef "i" "NODE"]); (assign (global "CurCmd") (const _Empty)); (assign (global "ExGntd") (const (boolc false))); (assign (global "MemData") (param (paramfix "d" "DATA" (intc 1)))); (assign (global "AuxData") (param (paramfix "d" "DATA" (intc 1))))])

let n_SendReqS =
  let name = "n_SendReqS" in
  let params = [paramdef "j" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _I)); (eqn (var (record [arr [("Chan1", [paramref "j"])]; global "Cmd"])) (const _Empty))]) in
  let statement = (assign (record [arr [("Chan1", [paramref "j"])]; global "Cmd"]) (const _ReqS)) in
  rule name params formula statement

let n_SendReqEI =
  let name = "n_SendReqEI" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I)); (eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _Empty))]) in
  let statement = (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _ReqE)) in
  rule name params formula statement

let n_SendReqES =
  let name = "n_SendReqES" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _S)); (eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _Empty))]) in
  let statement = (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _ReqE)) in
  rule name params formula statement

let n_RecvReq =
  let name = "n_RecvReq" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (global "CurCmd")) (const _Empty)); (neg (eqn (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"])) (const _Empty)))]) in
  let statement = (parallel [(assign (global "CurCmd") (var (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]))); (assign (record [arr [("Chan1", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (global "CurPtr") (param (paramref "i"))); (forStatement (assign (arr [("InvSet", [paramref "j"])]) (var (arr [("ShrSet", [paramref "j"])]))) [paramdef "j" "NODE"])]) in
  rule name params formula statement

let n_SendInvE =
  let name = "n_SendInvE" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(eqn (var (global "CurCmd")) (const _ReqE)); (eqn (var (arr [("InvSet", [paramref "i"])])) (const _True))]); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Inv)); (assign (arr [("InvSet", [paramref "i"])]) (const (boolc false)))]) in
  rule name params formula statement

let n_SendInvS =
  let name = "n_SendInvS" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (global "ExGntd")) (const _True))]); (eqn (var (arr [("InvSet", [paramref "i"])])) (const _True))]); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Inv)); (assign (arr [("InvSet", [paramref "i"])]) (const (boolc false)))]) in
  rule name params formula statement

let n_SendInvAck =
  let name = "n_SendInvAck" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Inv)); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _Empty))]) in
  let statement = (parallel [(assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _InvAck)); (ifStatement (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (assign (record [arr [("Chan3", [paramref "i"])]; global "Data"]) (var (record [arr [("Cache", [paramref "i"])]; global "Data"])))); (assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _I))]) in
  rule name params formula statement

let n_RecvInvAck =
  let name = "n_RecvInvAck" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(neg (eqn (var (global "CurCmd")) (const _Empty))); (eqn (var (record [arr [("Chan3", [paramref "i"])]; global "Cmd"])) (const _InvAck))]) in
  let statement = (parallel [(assign (arr [("ShrSet", [paramref "i"])]) (const (boolc false))); (ifStatement (eqn (var (global "ExGntd")) (const (boolc true))) (parallel [(assign (global "ExGntd") (const (boolc false))); (assign (global "MemData") (var (record [arr [("Chan3", [paramref "i"])]; global "Data"])))])); (assign (record [arr [("Chan3", [paramref "i"])]; global "Cmd"]) (const _Empty))]) in
  rule name params formula statement

let n_SendGntS =
  let name = "n_SendGntS" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (global "CurCmd")) (const _ReqS)); (eqn (var (global "CurPtr")) (param (paramref "i")))]); (eqn (var (global "ExGntd")) (const _False))]); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))]) in
  let statement = (parallel [(assign (arr [("ShrSet", [paramref "i"])]) (const (boolc true))); (assign (global "CurCmd") (const _Empty)); (assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _GntS)); (assign (record [arr [("Chan2", [paramref "i"])]; global "Data"]) (var (global "MemData")))]) in
  rule name params formula statement

let n_SendGntE =
  let name = "n_SendGntE" in
  let params = [paramdef "i" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (global "CurCmd")) (const _ReqE)); (eqn (var (global "CurPtr")) (param (paramref "i")))]); (eqn (var (global "ExGntd")) (const _False))]); (forallFormula [paramdef "j" "NODE"] (eqn (var (arr [("ShrSet", [paramref "j"])])) (const (boolc false))))]); (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _Empty))]) in
  let statement = (parallel [(assign (arr [("ShrSet", [paramref "i"])]) (const (boolc true))); (assign (global "CurCmd") (const _Empty)); (assign (global "ExGntd") (const (boolc true))); (assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _GntE)); (assign (record [arr [("Chan2", [paramref "i"])]; global "Data"]) (var (global "MemData")))]) in
  rule name params formula statement

let n_RecvGntS =
  let name = "n_RecvGntS" in
  let params = [paramdef "i" "NODE"] in
  let formula = (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntS)) in
  let statement = (parallel [(assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _S)); (assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Cache", [paramref "i"])]; global "Data"]) (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])))]) in
  rule name params formula statement

let n_RecvGntE =
  let name = "n_RecvGntE" in
  let params = [paramdef "i" "NODE"] in
  let formula = (eqn (var (record [arr [("Chan2", [paramref "i"])]; global "Cmd"])) (const _GntE)) in
  let statement = (parallel [(assign (record [arr [("Cache", [paramref "i"])]; global "State"]) (const _E)); (assign (record [arr [("Chan2", [paramref "i"])]; global "Cmd"]) (const _Empty)); (assign (record [arr [("Cache", [paramref "i"])]; global "Data"]) (var (record [arr [("Chan2", [paramref "i"])]; global "Data"])))]) in
  rule name params formula statement

let n_Store =
  let name = "n_Store" in
  let params = [paramdef "i" "NODE"; paramdef "d" "DATA"] in
  let formula = (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) in
  let statement = (parallel [(assign (record [arr [("Cache", [paramref "i"])]; global "Data"]) (param (paramref "d"))); (assign (global "AuxData") (param (paramref "d")))]) in
  rule name params formula statement

let rules = [n_SendReqS; n_SendReqEI; n_SendReqES; n_RecvReq; n_SendInvE; n_SendInvS; n_SendInvAck; n_RecvInvAck; n_SendGntS; n_SendGntE; n_RecvGntS; n_RecvGntE; n_Store]

let n_CntrlProp =
  let name = "n_CntrlProp" in
  let params = [paramdef "i" "NODE"; paramdef "j" "NODE"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _E)) (neg (eqn (var (record [arr [("Cache", [paramref "j"])]; global "State"])) (const _E))))) in
  prop name params formula

let n_DataProp =
  let name = "n_DataProp" in
  let params = [] in
  let formula = (andList [(imply (eqn (var (global "ExGntd")) (const (boolc false))) (eqn (var (global "MemData")) (var (global "AuxData")))); (forallFormula [paramdef "i" "NODE"] (imply (neg (eqn (var (record [arr [("Cache", [paramref "i"])]; global "State"])) (const _I))) (eqn (var (record [arr [("Cache", [paramref "i"])]; global "Data"])) (var (global "AuxData")))))]) in
  prop name params formula

let properties = [n_CntrlProp; n_DataProp]


let protocol = {
  name = "n_g2k";
  types;
  vardefs;
  init;
  rules;
  properties;
}






open Paramecium

let () = run_with_cmdline (fun () ->
  let name = "n_g2k" in
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
  let endF = eqn (var (record [arr [("Cache", [paramfix "i" "NODE" (intc 1)])]; global "State"])) (const _E) in
  let startF = eqn (var (record [arr [("Cache", [paramfix "i" "NODE" (intc 1)])]; global "State"])) (const _I) in
  let core_vars = [
    record [arr [("Cache", [paramfix "i" "NODE" (intc 1)])]; global "State"];
    record [arr [("Chan1", [paramfix "i" "NODE" (intc 1)])]; global "Cmd"];
  ] in
  let table = FlowFinder.bfs core_vars startF endF rule_insts in
  let dot_str = FlowFinder.table_to_dot table endF in
  Out_channel.write_all (name^".dot") dot_str
)
