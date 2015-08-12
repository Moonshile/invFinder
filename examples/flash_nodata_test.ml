
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _CACHE_I = strc "CACHE_I"
let _CACHE_S = strc "CACHE_S"
let _CACHE_E = strc "CACHE_E"
let _NODE_None = strc "NODE_None"
let _NODE_Get = strc "NODE_Get"
let _NODE_GetX = strc "NODE_GetX"
let _UNI_None = strc "UNI_None"
let _UNI_Get = strc "UNI_Get"
let _UNI_GetX = strc "UNI_GetX"
let _UNI_Put = strc "UNI_Put"
let _UNI_PutX = strc "UNI_PutX"
let _UNI_Nak = strc "UNI_Nak"
let _INV_None = strc "INV_None"
let _INV_Inv = strc "INV_Inv"
let _INV_InvAck = strc "INV_InvAck"
let _RP_None = strc "RP_None"
let _RP_Replace = strc "RP_Replace"
let _WB_None = strc "WB_None"
let _WB_Wb = strc "WB_Wb"
let _SHWB_None = strc "SHWB_None"
let _SHWB_ShWb = strc "SHWB_ShWb"
let _SHWB_FAck = strc "SHWB_FAck"
let _NAKC_None = strc "NAKC_None"
let _NAKC_Nakc = strc "NAKC_Nakc"
let _True = boolc true
let _False = boolc false

let types = [
  enum "CACHE_STATE" [_CACHE_I; _CACHE_S; _CACHE_E];
  enum "NODE_CMD" [_NODE_None; _NODE_Get; _NODE_GetX];
  enum "UNI_CMD" [_UNI_None; _UNI_Get; _UNI_GetX; _UNI_Put; _UNI_PutX; _UNI_Nak];
  enum "INV_CMD" [_INV_None; _INV_Inv; _INV_InvAck];
  enum "RP_CMD" [_RP_None; _RP_Replace];
  enum "WB_CMD" [_WB_None; _WB_Wb];
  enum "SHWB_CMD" [_SHWB_None; _SHWB_ShWb; _SHWB_FAck];
  enum "NAKC_CMD" [_NAKC_None; _NAKC_Nakc];
  enum "NODE" (int_consts [0; 1; 2; 3; 4; 5]);
  enum "boolean" [_True; _False];
]

let _NODE_STATE = List.concat [
  [arrdef [("ProcCmd", [])] "NODE_CMD"];
  [arrdef [("InvMarked", [])] "boolean"];
  [arrdef [("CacheState", [])] "CACHE_STATE"]
]

let _DIR_STATE = List.concat [
  [arrdef [("Pending", [])] "boolean"];
  [arrdef [("Local", [])] "boolean"];
  [arrdef [("Dirty", [])] "boolean"];
  [arrdef [("HeadVld", [])] "boolean"];
  [arrdef [("HeadPtr", [])] "NODE"];
  [arrdef [("ShrVld", [])] "boolean"];
  [arrdef [("ShrSet", [paramdef "i0" "NODE"])] "boolean"];
  [arrdef [("InvSet", [paramdef "i1" "NODE"])] "boolean"]
]

let _UNI_MSG = List.concat [
  [arrdef [("Cmd", [])] "UNI_CMD"];
  [arrdef [("Proc", [])] "NODE"]
]

let _INV_MSG = List.concat [
  [arrdef [("Cmd", [])] "INV_CMD"]
]

let _RP_MSG = List.concat [
  [arrdef [("Cmd", [])] "RP_CMD"]
]

let _WB_MSG = List.concat [
  [arrdef [("Cmd", [])] "WB_CMD"];
  [arrdef [("Proc", [])] "NODE"]
]

let _SHWB_MSG = List.concat [
  [arrdef [("Cmd", [])] "SHWB_CMD"];
  [arrdef [("Proc", [])] "NODE"]
]

let _NAKC_MSG = List.concat [
  [arrdef [("Cmd", [])] "NAKC_CMD"]
]

let _STATE = List.concat [
  record_def "Proc" [paramdef "i2" "NODE"] _NODE_STATE;
  record_def "Dir" [] _DIR_STATE;
  record_def "UniMsg" [paramdef "i3" "NODE"] _UNI_MSG;
  record_def "InvMsg" [paramdef "i4" "NODE"] _INV_MSG;
  record_def "RpMsg" [paramdef "i5" "NODE"] _RP_MSG;
  record_def "WbMsg" [] _WB_MSG;
  record_def "ShWbMsg" [] _SHWB_MSG;
  record_def "NakcMsg" [] _NAKC_MSG
]

let vardefs = List.concat [
  [arrdef [("Home", [])] "NODE"];
  record_def "Sta" [] _STATE
]

let _Home = paramfix "Home" "NODE" (intc 0)

let init = (parallel [(assign (global "Home") (param (paramfix "h" "NODE" (intc 0)))); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramfix "h" "NODE" (intc 0)))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (assign (record [global "Sta"; global "WbMsg"; global "Cmd"]) (const _WB_None)); (assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_None)); (assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_None)); (forStatement (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "p"])]; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("RpMsg", [paramref "p"])]; global "Cmd"]) (const _RP_None))]) [paramdef "p" "NODE"])])

let n_PI_Local_GetX_PutX =
  let name = "n_PI_Local_GetX_PutX" in
  let params = [] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("Proc", [_Home])]; global "ProcCmd"])) (const _NODE_None)); (orList [(eqn (var (record [global "Sta"; arr [("Proc", [_Home])]; global "CacheState"])) (const _CACHE_I)); (eqn (var (record [global "Sta"; arr [("Proc", [_Home])]; global "CacheState"])) (const _CACHE_S))])]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _False))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _False))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (ifStatement (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)) (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param _Home))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"])])); (assign (record [global "Sta"; arr [("Proc", [_Home])]; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; arr [("Proc", [_Home])]; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [_Home])]; global "CacheState"]) (const _CACHE_E))]) in
  rule name params formula statement

let rules = [n_PI_Local_GetX_PutX]

let n_CacheStateProp =
  let name = "n_CacheStateProp" in
  let params = [] in
  let formula = (neg (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramfix "i" "NODE" (intc 3)])]])) (const _True)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramfix "j" "NODE" (intc 1)])]; global "Cmd"])) (const _UNI_Get))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramfix "j" "NODE" (intc 1)])]; global "Proc"])) (param (paramfix "k" "NODE" (intc 2))))])) in
  prop name params formula

let properties = [n_CacheStateProp]


let protocol = {
  name = "n_flash_nodata";
  types;
  vardefs;
  init;
  rules;
  properties;
}

let () = run_with_cmdline (fun () ->
  let cinvs, relations = find protocol 
    ~smv:(In_channel.read_all "flash_nodata.smv")
    ~murphi:(In_channel.read_all "n_flash_nodata.m") in
  ()
)

