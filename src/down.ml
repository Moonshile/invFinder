
open Core.Std
open Utils
open Structure

let types = [ 
  enum "ind_t" (int_consts [1; 2; 3; 4; 5; 6]);
  enum "val_t" (int_consts [0; 1; 2; 3; 4; 5]);
  enum "sum_t" (int_consts (up_to 31));
] 
  
let vardefs = List.concat [
  [arrdef [("a", [paramdef "i0" "ind_t"])] "val_t"];
]

let proc_Decrement dec =
  let cond = uipPred ">=" [var dec; const (Intc 1)] in
  let s = assign dec (uipFun "-" [var dec; const (Intc 1)]) in
  IfStatement(cond, s)

let func_Sum () =
  let sum = global "sum" in
  let assgn1 = assign sum (const (Intc 0)) in
  let assgn = assign sum (uipFun "+" [var sum; var (arr [("a", [paramref "i"])])]) in
  let forAssgn = forStatement assgn [paramdef "i" "ind_t"] in
  let s = parallel [assgn1; forAssgn] in
  return sum s ~types

let rule1 =
  let name = "rule1" in
  let params = [paramdef "i" "ind_t"] in
  let guard = uipPred ">" [var (arr [("a", [paramref "i"])]); const (Intc 0)] in
  let s = parallel [
    proc_Decrement (arr [("a", [paramref "i"])]);
    IfStatement(
      uipPred "<" [
        uipFun "+" [(param (paramref "i")); (const (Intc 1))];
        const (Intc 6)
      ],
      ForStatement(
        IfStatement(
          andList [
            eqn (uipFun "+" [(param (paramref "i")); (const (intc 1))]) (param (paramref "j"));
            uipPred ">" [var (arr [("a", [paramref "j"])]); const (intc 0)]
          ],
          proc_Decrement (arr [("a", [paramref "j"])])
        ),
        [paramdef "j" "ind_t"]
      )
    )
  ] in
  rule name params guard s

let rules = [rule1]

let init = 
  forStatement (assign (arr [("a", [paramref "i"])]) (const (Intc 5))) [paramdef "i" "ind_t"]

let positive_sum =
  let name = "positive_sum" in
  let params = [] in
  let formula = uipPred ">" [func_Sum (); const (intc 0)] in
  prop name params formula

let properties = [positive_sum]

let protocol = {
  name = "down";
  types;
  vardefs;
  init;
  rules;
  properties;
}



let down_str = ToSMV.protocol_act (Preprocess.protocol_act protocol) in
Out_channel.write_all "down.smv" ~data:down_str;;
