
open Core.Std
open Utils
open Structure
open Extend

let statement_act s ~types =
  let no_for = eliminate_for s ~types in
  let no_quant = eliminate_quant no_for ~types in
  let pairs = flatten_exec no_quant in
  parallel (List.map pairs ~f:(fun (v, e) -> assign v e))

let rule_act r ~types =
  let rule_insts = rule_to_insts r ~types in
  List.filter_map rule_insts ~f:(fun (Rule(n, pds, g, s)) ->
    print_endline (sprintf "rule: %s" n);
    let g' = eliminate_quant_in_form g ~types in
    if Formula.is_tautology (neg g') then
      None
    else
      let s' = statement_act s ~types in
      Some(rule n pds g' s')
  )

let property_act (Prop(name, pds, form)) ~types =
  prop name pds (eliminate_quant_in_form form ~types)

let protocol_act {name; types; vardefs; init; rules; properties} =
  print_endline "========== Start to preprocess ==========";
  { 
    name = name;
    types = types;
    vardefs = vardefs;
    init = statement_act init ~types;
    rules = List.concat (List.map rules ~f:(rule_act ~types));
    properties = List.map properties ~f:(property_act ~types)
  }




