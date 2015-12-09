
open Core.Std
open Utils
open Structure

let statement_act s ~types =
  let no_for = eliminate_for s ~types in
  let no_quant = eliminate_quant no_for ~types in
  let pairs = flatten_exec no_quant in
  print_endline (sprintf "res count : %d" (List.length pairs));
  parallel (List.map pairs ~f:(fun (v, e) -> assign v e))

let rule_act (Rule(name, pds, form, s)) ~types =
  print_endline (sprintf "rule: %s" name);
  rule name pds (eliminate_quant_in_form form ~types) (statement_act s ~types)

let property_act (Prop(name, pds, form)) ~types =
  prop name pds (eliminate_quant_in_form form ~types)

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




