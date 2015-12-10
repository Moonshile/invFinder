
open Core.Std
open Structure

val eliminate_for : statement -> types:typedef list -> statement
val eliminate_quant_in_exp : exp -> types:typedef list -> exp
val eliminate_quant_in_form : formula -> types:typedef list -> formula
val eliminate_quant : statement -> types:typedef list -> statement
val eliminate_ifelse_wrapper : statement -> (var * exp) list
val eliminate_ifelse : statement -> statement

val exec_exp : exp -> pairs:(var * exp) list -> exp
val exec_formula : formula -> pairs:(var * exp) list -> formula
(*val exec_sequence : (var * exp) list -> (var * exp) list*)
val flatten_exec : statement -> (var * exp) list

val return : var -> statement -> types:typedef list -> exp
val read_param : var -> var list -> pds:paramdef list -> types:typedef list -> exp
val write_param : var -> var list -> exp -> pds:paramdef list -> statement


