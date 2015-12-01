
open Structure

val eliminate_for : statement -> types:typedef list -> statement                                                                  
val eliminate_ifelse_wrapper : statement -> (var * exp) list
val eliminate_ifelse : statement -> statement

val exec_exp : exp -> pairs:(var * exp) list -> exp
val exec_formula : formula -> pairs:(var * exp) list -> formula
val exec_sequence : (var * exp) list -> (var * exp) list

module Act :
  sig
    val exp_act : exp -> types:typedef list -> exp
    val form_act : formula -> types:typedef list -> formula
    val statement_act : statement -> types:typedef list -> statement
    val rule_act : rule -> types:typedef list -> rule
    val property_act : prop -> types:typedef list -> prop
    val protocol_act : protocol -> protocol
  end