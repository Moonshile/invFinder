
open Structure

val const_act : const -> string
val type_act : types:typedef list -> string -> string
val paramref_act : paramref -> string
val vardef_act : types:typedef list -> vardef -> string
val var_act : var -> string
val exp_act : exp -> string
val form_act : formula -> string
val statement_act : ?is_init:bool -> statement -> string -> string
val init_act : statement -> string
val rule_act : rule -> string * string
val prop_act : prop -> string
val protocol_act : protocol -> string
