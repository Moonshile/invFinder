

exception Unsupported of string

val const_act : Paramecium.const -> string option
val const_to_str : Paramecium.const -> string
val type_act : Paramecium.typedef -> string option
val var_act : Paramecium.var -> string
val paramref_to_index : Paramecium.paramref -> string
val exp_act : Paramecium.exp -> string
val formula_act : Loach.formula -> string
val protocol_act : Loach.protocol -> InvFinder.concrete_prop list -> InvFinder.t list -> string
