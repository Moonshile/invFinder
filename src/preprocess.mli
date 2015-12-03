
open Structure

val exp_act : exp -> types:typedef list -> exp
val form_act : formula -> types:typedef list -> formula
val statement_act : statement -> types:typedef list -> statement
val rule_act : rule -> types:typedef list -> rule
val property_act : prop -> types:typedef list -> prop
val protocol_act : protocol -> protocol
