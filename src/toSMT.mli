
open Structure

val context_of : types:typedef list -> vardefs:vardef list -> string
val form_of : formula -> string

val act : types:typedef list -> vardefs:vardef list -> formula -> string
