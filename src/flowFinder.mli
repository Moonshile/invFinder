

open Core.Std
open Paramecium

type flowpath =
  | FlowPath of string * string * formula

val bfs : var list -> formula -> formula -> rule list ->
  (string, int * formula * formula list * string list * flowpath list) Hashtbl.t

val table_to_dot : (string, int * formula * formula list * string list * flowpath list) Hashtbl.t ->
  string
