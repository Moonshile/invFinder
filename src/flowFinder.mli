

open Core.Std
open Paramecium

type flowpath =
  | FlowPath of string * string * formula

val bfs : formula -> formula -> rule list ->
  (string, formula * formula list * string list * flowpath list) Hashtbl.t
