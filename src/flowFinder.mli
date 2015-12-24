

open Core.Std
open Paramecium

type flowpath =
  | FlowPath of string * rule * formula

val bfs : formula -> formula -> rule list -> types:Paramecium.typedef list ->
  (string, formula * flowpath list) Hashtbl.t
