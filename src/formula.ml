
open Core.Std
open Utils
open Structure


let is_tautology form =
  not (Smt.is_satisfiable (ToSMT.form_of (neg form)))

let is_satisfiable form =
  Smt.is_satisfiable (ToSMT.form_of form)
