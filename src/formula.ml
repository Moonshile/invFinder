
open Core.Std
open Utils
open Structure


let is_tautology form =
  not (Smt.is_satisfiable (ToSMT.form_of (neg form)))

let is_satisfiable form =
  Smt.is_satisfiable (ToSMT.form_of form)


let rec eliminate_imply_neg ?(eli_eqn=false)  form =
  match form with
  | Chaos
  | Miracle
  | Eqn(_)
  | UIPPred(_) -> form
  | Neg(Chaos) -> miracle
  | Neg(Miracle) -> chaos
  | Neg(Eqn(Const(Boolc(true)), e1))
  | Neg(Eqn(e1, Const(Boolc(true)))) ->
    if eli_eqn then eqn e1 (Const(Boolc(false))) else begin form end
  | Neg(Eqn(Const(Boolc(false)), e1))
  | Neg(Eqn(e1, Const(Boolc(false)))) ->
    if eli_eqn then eqn e1 (Const(Boolc(true))) else begin form end
  | Neg(Eqn(_))
  | Neg(UIPPred(_)) -> form
  | Neg(Neg(f)) -> eliminate_imply_neg ~eli_eqn f
  | Neg(AndList(fl)) -> eliminate_imply_neg ~eli_eqn (orList (List.map fl ~f:neg))
  | Neg(OrList(fl)) -> eliminate_imply_neg ~eli_eqn (andList (List.map fl ~f:neg))
  | Neg(Imply(f1, f2)) -> eliminate_imply_neg ~eli_eqn (andList [f1; neg f2])
  | AndList(fl) -> andList (List.map fl ~f:(eliminate_imply_neg ~eli_eqn))
  | OrList(fl) -> orList (List.map fl ~f:(eliminate_imply_neg ~eli_eqn))
  | Imply(f1, f2) -> eliminate_imply_neg ~eli_eqn (orList [neg f1; f2])
  | Neg(ForallFormula(_))
  | Neg(ExistFormula(_))
  | ForallFormula(_)
  | ExistFormula(_) -> raise Empty_exception

(** Cast a formula to a list of formulae with and relation between them *)
let flat_and_to_list form =
  let no_imply_neg = eliminate_imply_neg form in
  let rec wrapper form =
    match form with
    | Chaos
    | Miracle
    | Eqn(_)
    | Neg(Eqn(_))
    | UIPPred(_) -> [form]
    | AndList([]) -> [chaos]
    | AndList([f]) -> [f]
    | AndList(fl) -> List.concat (List.map fl ~f:wrapper)
    | OrList([]) -> [miracle]
    | OrList([f]) -> [f]
    | OrList(fl) -> [form]
    | Neg(_)
    | Imply(_)
    | ForallFormula(_)
    | ExistFormula(_) -> raise Empty_exception
  in
  wrapper no_imply_neg

(** For andList, flat its all components,
    for others, flat to a single list
*)
let flat_to_andList form =
  andList (flat_and_to_list form)
