
open Core.Std

(*------------------------------ Types ---------------------------------*)

(** Constants *)
type const =
  | Intc of int
  | Strc of string
  | Boolc of bool
with sexp

val intc : int -> const
val strc : string -> const
val boolc : bool -> const

(** Convert a int list to const list *)
val int_consts : int list -> const list
(** Convert a string list to const list *)
val str_consts : string list -> const list
(** Convert a boolean list to const list *)
val bool_consts : bool list -> const list

(** Basic types available, including integers and enumerations.
    Types are defined by their names and range.
*)
type typedef =
  | Enum of string * const list
with sexp

val enum : string -> const list -> typedef

(** Parameter definitions
    + paramdef, name and typename
*)
type paramdef =
  | Paramdef of string * string
with sexp

val paramdef : string -> string -> paramdef

(** Parameter references
    + Paramref, var name
    + Paramfix, var name, typename, value
*)
type paramref =
  | Paramref of string
  | Paramfix of string * string * const
with sexp

val paramref : string -> paramref
val paramfix : string -> string -> const -> paramref

(** Variable definitions, each with its name and name of its type
    + Array var: name, param definitions, type name
*)
type vardef =
  | Arrdef of (string * paramdef list) list * string
with sexp

val arrdef : (string * paramdef list) list -> string -> vardef

(** Record definition *)
val record_def : string -> paramdef list-> vardef list -> vardef list

(** Variable reference *)
type var =
  | Arr of (string * paramref list) list
with sexp

val arr : (string * paramref list) list -> var

(** Global variable *)
val global : string -> var

(** Record *)
val record : var list -> var

(** Represents expressions, including
    + Constants
    + Variable references
    + Parameter
    + Ite exp
    + UIPFun: Uninterpreted function, such as + - * /
*)
type exp =
  | Const of const
  | Var of var
  | Param of paramref
  | Ite of formula * exp * exp
  | UIPFun of string * exp list
(** Boolean expressions, including
    + Boolean constants, Chaos as True, Miracle as false
    + Equation expression
    + Other basic logical operations, including negation,
      conjuction, disjuction, and implication
    + Uninterpreted predications, such as > >= < <=
*)
and formula =
  | Chaos
  | Miracle
  | Eqn of exp * exp
  | UIPPred of string * exp list
  | Neg of formula
  | AndList of formula list
  | OrList of formula list
  | Imply of formula * formula
  | ForallFormula of paramdef list * formula
  | ExistFormula of paramdef list * formula
with sexp

val const : const -> exp
val var : var -> exp
val param : paramref -> exp
val ite : formula -> exp -> exp -> exp
val uipFun : string -> exp list -> exp

val chaos : formula
val miracle : formula
val eqn : exp -> exp -> formula
val uipPred : string -> exp list -> formula
val neg : formula -> formula
val andList : formula list -> formula
val orList : formula list -> formula
val imply : formula -> formula -> formula
(** Forall formula *)
val forallFormula : paramdef list -> formula -> formula
(** Exist formula *)
val existFormula : paramdef list -> formula -> formula

(** Assignment statements *)
type statement =
  | Assign of var * exp
  | Parallel of statement list
  | IfStatement of formula * statement
  | IfelseStatement of formula * statement * statement
  | ForStatement of statement * paramdef list
with sexp

val assign : var -> exp -> statement
val parallel : statement list -> statement
val ifStatement : formula -> statement -> statement
val ifelseStatement : formula -> statement -> statement -> statement
val forStatement : statement -> paramdef list -> statement

(** Represents rules which consists of guard and assignments
    + Rule: name, parameters, guard, assignments
*)
type rule = 
  | Rule of string * paramdef list * formula * statement
with sexp

val rule : string -> paramdef list -> formula -> statement -> rule

(** Represents properties
    + Prop: name, parameters, formula
*)
type prop =
  | Prop of string * paramdef list * formula
with sexp

val prop : string -> paramdef list -> formula -> prop

(** Represents the whole protocol *)
type protocol = {
  name: string;
  types: typedef list;
  vardefs: vardef list;
  init: statement;
  rules: rule list;
  properties: prop list;
}
with sexp





exception Unmatched_parameters
exception Unexhausted_inst





val name2type : tname:string -> types:typedef list -> const list
val cart_product : paramdef list -> typedef list -> const list list
val cart_product_with_name : paramdef list -> typedef list -> (string * const) list list
val cart_product_with_paramfix : paramdef list -> typedef list -> paramref list list
val name_of_param : paramref -> string
val set_param_name : paramref -> string -> paramref
val typename_of_paramfix : paramref -> string
val find_paramfix : paramref list -> string -> paramref option
val find_paramdef : paramdef list -> string -> paramdef option





val attach : string -> const -> string
val attach_list : string -> const list -> string
val apply_paramref : paramref -> p:paramref list -> paramref
val apply_array : var -> p:paramref list -> var
val apply_exp : exp -> p:paramref list -> exp
val apply_form : formula -> p:paramref list -> formula
val apply_statement : statement -> p:paramref list -> statement
val name_match : paramref list -> paramdef list -> bool
val apply_rule : rule -> p:paramref list -> rule
val apply_prop : prop -> p:paramref list -> prop
val rule_to_insts : rule -> types:typedef list -> rule list
val prop_to_insts : prop -> types:typedef list -> prop list





module Equal :
  sig
    val in_paramref : paramref -> paramref -> bool
    val in_var : var -> var -> bool
    val in_exp : exp -> exp -> bool
    val in_form : formula -> formula -> bool
  end

module Vars :
  sig
    val of_exp : exp -> var list
    val of_form : formula -> var list
    val of_statement : statement -> var list
    val of_rule : rule -> var list
  end

module VarNamesWithParam :
  sig
    val of_exp : of_var:(var -> String.Set.t) -> exp -> String.Set.t
    val of_form : of_var:(var -> String.Set.t) -> formula -> String.Set.t
    val of_statement : of_var:(var -> String.Set.t) -> statement -> String.Set.t
    val of_rule : of_var:(var -> String.Set.t) -> rule -> String.Set.t
  end







val eliminate_for : statement -> types:typedef list -> statement
val eliminate_quant_in_exp : exp -> types:typedef list -> exp
val eliminate_quant_in_form : formula -> types:typedef list -> formula
val eliminate_quant : statement -> types:typedef list -> statement
val eliminate_ifelse_wrapper : statement -> (var * exp) list
val eliminate_ifelse : statement -> statement
val exec_exp : exp -> pairs:(var * exp) list -> exp
val exec_formula : formula -> pairs:(var * exp) list -> formula
val exec_sequence : (var * exp) list -> (var * exp) list
val flatten_exec : vars:var list -> statement -> (var * exp) list
val return : var -> statement -> types:typedef list -> exp
val read_param : var -> var list -> pds:paramdef list -> types:typedef list -> exp
val write_param : var -> var list -> exp -> pds:paramdef list -> statement






