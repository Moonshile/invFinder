(** For find invariants and causal relations based on Paramecium

    @author Yongjian Li <lyj238@gmail.com>
    @author Kaiqiang Duan <duankq@ios.ac.cn>
*)

open Core.Std
open Paramecium

(** Raised when parallel statements haven't been cast to assign list *)
exception Unexhausted_flat_parallel

(** Raised when circular parallel assignments detected *)
exception Circular_parallel_assign

(** Raised when require to check a inv has too many paramters *)
exception Parameter_overflow

exception Invariant_not_sat_on_init of string

(** Concrete rule

    + ConcreteRule: instantiated rule, concrete param list
    + AllRuleInst: all instances of the rule has same relation
*)
type concrete_rule =
  | ConcreteRule of string * paramref list
  | AllRuleInst of string
with sexp

val concrete_rule : rule -> paramref list -> concrete_rule
val all_rule_inst : rule -> concrete_rule

val all_rule_inst_from_name : string -> concrete_rule

(** Concrete property

    + ConcreteProp: property, concrete param list
*)
type concrete_prop =
  | ConcreteProp of prop * paramref list
with sexp

val concrete_prop : prop -> paramref list -> concrete_prop

(** Causal relations

  + InvHoldForRule1
  + InvHoldForRule2
  + InvHoldForRule3: the new concrete invariant found
*)
type relation =
  | InvHoldForRule1
  | InvHoldForRule2
  | InvHoldForRule3 of concrete_prop
with sexp

val invHoldForRule1 : relation
val invHoldForRule2 : relation
val invHoldForRule3 : concrete_prop -> relation

(** InvFinder type, i.e., causal relation table *)
type t = {
  rule: concrete_rule;
  inv: concrete_prop;
  branch: formula;
  relation: relation;
}
with sexp

val get_rname_of_crname : string -> string
val concrete_prop_2_form : concrete_prop -> Paramecium.formula
val form_2_concreate_prop : ?id:int -> ?rename:bool -> Paramecium.formula -> concrete_prop

(** Convert t to a string *)
val to_str : t -> string

(** Find invs and causal relations of a protocol

    @param protocol the protocol
    @param prop_params property parameters given
    @return a triple list: the concrete prop, new invs generated by the prop, and relations
*)
val find : ?smv_escape:(string -> string) ->
  ?smv:string -> ?smv_bmc:string -> ?murphi:string -> Loach.protocol ->
  (concrete_prop * String.Set.t) list * t list list list

