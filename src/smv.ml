(** Check a invariant with NuSMV

    @author Yongjian Li <lyj238@gmail.com>
    @author Kaiqiang Duan <duankq@ios.ac.cn>
*)

open Utils

open Core.Std

(* Raises when there are some errors in the NuSMV code *)
exception Protocol_name_not_set

let protocol_name = ref ""

let table = Hashtbl.create ~hashable:String.hashable ()

let set_context name smv_file_content =
  protocol_name := name;
  let _res = Client.Smv.compute_reachable name smv_file_content in
  let diameter = ref 0 in
  while !diameter = 0 do
    Unix.sleep 1;
    diameter := Client.Smv.query_reachable name;
  done;
  !diameter


(** Judge if a given invariant is true invariant

    @param quiet true (default) to prevent to print output of smt solver to screen
    @param inv the inv to be judged
    @return true if is true invariant else false
*)
let is_inv ?(quiet=true) inv =
  match Hashtbl.find table inv with
  | Some (r) -> r
  | None -> 
    if (!protocol_name) = "" then raise Protocol_name_not_set
    else begin
      let r = Client.Smv.check_inv (!protocol_name) inv in
      (Hashtbl.replace table ~key:inv ~data:r); r
    end
