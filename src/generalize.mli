(** Generalize a concrete formula based on Paramecium to parameterized format

    @author Yongjian Li <lyj238@gmail.com>
    @author Kaiqiang Duan <duankq@ios.ac.cn>
*)

open Paramecium

open Core.Std

(** Convert formula *)
val form_act : formula -> paramdef list * paramref list * formula
