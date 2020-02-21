(*
 * Simpson term normalization
 *)

open Typecheck
open Term
open Printf
open List

type 'a option =
  | None
  | Some of 'a

let isSome x =
  match x with
  | None -> false
  | Some _ -> true

let ( <&> ) x y =
  match x with
  | Some _ -> y
  | None -> None

let list_join =
  fold_right (fun a b -> a <&> b)

let rec test_comp_term tm =
  match tm with
  | VarT id -> tc_ok (Some ((id , ObjT) :: []))
  | DefAppT (_, _) -> tc_fail "can't normalize a def"
  | CellAppT (cell_tm, args) ->
     tc_traverse test_comp_term args >>= fun args_tested ->
     (match cell_tm with
      | CohT (_, _) ->
         tc_ok None
      | CompT (ctx, ty) ->
         test_comp_type ty >>= fun res ->
         tc_ok (list_join args_tested (if res then Some ctx else None))
     ) >>= fun term_tested ->
     tc_ok (list_join args_tested term_tested)

and test_comp_type ty =
  match ty with
  | ObjT -> tc_ok true
  | ArrT (ty, tm1, tm2) ->
     test_comp_type ty >>= fun ty_tested ->
     test_comp_term tm1 >>= fun tm1_tested ->
     test_comp_term tm2 >>= fun tm2_tested ->
     tc_ok (ty_tested && isSome (tm1_tested <&> tm2_tested))

let tc_normalize_simpson tm =
  test_comp_term tm >>= fun isPureComp ->
  match isPureComp with
  | Some ctx -> printf "is pure comp\n"; tc_ucomp ctx >>= fun (tm, _) -> tc_ok tm
  | None -> printf "not pure comp\n"; tc_ok tm
