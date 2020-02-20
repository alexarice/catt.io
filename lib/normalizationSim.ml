(*
 * Simpson term normalization
 *)

open Typecheck
open Term
open Printf

let test_comp tm =
  match tm with
  | VarT _ -> tc_ok true
  | DefAppT (id, _) ->
     tc_lookup_def id >>= fun def ->
     (match def with
     | TCCellDef _ ->
        tc_ok false
     | TCTermDef (_, _, _) ->
        tc_ok false)
  | CellAppT (_, _) ->
     tc_ok false

let tc_normalize_simpson tm =
  test_comp tm >>= fun isPureComp ->
  match isPureComp with
  | true -> printf "is pure comp\n"; tc_ok tm
  | false -> printf "not pure comp\n"; tc_ok tm
