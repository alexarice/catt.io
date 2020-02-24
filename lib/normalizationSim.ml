(*
 * Simpson term normalization
 *)

open Typecheck
open Term
open List
open Common

let rec test_comp_term tm =
  match tm with
  | VarT id -> tc_ok (((id , ObjT) :: []))
  | DefAppT (_, _) -> tc_fail "can't normalize a def"
  | CellAppT (cell_tm, args) ->
     tc_traverse test_comp_term args >>= fun _ ->
     (match cell_tm with
      | CohT (_, _) ->
         tc_fail "Encountered Coherence"
      | CompT (ctx, ty) ->
         test_comp_type ty >>= fun _ ->
         tc_ok ctx
     )

and test_comp_type ty =
  match ty with
  | ObjT -> tc_ok ()
  | ArrT (ty, tm1, tm2) ->
     test_comp_type ty >>= fun _ ->
     test_comp_term tm1 >>= fun _ ->
     test_comp_term tm2 >>= fun _ ->
     tc_ok ()

let is_nice_comp ct =
  match ct with
  | CohT (_, _) ->
     tc_fail "Coherences are not compositions"
  | CompT (_, ty) ->
     (match ty with
      | ObjT -> tc_fail "Composition type should be an arrow"
      | x ->
         test_comp_type x
     )

let is_bubble ct =
  match ct with
  | CohT _ ->
     tc_fail "Coherence is not a bubble"
  | CompT (pd, _) ->
     tc_pd_src pd >>= fun pd_src ->
     tc_pd_tgt pd >>= fun pd_tgt ->
     tc_lift (is_disc_pd pd_src >>== fun _ -> is_disc_pd pd_tgt)

let tc_normalize_disk tm =
  match tm with
  | VarT _ -> tc_fail "Not a composition"
  | DefAppT _ -> tc_fail "can't normalize a def"
  | CellAppT (ct, args) ->
     (match ct with
      | CohT _ -> tc_fail "normalize_disk does not normalize coherences"
      | CompT (pd ,ty) ->
         tc_lift (is_disc_pd pd) >>= fun x ->
         test_comp_type ty >>= fun _ ->
         if length args != length pd then tc_fail "malformed composition" else
           tc_ok (assoc x (combine pd args))
     )

let rec trans r tm =
  tc_try_2 (r tm)
    (fun tm' -> trans r tm')
    (fun _ -> tc_ok tm)

let ( >+> ) r1 r2 tm =
  tc_try_2 (r1 tm)
    (fun tm' -> tc_ok tm')
    (fun _ -> r2 tm)

let tc_normalize_simpson tm =
  trans tc_normalize_disk tm
