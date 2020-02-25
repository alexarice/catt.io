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

let is_bubble pd =
  tc_pd_src pd >>= fun pd_src ->
  tc_pd_tgt pd >>= fun pd_tgt ->
  tc_lift (is_disc_pd pd_src >>== fun var1 ->
           is_disc_pd pd_tgt >>== fun var2 ->
           Succeed (var1, var2))

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
           (match assoc_opt x (combine pd args) with
           | Some y -> tc_ok y
           | None -> tc_fail "assoc failed")
     )

let rec sub_into_type x y ty =
  match ty with
  | ObjT -> ObjT
  | ArrT (ty', VarT a, VarT b) ->
     ArrT (sub_into_type x y ty', VarT (if a = x then y else a), VarT (if b = x then y else b))
  | other -> other

let rec filterPd pda x y =
  match pda with
  | [] -> []
  | ((id, ty), a) :: xs ->
     if id = x then filterPd xs x y else
       ((id, sub_into_type x y ty), a) :: filterPd xs x y

let rec split xs =
  match xs with
  | [] -> ([], [])
  | (y1, y2) :: ys ->
     let (ys1, ys2) = split ys in
     (y1 :: ys1, y2 :: ys2)

let insertPd z pd2a =
  match z with
  | (_, _, []) -> Fail "pasting diagram not big enough"
  | (_, xs, tgt :: ys) ->
     let res = (hd pd2a, xs, tgt :: tl pd2a @ ys) in
     Succeed (split (zipper_close res))

let rec merge_pd dim z pd2 args' =
  let ty = app_zip_head_ty z in
  let pd2a = combine pd2 args' in
  tc_lift (zipper_open pd2a) >>= fun z2 ->
  if dim_of ty < dim then
    tc_fail "merging dimension too low" else
    (match ty with
     | ArrT (_, VarT x, VarT y) ->
        is_bubble pd2 >>= fun ((s1, _), (s2, _)) ->
        tc_lift
          (app_zip_scan_back x z >>== fun zx ->
           app_zip_scan_back s1 z2 >>== fun z2s1 ->
           get_sub_list zx z2s1 y s2) >>= fun xs ->
        let pd2a' = fold_right (fun (c, d) p -> filterPd p c d) xs pd2a in
        tc_lift (insertPd z pd2a') >>= fun (newpd, newargs) ->
        tc_check_pd newpd >>= fun _ ->
        tc_ok (newpd, newargs)
     | _ -> tc_fail "bad pasting diagram")

and get_sub_list zx z2a y b =
  Printf.printf "got here too\n";
  let ty1 = app_zip_head_ty zx in
  let ty2 = app_zip_head_ty z2a in
  match (ty1, ty2) with
  | (ObjT, ObjT) ->
     Succeed ((app_zip_head_id z2a, app_zip_head_id zx) :: (b, y) :: [])
  | (ArrT (_, VarT c, VarT d), ArrT (_, VarT e, VarT f)) ->
     app_zip_scan_back c zx >>== fun zc ->
     app_zip_scan_back e z2a >>== fun z2e ->
     get_sub_list zc z2e d f >>== fun xs ->
     Succeed ((app_zip_head_id z2a, app_zip_head_id zx) :: (b, y) :: xs)
  | _ -> Fail "oh no"

let rec try_all xs =
  match xs with
  | [] -> tc_fail "No success"
  | y :: ys ->
     tc_try_2 y (fun x -> tc_ok x) (fun _ -> try_all ys)

let try_arg ty dim z (* pd ty args1 ((id, _), arg) *) =
  match app_zip_head_tm z with
  | VarT _ -> tc_fail ""
  | DefAppT _ -> tc_fail ""
  | CellAppT (ct, args) ->
     is_nice_comp ct >>= fun _ ->
     (match ct with
      | CohT _ -> tc_fail ""
      | CompT (pd2, _) ->
         merge_pd dim z pd2 args >>= fun (newpd, newargs) ->
         tc_ok (CellAppT ((CompT (newpd, ty)), newargs))
     )

let bubble_pop tm =
  match tm with
  | VarT _ -> tc_fail "Not a composition"
  | DefAppT _ -> tc_fail "can't normalize a def"
  | CellAppT (ct, args) ->
     is_nice_comp ct >>= fun _ ->
     (match ct with
      | CohT _ -> tc_fail "bubble_pop does not normalize coherences"
      | CompT (pd, ty) ->
         tc_lift (get_all_zippers (combine pd args)) >>= fun zs ->
         try_all (map (try_arg ty (dim_of_pd pd)) zs)
     )

(* let try_wall pd args (id, _) =
 *
 * let wall_destruction tm =
 *   match tm with
 *   | VarT _ -> tc_fail "Not a composition"
 *   | DefAppT _ -> tc_fail "can't normalize a def"
 *   | CellAppT (ct, args) ->
 *      is_nice_comp ct >>= fun _ ->
 *      (match ct with
 *       | CohT _ -> tc_fail "wall_destruction does not normalize coherences"
 *       | CompT (pd, _) ->
 *          try_all (map (try_wall pd args) pd)
 *      ) *)


let rec trans r tm =
  r tm >>= fun tm' ->
  trans' r tm'

and trans' r tm =
  tc_try_2 (r tm)
    (fun tm' -> trans' r tm')
    (fun _ -> tc_ok tm)

let ( >+> ) r1 r2 tm =
  tc_try_2 (r1 tm)
    (fun tm' -> tc_ok tm')
    (fun _ -> r2 tm)

let tc_normalize_simpson tm =
  trans' (tc_normalize_disk >+> bubble_pop) tm
