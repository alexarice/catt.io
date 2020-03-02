(*
 * Simpson term normalization
 *)

open Typecheck
open Term
open List
open Common

type reduction = tc_env -> tm_term -> (string * tm_term err)

type 'a maybe = Some of 'a | Nothing

type 'a rm = tc_env -> (string list * 'a maybe)

let prepend_output (o : string list) (r : 'a rm) : 'a rm = fun env ->
  let (o2, ans) = r env in (o @ o2, ans)

let ( >>=== ) (red : 'a rm) (f : 'a -> 'b rm) : 'b rm = fun env ->
  match red env with
  | (output, Some x) -> prepend_output output (f x) env
  | (output, Nothing) -> (output, Nothing)

let rm_lift (a : 'a tcm) : 'a rm = fun env ->
  match a env with
  | Succeed x -> ([], Some x)
  | Fail s -> ([s], Nothing)

let all_lift (a : 'a err) : 'a rm =
  rm_lift (tc_lift a)

let put (s : string) : unit rm =
  fun _ -> ([s], Some ())

let rm_ok (x : 'a) : 'a rm =
  fun _ -> ([], Some x)

let rm_fail (s : string) : 'a rm =
  fun _ -> ([s], Nothing)

let rec rm_traverse (f : 'a -> 'b rm) (xs : 'a list) : 'b list rm =
  match xs with
  | [] -> rm_ok []
  | y :: ys ->
     f y >>=== fun z ->
     rm_traverse f ys >>=== fun zs ->
     rm_ok (z :: zs)

let ( <|> ) (r1 : 'a rm) (r2 : 'a rm) : 'a rm = fun env ->
  match r1 env with
  | (output, Some tm) -> (output, Some tm)
  | (output, Nothing) -> prepend_output output r2 env

let ( >+> ) (r1 : 'a -> 'b rm) (r2: 'a -> 'b rm) (tm : 'a) : 'b rm =
  r1 tm <|> r2 tm

let rec ref_trans_close (r: 'a -> 'a rm) (tm : 'a) : 'a rm = fun env ->
  match r tm env with
  | (output, Some tm') -> prepend_output output (ref_trans_close r tm') env
  | (output, Nothing) -> (output, Some tm)

let run_reduction (r : 'a -> 'b rm) (tm : 'a) : (string list * 'b) tcm = fun env ->
  match r tm env with
  | (output, Some tm') -> Succeed (output, tm')
  | (output, Nothing) -> Succeed (output, tm)

let rec test_comp_term tm =
  match tm with
  | VarT id -> rm_ok (((id , ObjT) :: []))
  | DefAppT (_, _) -> rm_fail "can't normalize a def"
  | CellAppT (cell_tm, args) ->
     rm_traverse test_comp_term args >>=== fun _ ->
     (match cell_tm with
      | CohT (_, _) ->
         rm_fail "Encountered Coherence"
      | CompT (ctx, ty) ->
         test_comp_type ty >>=== fun _ ->
         rm_ok ctx
     )

and test_comp_type ty =
  match ty with
  | ObjT -> rm_ok ()
  | ArrT (ty, tm1, tm2) ->
     test_comp_type ty >>=== fun _ ->
     test_comp_term tm1 >>=== fun _ ->
     test_comp_term tm2 >>=== fun _ ->
     rm_ok ()

let is_nice_comp ct =
  match ct with
  | CohT (_, _) ->
     rm_fail "Coherences are not compositions"
  | CompT (pd, ty) ->
     (match ty with
      | ObjT -> rm_fail "Composition type should be an arrow"
      | ArrT (x,a,b) ->
         test_comp_type ty >>=== fun _ ->
         rm_ok (pd,(x,a,b))
     )

let is_bubble pd =
  tc_pd_src pd >>= fun pd_src ->
  tc_pd_tgt pd >>= fun pd_tgt ->
  tc_lift (is_disc_pd pd_src >>== fun var1 ->
           is_disc_pd pd_tgt >>== fun var2 ->
           Succeed (var1, var2))

let rm_assoc item al =
  match assoc_opt item al with
  | Some y -> rm_ok y
  | None -> rm_fail "assoc failed"

let tc_assoc item al =
  match assoc_opt item al with
  | Some y -> tc_ok y
  | None -> tc_fail "assoc failed"

let normalize_disk tm =
  put "Trying normalize disk...\n" >>=== fun _ ->
  match tm with
  | VarT _ -> rm_fail "Not a composition"
  | DefAppT _ -> rm_fail "can't normalize a def"
  | CellAppT (ct, args) ->
     (match ct with
      | CohT _ -> rm_fail "normalize_disk does not normalize coherences"
      | CompT (pd ,ty) ->
         all_lift (is_disc_pd pd) >>=== fun x ->
         test_comp_type ty >>=== fun _ ->
         if length args != length pd then rm_fail "malformed composition" else
           rm_assoc x (combine pd args)
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
  | [] -> rm_fail "No success\n"
  | y :: ys ->
     y <|> try_all ys


let try_arg ty dim z (* pd ty args1 ((id, _), arg) *) =
  put (Printf.sprintf "Trying arg %s" (app_zip_head_id z)) >>=== fun _ ->
  match app_zip_head_tm z with
  | VarT _ -> rm_fail ""
  | DefAppT _ -> rm_fail ""
  | CellAppT (ct, args) ->
     is_nice_comp ct >>=== fun (pd2, _) ->
     rm_lift (merge_pd dim z pd2 args) >>=== fun (newpd, newargs) ->
     rm_ok (CellAppT ((CompT (newpd, ty)), newargs))

let bubble_pop tm =
  put "Trying bubble pop" >>=== fun _ ->
  match tm with
  | VarT _ -> rm_fail "Not a composition"
  | DefAppT _ -> rm_fail "can't normalize a def"
  | CellAppT (ct, args) ->
     is_nice_comp ct >>=== fun (pd, (x,a,b)) ->
     all_lift (get_all_zippers (combine pd args)) >>=== fun zs ->
     try_all (map (try_arg (ArrT (x,a,b)) (dim_of_pd pd)) zs)

let check b s =
  if b then tc_ok () else tc_fail s

let check_rm b s =
  if b then rm_ok () else rm_fail s

let rec create_iso pd1 pd2 =
  create_iso' (rev pd1) (rev pd2) [] >>= fun l -> tc_ok (rev l)

and create_iso' pd1 pd2 sub =
  match (pd1, pd2) with
  | ([],[]) -> tc_ok sub
  | ((id1,ty1) :: bs, (id2,ty2) :: cs) ->
     check (sub_all_into_type ty2 sub = ty1) (Printf.sprintf "no iso %s %s" (print_ty_term ty1) (print_ty_term ty2)) >>= fun _ ->
     create_iso' bs cs ((id2,id1) :: sub)
  | _ -> tc_fail "pasting diagrams are not the same size"

and sub_all_into_type (ty : ty_term) sub =
  fold_right (fun (a,b) t -> sub_into_type a b t) sub ty

let rec filterPdWithJoin pd2a (sublist : (string * string) list) =
  match pd2a with
  | [] -> tc_fail "not a valid pasting diagram"
  | _ :: [] -> tc_ok []
  | _ :: _ :: [] -> tc_fail "not a valid pasting diagram"
  | ((fillid, fillty), fillarg) :: ((tgtid, tgtty), tgtarg) :: ((joinid, jointy), joinarg) :: rest ->
     if mem_assoc fillid sublist then filterPdWithJoin rest sublist else
       tc_try_2 (tc_assoc joinid sublist) tc_ok (fun _ -> tc_ok joinid) >>= fun joinidsub ->
       let filltysub = sub_all_into_type fillty sublist in
       let tgttysub = sub_all_into_type tgtty sublist in
       filterPdWithJoin (((joinid, jointy), joinarg) :: rest) sublist >>= fun restdone ->
       tc_ok ((joinidsub, (((fillid, filltysub), fillarg), ((tgtid, tgttysub), tgtarg))) :: restdone)

let rec fold_right_m f (xs : 'b list) a =
  match xs with
  | [] -> tc_ok a
  | y :: ys ->
     fold_right_m f ys a >>= fun res ->
     f res y

let rec insertJoins (pd1a : pd_and_args list) (joins : (string * (pd_and_args * pd_and_args)) list) =
  fold_right_m applyjoin joins pd1a

and applyjoin pd (join : string * (pd_and_args * pd_and_args)) : (pd_and_args list) tcm =
  match join with
  | (id, (x, y)) ->
     (match pd with
      | ((fillid,fillty),fillarg) :: tgt :: ys ->
         if id = fillid then tc_ok (x :: y :: pd) else
           applyjoin ys (id, (x, y)) >>= fun joined ->
           tc_ok (((fillid,fillty),fillarg) :: tgt :: joined)
      | _ -> tc_fail "Can't apply join")


let join_pds pd1 args1 pd2 args2 =
  rm_lift (tc_pd_tgt pd1) >>=== fun pdtgt ->
  rm_lift (tc_pd_src pd2) >>=== fun pdsrc ->
  put (Printf.sprintf "Attempting iso\n%s\n%s" (print_term_ctx pdsrc) (print_term_ctx pdtgt)) >>=== fun _ ->
  rm_lift (create_iso pdtgt pdsrc) >>=== fun sublist ->
  put (Printf.sprintf "Got iso %s" (String.concat " " (map (fun (x,y) -> Printf.sprintf "(%s,%s)" x y) sublist))) >>=== fun _ ->
  rm_lift (filterPdWithJoin (combine pd2 args2) sublist) >>=== fun joins ->
  rm_lift (insertJoins (combine pd1 args1) joins)



let try_wall dim z =
  put (Printf.sprintf "Trying wall %s" (app_zip_head_id z)) >>=== fun _ ->
  match z with
  | (((id, ty), _), a :: b :: c :: after, before) ->
     check_rm (dim_of ty = dim - 1) "wrong dimension for wall" >>=== fun _ ->
     (match (a, c) with
      | (((_, ArrT (tyb, VarT s, VarT x)), arga), ((_, ArrT (_, VarT y, VarT t)), argb)) ->
         check_rm (x = id) "target doesn't match" >>=== fun _ ->
         check_rm (y = id) "source doesn't match" >>=== fun _ ->
         (match (arga, argb) with
          | (CellAppT (ct1, args1)), CellAppT (ct2, args2) ->
             is_nice_comp ct1 >>=== fun (pd1, (tyf, start, _)) ->
             is_nice_comp ct2 >>=== fun (pd2, (_, _, last)) ->
             join_pds pd1 args1 pd2 args2 >>=== fun pd3a ->
             let (newpd, newargs) = split pd3a in
             rm_lift (tc_check_pd newpd) >>=== fun _ ->
             let newarg = CellAppT (CompT (newpd, ArrT (tyf, start, last)), newargs) in
             let zippedres = (b, ((id, ArrT (tyb, VarT s, VarT t)), newarg) :: after, before) in
             let (respd, resargs) = split (zipper_close zippedres) in
             rm_lift (tc_check_pd respd) >>=== fun _ ->
             rm_ok (CellAppT ((CompT (respd, ty)), resargs))
          | _ -> rm_fail "can't expand variables"
         )
      | _ -> rm_fail "couldn't extract variables"
     )

  | _ -> rm_fail "not a wall"

let wall_destruction tm =
  put "Trying wall destruction" >>=== fun _ ->
  match tm with
  | VarT _ -> rm_fail "Not a composition"
  | DefAppT _ -> rm_fail "can't normalize a def"
  | CellAppT (ct, args) ->
     is_nice_comp ct >>=== fun (pd, _) ->
     all_lift (get_all_zippers (combine pd args)) >>=== fun zs ->
     try_all (map (try_wall (dim_of_pd pd)) zs)

let tc_normalize_simpson tm : tm_term tcm =
  let reduction = ref_trans_close (normalize_disk >+>
                                     bubble_pop >+>
                                     wall_destruction) in
  run_reduction reduction tm >>= fun (output, tm') ->
  Printf.printf "%s\n" (String.concat "\n" output);
  tc_ok tm'
