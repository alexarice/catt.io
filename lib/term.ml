(*****************************************************************************)
(*                                                                           *)
(*                              Internal Syntax                              *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Base
open Expr
open Suite

(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type idx = int
type mvar = int

type term =
  | VarT of idx
  | TopT of name 
  | LamT of name * icit * term
  | AppT of term * term * icit
  | PiT of name * icit * term * term
  | QuotT of quot_res
  | ObjT of term
  | HomT of term * term * term
  | CohT of term tele * term
  | CylT of term * term * term
  | BaseT of term
  | LidT of term
  | CoreT of term 
  | ArrT of term
  | CatT
  | TypT
  | MetaT of mvar
  | InsMetaT of mvar 

and quot_res =
  | PCompRes of unit Pd.pd * term tele * term
  | SCompRes of int list * term tele * term 

(*****************************************************************************)
(*                              Utility Routines                             *)
(*****************************************************************************)

let lvl_to_idx k l = k - l - 1

let rec term_to_expr nms tm =
  let tte = term_to_expr in 
  match tm with
  | VarT i ->
    let nm = db_get i nms in VarE nm
  | TopT nm -> VarE nm
  | LamT (nm,ict,bdy) ->
    LamE (nm, ict, tte (Ext (nms,nm)) bdy)
  | AppT (u,v,ict) ->
    AppE (tte nms u, tte nms v, ict)
  | PiT (nm,ict,a,b) ->
    PiE (nm, ict, tte nms a, tte (Ext (nms,nm)) b)
  | QuotT (PCompRes (pd,_,_)) -> QuotE (PComp pd)
  | QuotT (SCompRes (ds,_,_)) -> QuotE (SComp ds) 
  | ObjT c -> ObjE (tte nms c)
  | HomT (c,s,t) ->
    HomE (tte nms c, tte nms s, tte nms t)
  | CohT (g,a) ->

    let rec go g nms m =
      match g with
      | Emp -> m nms Emp
      | Ext (g',(nm,ict,ty)) ->
        go g' nms (fun nms' ge' ->
            let e = tte nms' ty in
            m (Ext (nms',nm))
              (Ext (ge',(nm,ict,e))))

    in go g nms (fun nms' ge' -> CohE (ge' , tte nms' a))

  | CylT (b,l,c) ->
    CylE (tte nms b, tte nms l, tte nms c)
  | BaseT c -> BaseE (tte nms c)
  | LidT c -> LidE (tte nms c)
  | CoreT c -> CoreE (tte nms c)
  | ArrT c -> ArrE (tte nms c)
  | CatT -> CatE 
  | TypT -> TypE
  | MetaT _ -> HoleE
  (* Somewhat dubious, since we lose the implicit application ... *)
  | InsMetaT _ -> HoleE

let rec tele_to_pi tl ty =
  match tl with
  | Emp -> ty
  | Ext (tl',(nm,ict,ty_tm)) ->
    tele_to_pi tl' (PiT (nm,ict,ty_tm,ty))

let pi_to_tele ty =
  let rec go tl ty = 
    match ty with
    | PiT (nm,ict,a,b) ->
      go (Ext (tl,(nm,ict,a))) b
    | _ -> (tl,ty)
  in go Emp ty

(* labels a pd with deBruijn levels *)
let pd_to_lvl pd =
  let open Pd in

  let rec pd_to_lvl_br k br =
    match br with
    | Br (_,brs) ->
      let (k', brs') = pd_to_lvl_brs (k+1) brs
      in (k', Br (VarT k, brs'))

  and pd_to_lvl_brs k brs =
    match brs with
    | Emp -> (k,Emp)
    | Ext (bs,(_,b)) ->
      let (k', bs') = pd_to_lvl_brs k bs in
      let (k'', b') = pd_to_lvl_br (k'+1) b in 
      (k'', Ext (bs',(VarT k', b')))

  in snd (pd_to_lvl_br 0 pd)

(* label a pasting diagram with deBruijn indices *)
let pd_to_idx pd = 
  let open Pd in

  let rec pd_to_idx_br k br =
    match br with
    | Br (_,brs) ->
      let (l, brs') = pd_to_idx_brs k brs in
      (l+1, Br (VarT l, brs'))

  and pd_to_idx_brs k brs =
    match brs with
    | Emp -> (k,Emp)
    | Ext (brs',(_,br)) ->
      let (k', br') = pd_to_idx_br k br in
      let (k'', brs'') = pd_to_idx_brs (k'+1) brs' in
      (k'', Ext (brs'',(VarT k',br')))

  in snd (pd_to_idx_br 0 pd)

let pd_to_term_tele pd =
  let mk_cat = CatT in 
  let mk_obj c = ObjT c in 
  let mk_hom c s t = HomT (c,s,t) in 
  let mk_nm _ l = str "x%d" l in 
  let mk_var _ l = VarT l in 
  let mk_base_cat = VarT 0 in
  pd_to_tele mk_cat mk_obj mk_hom mk_nm mk_var mk_base_cat pd 

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)
    
let is_app_tm tm =
  match tm with
  | AppT (_,_,_) -> true
  | _ -> false

let is_pi_tm tm =
  match tm with
  | PiT (_,_,_,_) -> true
  | _ -> false
    
let rec pp_term ppf tm =
  match tm with
  | VarT i -> int ppf i
  | TopT nm -> string ppf nm 
  | LamT (nm,Impl,t) ->
    pf ppf "\\{%s}. %a" nm pp_term t
  | LamT (nm,Expl,t) ->
    pf ppf "\\%s. %a" nm pp_term t
  | AppT (u,v,Impl) ->
    pf ppf "%a {%a}" pp_term u pp_term v
  | AppT (u,v,Expl) ->
    let pp_v = if (is_app_tm v) then
        parens pp_term
      else pp_term in 
    pf ppf "%a %a" pp_term u pp_v v
  | PiT (nm,Impl,a,p) ->
    pf ppf "{%s : %a} -> %a" nm
      pp_term a pp_term p
  | PiT (nm,Expl,a,p) when Poly.(=) nm "" ->
    let pp_a = if (is_pi_tm a) then
        parens pp_term
      else pp_term in 
    pf ppf "%a -> %a" 
      pp_a a pp_term p
  | PiT (nm,Expl,a,p) ->
    pf ppf "(%s : %a) -> %a" nm
      pp_term a pp_term p
  | QuotT (PCompRes (pd,_,_)) ->
    pf ppf "`[ %a ]" pp_quot_cmd (PComp pd)
  | QuotT (SCompRes (ds,_,_)) ->
    pf ppf "`[ %a ]" pp_quot_cmd (SComp ds)
  | ObjT c ->
    pf ppf "[%a]" pp_term c
  | HomT (c,s,t) ->
    pf ppf "%a | %a => %a" pp_term c pp_term s pp_term t
  | CohT (g,a) ->
    pf ppf "coh @[[ %a : %a ]@]" (pp_tele pp_term) g pp_term a
  | CylT (b,l,c) ->
    pf ppf "[| %a | %a | %a |]" pp_term b pp_term l pp_term c
  | BaseT c -> pf ppf "base %a" pp_term c
  | LidT c -> pf ppf "lid %a" pp_term c
  | CoreT c -> pf ppf "core %a" pp_term c
  | ArrT c -> pf ppf "Arr %a" pp_term c
  | CatT -> pf ppf "Cat"
  | TypT -> pf ppf "U"
  | MetaT _ -> pf ppf "_"
  (* Again, misses some implicit information ... *)
  | InsMetaT _ -> pf ppf "*_*"
