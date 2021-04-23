(*****************************************************************************)
(*                                                                           *)
(*                               Agda Conversion                             *)
(*                                                                           *)
(*****************************************************************************)

(* open Fmt *)
(* open Term
 * open Meta
 * open Value
 * open Suite
 * open Syntax
 * open Cylinder *)
open Expr
open Fmt
open Suite
open Syntax

(*****************************************************************************)
(*                                 Printing                                  *)
(*****************************************************************************)

module SS = Set.Make(String)

let rec expr_to_agda nm_to_refl ppf e =
  match e with
  | VarE nm -> if SS.mem nm nm_to_refl then pf ppf "refl" else pf ppf "%s" nm
  | LamE (nm, Expl, e2) -> pf ppf "λ %s → %a" nm (expr_to_agda nm_to_refl) e2
  | LamE (nm, Impl, e2) -> pf ppf "λ {%s} → %a" nm (expr_to_agda nm_to_refl) e2
  | AppE (e1, e2, Expl) -> pf ppf "(%a) (%a)" (expr_to_agda nm_to_refl) e1 (expr_to_agda nm_to_refl) e2
  | AppE (e1, e2, Impl) -> pf ppf "(%a) {%a}" (expr_to_agda nm_to_refl) e1 (expr_to_agda nm_to_refl) e2
  | PiE (nm, Expl, e1, e2) -> pf ppf "(%s : %a) → %a" nm (expr_to_agda nm_to_refl) e1 (expr_to_agda nm_to_refl) e2
  | PiE (nm, Impl, e1, e2) -> pf ppf "{%s : %a} → %a" nm (expr_to_agda nm_to_refl) e1 (expr_to_agda nm_to_refl) e2
  | CatE -> pf ppf "Set"
  | ObjE e1 -> pf ppf "%a" (expr_to_agda nm_to_refl) e1
  | HomE (_,e1,e2) -> pf ppf "%a ≡ %a" (expr_to_agda nm_to_refl) e1 (expr_to_agda nm_to_refl) e2
  | CohE (g,_,_,_) -> pf ppf "λ where %a → refl" (pp_suite (fun ppf x ->
                                                      match x with
                                                      | (_,Impl,ObjE(HomE(_,_,_))) -> pf ppf "{refl}"
                                                      | (_,Impl,_) -> pf ppf ""
                                                      | (_,Expl,ObjE(HomE(_,_,_))) -> pf ppf "refl"
                                                      | (_,Expl,_) -> pf ppf "_"
                        )) g
  | _ -> pf ppf "Oh no"
