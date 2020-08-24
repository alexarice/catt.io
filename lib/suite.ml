(*****************************************************************************)
(*                                                                           *)
(*                            Suites (snoc lists)                            *)
(*                                                                           *)
(*****************************************************************************)

type 'a suite =
  | Emp
  | Ext of 'a suite * 'a 

let (|>) a b = Ext (a, b)

let rec length s =
  match s with
  | Emp -> 0
  | Ext (s',_) -> length s' + 1

let rec map f s =
  match s with
  | Emp -> Emp
  | Ext (s',x) -> map f s' |> f x 

let rec fold_left f a s =
  match s with
  | Emp -> a
  | Ext (s',x) -> f (fold_left f a s') x

let rec fold_right f s a =
  match s with
  | Emp -> a
  | Ext (s',x) -> fold_right f s' (f x a)

let rec append s t =
  match t with
  | Emp -> s
  | Ext (t',x) -> Ext (append s t',x)

let rec join ss =
  match ss with
  | Emp -> Emp
  | Ext (ss',s) -> append (join ss') s

let rec zip s t =
  match (s,t) with
  | (Emp,_) -> Emp
  | (_,Emp) -> Emp
  | (Ext (s',a), Ext (t',b)) ->
    Ext (zip s' t', (a, b))

let zip_with_idx s =
  let rec zip_with_idx_pr s =
    match s with
    | Emp -> (Emp,0)
    | Ext (s',x) ->
      let (s'', i) = zip_with_idx_pr s' in
      (Ext (s'',(i,x)), i+1)
  in fst (zip_with_idx_pr s)
    
let rec first s =
  match s with
  | Emp -> raise Not_found
  | Ext (Emp,x) -> x
  | Ext (s',_) -> first s'

let last s =
  match s with
  | Emp -> raise Not_found
  | Ext (_,x) -> x
    
let rec assoc k s =
  match s with
  | Emp -> raise Not_found
  | Ext (s',(k',v)) ->
    if (k = k') then v
    else assoc k s'

let singleton a = Ext (Emp, a)

(* Extract de Brujin index from a suite *)
let rec db_get i s =
  match s with
  | Emp -> raise Not_found
  | Ext (s',x) ->
    if (i <= 0) then x
    else db_get (i-1) s'

(* Is there a version which doesn't traverse
   twice? *)
        
let nth n s =
  let l = length s in
  db_get (l-n-1) s 
    
(*****************************************************************************)
(*                                 Instances                                 *)
(*****************************************************************************)

open Cheshire.Monad
open Cheshire.Applicative

module SuiteMonad = MakeMonad(struct

    type 'a t = 'a suite

    let map = map

    let pure = singleton 

    let rec bind s f =
      match s with
      | Emp -> Emp
      | Ext (s',x) -> append (bind s' f) (f x)
      
  end)

module SuiteTraverse(A : Applicative) = struct

  type 'a t = 'a suite
  type 'a m = 'a A.t

  open A.ApplicativeSyntax

  let rec traverse f s =
    match s with
    | Emp -> A.pure Emp
    | Ext (s',x) ->
      let+ y = f x
      and+ t = traverse f s' in
      Ext (t,y)
        
  end

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

open Format

let rec pp_print_suite_custom emp b sep f ppf s =
  match s with
  | Emp -> pp_print_string ppf emp
  | Ext (Emp,a) ->
    if b then 
      fprintf ppf "%s@,%s%a" emp sep f a
    else
      fprintf ppf "%s@,%a" emp f a
  | Ext (s',a) ->
    pp_print_suite_custom emp b sep f ppf s'; 
    fprintf ppf "@,%s%a" sep f a

let pp_print_suite f ppf s =
  pp_print_suite_custom "Emp" true "|>" f ppf s

let pp_print_suite_horiz f ppf s =
  pp_print_suite_custom "" false "," f ppf s
    
