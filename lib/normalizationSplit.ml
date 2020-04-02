(*
 * Untitled normalization
 *)

open Term
open Typecheck
open List
open Common
open Printf

type 'a form = Base of 'a | Com of 'a form list * 'a form * 'a form list

type 'a top_form = 'a form list * 'a form

type cell = string * ty_term

let rec print_top_form ((ys , y) : cell top_form) : string =
  let rest = concatMapWithComma (indent $ print_form) (rev ys) in
  let last = indent (print_form y) in
  let sep = if length rest = 0 then [] else [","] in
  String.concat "\n" (["["] @ rest @ sep @ last @ ["]\n"])

and print_form (fm : cell form) =
  match fm with
  | Base (x , _) -> [sprintf "Base: %s" x]
  | Com (before , x , after) ->
     ["<"; "  ["]
     @ indent (concatMapWithComma print_form (rev before))
     @ ["  ]";"  <<"]
     @ indent (print_form x)
     @ ["  >>";"  ["]
     @ indent (concatMapWithComma print_form (rev after))
     @ ["  ]";">"]


and indent (xs : string list) : string list =
  map (fun y -> "  " ^ y) xs

and concatMapWithComma (f : 'a -> string list) (xs : 'a list) : string list =
  match xs with
  | [] -> []
  | y :: [] -> f y
  | y :: ys -> f y @ "," :: concatMapWithComma f ys


let add_to_tf_end (a : 'a form) ((before, x) : 'a top_form) : 'a top_form = (x :: before, a)

let add_to_end (a : 'a form) (f : 'a form) : 'a form tcm =
  match f with
  | Base _ -> tc_fail "Cannot add to Base"
  | Com (before, x , after) -> tc_ok (Com (before, x , a :: after))

let get_last (f : 'a form) : 'a form tcm =
  match f with
  | Base _ -> tc_fail "tried to get last of base"
  | Com (_, _ , a :: _) -> tc_ok a
  | Com (_, x , []) -> tc_ok x

let rec mapf (f : 'a -> 'b) (fm : 'a form) : 'b form =
  match fm with
  | Base x -> Base (f x)
  | Com (before, x, after) -> Com (map (mapf f) before, mapf f x, map (mapf f) after)

and maptf (f : 'a -> 'b) ((before , x) : 'a top_form) : 'b top_form =
  (map (mapf f) before, mapf f x)

let tc_tf_traverse (f : 'a form -> 'b form tcm) (tf : 'a top_form) : ('a top_form tcm) =
  tc_traverse f (fst tf) >>= fun tf1 ->
  f (snd tf) >>= fun tf2 ->
  tc_ok (tf1, tf2)

let tc_f_traverse (f : 'a form -> 'b form tcm) (fm : 'a form) : 'b form tcm =
  match fm with
  | Base _ -> tc_fail "Can't traverse a base"
  | Com (before, x, after) ->
     tc_traverse f before >>= fun before' ->
     f x >>= fun x' ->
     tc_traverse f after >>= fun after' ->
     tc_ok (Com (before' , x' , after'))


let rec foldf (l : 'a -> 'b) (n : 'b list -> 'b -> 'b list -> 'b) (fm : 'a form) : 'b =
  match fm with
  | Base x -> l x
  | Com (before, x, after) -> n (map (foldf l n) before) (foldf l n x) (map (foldf l n) after)

let dim_of_form (f : cell form) =
  foldf (dim_of $ snd) (fun _ x _ -> x) f

let dim_of_top_form (f : cell top_form) =
  dim_of_form (snd f)

let to_top_form (f : cell form) : cell top_form tcm =
  match f with
  | Base _ -> tc_fail "Can't coerce base to top form"
  | Com (before , x , a :: after) -> tc_ok (after @ (x :: before), a)
  | Com (before , x , []) -> tc_ok (before, x)

let rec get_tgt_of_form (f : cell form) : cell form tcm =
  match f with
  | Base (_, ObjT) -> tc_fail "Bases should not be 0 dimensional"
  | Base (_, ArrT (_, _, VarT x) ) ->
     tc_lookup_var x >>= fun y -> tc_ok (Base (x,y))
  | Com (before, x, after) ->
     get_tgt_of_form x >>= fun tgtx ->
     tc_ok (Com (before, tgtx, after))
  | _ -> tc_fail "Encounted non variable"

let rec get_target_to_dim (n : int) (f : cell form) : cell form tcm =
  if n >= dim_of_form f
  then tc_ok f
  else get_tgt_of_form f >>= fun f' -> get_target_to_dim n f'

let rec to_split_form (pd : ctx) : cell top_form tcm =
  tc_check_pd pd >>= fun _ ->
  tc_in_ctx pd (match pd with
                | f :: _ :: _ :: [] -> tc_ok ([], Base f)
                | fill :: _ :: pd' ->
                   to_split_form pd' >>= fun tf ->
                   add_cell_to_form fill tf
                | _ -> tc_fail "pd is not long enough")

and add_cell_to_form ((f,fty) : cell) (tf : cell top_form) : cell top_form tcm =
  match dim_of fty - dim_of_top_form tf with
  | 1 -> tc_ok ([], insert_cell (f,fty) tf)
  | 0 -> if dim_of fty = 1
         then tc_ok (add_to_tf_end (Base (f, fty)) tf)
         else get_tgt_of_form (snd tf) >>= fun tgt ->
         to_top_form tgt >>= fun tgttf ->
         tc_ok (add_to_tf_end (insert_cell (f,fty) tgttf) tf)
  | n -> if n > 1
         then tc_fail "Pasting diagram has gone wrong"
         else tc_tf_traverse (append_to_form (f, fty) (-1-n)) tf

and insert_cell (c : cell) (tf : cell top_form) : cell form =
  match tf with
  | (before, f) -> Com (before, insert_cell_into_form c f, [])

and insert_cell_into_form (c : cell) (f : cell form) : cell form =
  match f with
  | Base _ -> Base c
  | Com (before, x, after) -> Com (before, insert_cell_into_form c x, after)

and append_to_form ((c, ty) : cell) (n : int) (f : cell form) : cell form tcm =
  printf "(%s,%s) %d\n" c (print_ty_term ty) n;
  printf "%s" (String.concat "\n" (print_form f));
  match n with
  | 0 -> if dim_of ty = 1
         then add_to_end (Base (c, ty)) f
         else get_last f >>= fun lf ->
              get_target_to_dim (dim_of ty - 1) lf >>= fun tgt ->
              to_top_form tgt >>= fun tgttf ->
              add_to_end (insert_cell (c, ty) tgttf) f
  | _ -> tc_f_traverse (append_to_form (c, ty) (n-1)) f
