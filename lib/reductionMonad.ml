open Typecheck
open Term
open Common
open List

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

let rm_in_ctx (c : ctx) (m : 'a rm) : 'a rm = fun env -> m { env with gma = c }

let rm_assoc item al =
  match assoc_opt item al with
  | Some y -> rm_ok y
  | None -> rm_fail "assoc failed"

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

let rec try_all xs =
  match xs with
  | [] -> rm_fail "No success\n"
  | y :: ys ->
     y <|> try_all ys

let ( >+> ) (r1 : 'a -> 'b rm) (r2: 'a -> 'b rm) (tm : 'a) : 'b rm =
  r1 tm <|> r2 tm
