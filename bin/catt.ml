(*****************************************************************************)
(*                                                                           *)
(*                                   Main                                    *)
(*                                                                           *)
(*****************************************************************************)

(* fix this .... *)
open Format

open Catt.Io
open Catt.Typecheck
(* open Catt.Agda *)
open Catt.Term
open Catt.Eval

module SS = Set.Make(String)

(*****************************************************************************)
(*                                  Options                                  *)
(*****************************************************************************)

let usage = "catt [options] [file]"

let spec_list = []

(*****************************************************************************)
(*                              Main Entry Point                             *)
(*****************************************************************************)


let pp_error ppf e =
  match e with
  | `NameNotInScope nm -> Fmt.pf ppf "Name not in scope: %s" nm
  | `TypeMismatch msg -> Fmt.pf ppf "%s" msg
  | `PastingError msg -> Fmt.pf ppf "Error while checking pasting context: %s" msg
  | `FullnessError msg -> Fmt.pf ppf "Fullness error: %s" msg
  | `IcityMismatch (_, _) -> Fmt.pf ppf "Icity mismatch"
  | `BadCohQuot msg -> Fmt.pf ppf "%s" msg
  | `NotImplemented f -> Fmt.pf ppf "Feature not implemented: %s" f
  | `InvalidCylinder msg -> Fmt.pf ppf "Invalid cylinder: %s" msg
  | `InternalError -> Fmt.pf ppf "Internal Error"

let () =
  let file_in = ref [] in
  set_margin 80;
  open_vbox 0; (* initialize the pretty printer *)
  Arg.parse spec_list (fun s -> file_in := s::!file_in) usage;
  let files = List.rev (!file_in) in
  let defs = parse_all files in
  match check_defs empty_ctx defs with
  | Ok x ->
    printf "----------------@,Success!";
    print_newline ();
    print_newline ();
    dump_ctx false x;
    Fmt.pr "%a" (Catt.Suite.pp_suite (Catt.Agda.expr_to_agda SS.empty)) (Catt.Suite.map_suite x.top ~f:(fun y -> term_to_expr Emp (quote false 0 (snd y))))
  | Error err -> Fmt.pr "@,Typing error: @,@,%a@,@," pp_error err
