open Parsetree
open Ast_iterator
open Asttypes
open Longident

type target = Ref | While | For

module ExprSet = Set.Make (struct
  type t = target * Location.t

  let compare = compare
end)

let parse_ocaml_file filename =
  let ic = open_in filename in
  let lb = Lexing.from_channel ic in
  Location.init lb filename;
  let ast = Parse.implementation lb in
  close_in ic;
  ast

let detect_ref_and_while ast =
  let found = ref ExprSet.empty in

  let iter : iterator =
    {
      default_iterator with
      expr =
        (fun this expr ->
          (match expr.pexp_desc with
          | Pexp_apply
              ({ pexp_desc = Pexp_ident { txt = Lident "ref"; _ }; _ }, _) ->
              found := ExprSet.add (Ref, expr.pexp_loc) !found
          | Pexp_while _ -> found := ExprSet.add (While, expr.pexp_loc) !found
          | Pexp_for _ -> found := ExprSet.add (For, expr.pexp_loc) !found
          | _ -> ());
          default_iterator.expr this expr);
    }
  in

  iter.structure iter ast;
  !found

let () =
  let files = Array.to_list Sys.argv |> List.tl in
  let alarms =
    List.fold_left
      (fun acc filename ->
        let ast = parse_ocaml_file filename in
        let found = detect_ref_and_while ast in
        ExprSet.union acc found)
      ExprSet.empty files
  in
  ExprSet.iter
    (function
      | Ref, loc -> Format.printf "%a: found ref\n" Location.print_loc loc
      | While, loc -> Format.printf "%a: found while\n" Location.print_loc loc
      | For, loc -> Format.printf "%a: found for\n" Location.print_loc loc)
    alarms;
  if ExprSet.is_empty alarms then exit 0 else exit 1
