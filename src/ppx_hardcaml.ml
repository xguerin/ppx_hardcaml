(*
 * Copyright (c) 2016 Xavier R. Guérin <copyright@applepine.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open Ast_mapper
open Ast_convenience
open Asttypes
open StdLabels
open Longident
open Parsetree
open Printf

(* Exception *)

let location_exn ~loc msg =
  Location.Error (Location.error ~loc msg)
  |> raise
;;

(* Wrappers *)

let wrap_expr ~loc { pexp_desc; pexp_loc; pexp_attributes } =
  let ext = Location.mkloc "hw" loc in
  let evl = Pstr_eval({ pexp_desc; pexp_loc; pexp_attributes }, pexp_attributes) in 
  let str = PStr([{ pstr_desc = evl ; pstr_loc = pexp_loc }])
  in
  { pexp_desc = Pexp_extension(ext, str); pexp_loc; pexp_attributes }

let wrap_let_binding ~loc { pvb_pat; pvb_expr; pvb_loc; pvb_attributes } =
  { pvb_pat; pvb_expr = wrap_expr ~loc pvb_expr; pvb_loc; pvb_attributes }

(* Binary operators conversion *)

let to_hw_ident_lident ~loc = function
  (* Bitwise *)
  | "lor"  -> { txt = Lident("|:" ); loc } 
  | "land" -> { txt = Lident("&:" ); loc } 
  | "lxor" -> { txt = Lident("^:" ); loc } 
  | "lnot" -> { txt = Lident("~:" ); loc } 
  (* Arithmetic *)
  | "+"    -> { txt = Lident("+:" ); loc } 
  | "-"    -> { txt = Lident("-:" ); loc } 
  | "*"    -> { txt = Lident("*:" ); loc } 
  (* Comparison *)
  | "<"    -> { txt = Lident("<:" ); loc } 
  | "<="   -> { txt = Lident("<=:"); loc } 
  | ">"    -> { txt = Lident(">:" ); loc } 
  | ">="   -> { txt = Lident(">=:"); loc } 
  | "=="   -> { txt = Lident("==:"); loc } 
  | "<>"   -> { txt = Lident("<>:"); loc } 
  | strn   -> { txt = Lident(strn ); loc } 

let to_hw_ident ~loc = function
  | { txt = Lident(strn); loc } -> to_hw_ident_lident ~loc strn
  | { txt = Ldot(Lident("String"), "get"); loc } -> { txt = Lident("select"); loc }
  | _ -> location_exn ~loc "Invalid use of HardCaml PPX extension"

(* Scenarios *)

let rec do_apply ~loc { pexp_desc; pexp_loc; pexp_attributes } = 
  match pexp_desc with
  | Pexp_apply({ pexp_desc = Pexp_ident(ident); pexp_loc; pexp_attributes }, ops) ->
    let hw_ops   = List.map (fun (l, e) -> (l, do_apply ~loc e)) ops in
    let hw_ident = to_hw_ident ~loc ident in
    let hw_label = { pexp_desc = Pexp_ident(hw_ident); pexp_loc; pexp_attributes } in
    { pexp_desc = Pexp_apply(hw_label, hw_ops); pexp_loc; pexp_attributes }
  | _ -> { pexp_desc; pexp_loc; pexp_attributes }

let do_let ~loc bindings =
  List.map (wrap_let_binding ~loc) bindings

(* Mapper *)

open Ppx_core.Std

let mapper ~loc ~path:_ { pexp_desc; pexp_loc; pexp_attributes } =
  printf "%s\n" (Pprintast.string_of_expression { pexp_desc; pexp_loc; pexp_attributes });
  match pexp_desc with
  | Pexp_apply(_, _) ->
    do_apply ~loc { pexp_desc; pexp_loc; pexp_attributes }
  | Pexp_let(Nonrecursive, bindings, next) ->
    let wb = do_let ~loc bindings in
    { pexp_desc = Pexp_let(Nonrecursive, wb, next) ; pexp_loc; pexp_attributes }
  | _ -> location_exn ~loc "Invalid use of HardCaml PPX extension"

let expr_extension =
  Extension.V2.declare
    "hw"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    mapper
;;

let () =
  Ppx_driver.register_transformation "hw" ~extensions:[expr_extension]
;;
