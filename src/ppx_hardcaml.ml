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
  | _ -> location_exn ~loc "Invalid use of HardCaml PPX extension"

(* Scenarios *)

let do_apply ~loc = function
  | { pexp_desc = Pexp_ident(ident); pexp_loc; pexp_attributes } ->
    let hw_ident = to_hw_ident ~loc ident in
    { pexp_desc = Pexp_ident(hw_ident); pexp_loc; pexp_attributes }
  | _ -> location_exn ~loc "Invalid use of HardCaml PPX extension"

(* Mapper *)

open Ppx_core.Std

let mapper ~loc ~path:_ { pexp_desc; pexp_loc; pexp_attributes } =
  match pexp_desc with
  | Pexp_apply(label, ops) ->
    { pexp_desc = Pexp_apply(do_apply ~loc label, ops); pexp_loc; pexp_attributes }
  | _ -> location_exn ~loc "Invalid use of HardCaml PPX extension"

let extension =
  Extension.V2.declare
    "hw"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    mapper
;;

let () =
  Ppx_driver.register_transformation "hw" ~extensions:[extension]
;;
