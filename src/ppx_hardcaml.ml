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

(* Mapper *)

open Ppx_core.Std

let mapper ~loc ~path:_ { pexp_desc; pexp_loc; pexp_attributes } =
  match pexp_desc with
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
