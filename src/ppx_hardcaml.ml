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

let wrap_expr ~loc ({ pexp_desc; pexp_loc; pexp_attributes } as expr) =
  let ext = Location.mkloc "hw" loc in
  let evl = Pstr_eval({ pexp_desc; pexp_loc; pexp_attributes }, pexp_attributes) in 
  let str = PStr([{ pstr_desc = evl ; pstr_loc = pexp_loc }])
  in
  { expr with pexp_desc = Pexp_extension(ext, str) }

let wrap_let_binding ~loc ({ pvb_pat; pvb_expr; pvb_loc; pvb_attributes } as binding) =
  { binding with pvb_expr = wrap_expr ~loc pvb_expr }

(* Binary operators conversion *)

let to_hw_ident ~loc = function
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
  (* Concatenation *)
  | "@"    -> { txt = Lident("@:"); loc } 
  (* Default *)
  | strn   -> { txt = Lident(strn ); loc } 

(* Scenarios *)

let rec do_apply ~loc expr = 
  match expr.pexp_desc with
  (* Process binary operators *)
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Lident(strn); loc }) } as label,
      ops
    ) ->
    let hw_ops   = List.map (fun (l, e) -> (l, wrap_expr ~loc e)) ops
    and hw_ident = to_hw_ident ~loc strn in
    let hw_label = { label with pexp_desc = Pexp_ident(hw_ident) } in
    { expr with pexp_desc = Pexp_apply(hw_label, hw_ops) }
  (* Process valid signal index operator *)
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Ldot(Lident("String"), "get"); loc }) } as label,
      [ var_tuple;
        (_, { pexp_desc = Pexp_tuple ([
            { pexp_desc = Pexp_constant(Pconst_integer(v0, _)) } as hw_v0int;
            { pexp_desc = Pexp_constant(Pconst_integer(v1, _)) } as hw_v1int
          ])})
      ]) ->
    let hw_ident = { txt = Lident("select"); loc } in
    let hw_label = { label with pexp_desc = Pexp_ident(hw_ident) } in
    let hw_ops   = [ var_tuple; (Nolabel, hw_v0int); (Nolabel, hw_v1int) ] in
    { expr with pexp_desc = Pexp_apply(hw_label, hw_ops) }
  (* Process invalid signal index operator *)
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Ldot(Lident("String"), "get"); loc }) },
      _
    ) ->
    location_exn ~loc "Invalid signal subscript format"
  | _ ->
    location_exn ~loc "[%hw] unsupported expression"

let do_let ~loc bindings =
  List.map (wrap_let_binding ~loc) bindings

(* Expression mapper *)

open Ppx_core.Std

let expr_mapper ~loc ~path:_ ({ pexp_desc; pexp_loc; pexp_attributes } as expr) =
  match pexp_desc with
  | Pexp_apply(_, _) ->
    do_apply ~loc expr
  | Pexp_let(Nonrecursive, bindings, next) ->
    let wb = do_let ~loc bindings in
    { expr with pexp_desc = Pexp_let(Nonrecursive, wb, next) }
  | Pexp_construct (({ txt = Lident ("::"); loc } as ident), Some (nexpr)) -> 
    { expr with pexp_desc = Pexp_construct (ident, Some (wrap_expr ~loc nexpr)) }
  | Pexp_tuple (lexprs) ->
    { expr with pexp_desc = Pexp_tuple (List.map (fun e -> wrap_expr ~loc:pexp_loc e) lexprs) }
  | _ -> expr

let expr_extension =
  Extension.V2.declare
    "hw"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    expr_mapper
;;

(* Driver registration *)

let () =
  Ppx_driver.register_transformation "hw" ~extensions:[expr_extension]
;;
