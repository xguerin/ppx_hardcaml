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

(* Helpers *)

let (++) a b =
  let hw_a = [%expr [%e a]]
  and hw_b = [%expr [%e b]]
  in
  [%expr uresize [%e hw_a] (max (width [%e hw_a]) (width [%e hw_b]))]

(* Expression mapper *)

let check_index_format expr =
  match expr.pexp_desc with
  | Pexp_constant(Pconst_integer(_, _))
  | Pexp_apply(_, _)
  | Pexp_ident(_) -> ()
  | _ -> location_exn ~loc:expr.pexp_loc "Invalid signal subscript format"

let const_mapper = function
  | { pexp_desc = Pexp_constant(Pconst_integer(txt, Some('h'))) } as expr
    when String.length txt > 2 && String.sub txt ~pos:0 ~len:2 = "0b" ->
    let l = String.length txt - 2 in
    let s = String.sub txt ~pos:2 ~len:l in
    let v = { expr with pexp_desc = Pexp_constant(Pconst_string(s, None)) } in
    [%expr constb [%e v]] 
  | { pexp_desc = Pexp_constant(Pconst_integer(txt, Some('h'))) } as expr ->
    let v = { expr with pexp_desc = Pexp_constant(Pconst_integer(txt, None)) } in
    [%expr consti (HardCaml.Utils.nbits [%e v]) [%e v]] 
  | { pexp_loc } -> location_exn ~loc:pexp_loc "Invalid constant format"

let expr_mapper m expr =
  (* Check the type of the expression *)
  begin match expr with 
    (* Bitwise operators *)
    | [%expr [%e? a] lor  [%e? b]] -> Some [%expr [%e a ++ b] |:  [%e b ++ a]]
    | [%expr [%e? a] land [%e? b]] -> Some [%expr [%e a ++ b] &:  [%e b ++ a]]
    | [%expr [%e? a] lxor [%e? b]] -> Some [%expr [%e a ++ b] ^:  [%e b ++ a]]
    | [%expr         lnot [%e? a]] -> Some [%expr             ~:  [%e      a]]
    (* Arithmetic operators *)
    | [%expr [%e? a] +    [%e? b]] -> Some [%expr [%e a ++ b] +:  [%e b ++ a]]
    | [%expr [%e? a] *    [%e? b]] -> Some [%expr [%e a ++ b] *:  [%e b ++ a]]
    | [%expr [%e? a] -    [%e? b]] -> Some [%expr [%e a ++ b] -:  [%e b ++ a]]
    (* Comparison operators *)
    | [%expr [%e? a] <    [%e? b]] -> Some [%expr [%e a ++ b] <:  [%e b ++ a]]
    | [%expr [%e? a] <=   [%e? b]] -> Some [%expr [%e a ++ b] <=: [%e b ++ a]]
    | [%expr [%e? a] >    [%e? b]] -> Some [%expr [%e a ++ b] >:  [%e b ++ a]]
    | [%expr [%e? a] >=   [%e? b]] -> Some [%expr [%e a ++ b] >=: [%e b ++ a]]
    | [%expr [%e? a] ==   [%e? b]] -> Some [%expr [%e a ++ b] ==: [%e b ++ a]]
    | [%expr [%e? a] <>   [%e? b]] -> Some [%expr [%e a ++ b] <>: [%e b ++ a]]
    (* Concatenation operator *)
    | [%expr [%e? a] @    [%e? b]] -> Some [%expr [%e a ++ b] @:  [%e b ++ a]]
    (* Process valid signal index operator *)
    | [%expr [%e? s].[[%e? i0], [%e? i1]]] ->
      check_index_format i0;
      check_index_format i1;
      Some [%expr select [%e s] [%e i0] [%e i1]]
    (* Process valid signal single bit operator *)
    | [%expr [%e? s].[[%e? i]]] ->
      check_index_format i;
      Some [%expr bit [%e s] [%e i]]
    (* if/then/else construct *)
    | [%expr if [%e? cnd] then [%e? e0] else [%e? e1]] ->
      Some [%expr mux2 [%e cnd] [%e e0] [%e e1]]
    (* Constant *)
    | { pexp_desc = Pexp_constant(Pconst_integer(_, Some('h'))) } ->
      Some (const_mapper expr)
    (* Default *)
    | expr -> None
  end
  (* Call the proper mapper if the expression was rewritten or not *)
  |> function
  | Some (expr) -> m.expr m expr
  | None -> default_mapper.expr m expr

(* Top level mapper *)

let mapper argv = 
  { default_mapper with
    (* Expression mapper *)
    expr = begin fun mapper expr ->
      match expr with
      (* let%hw expression *)
      | [%expr [%hw [%e? { pexp_desc = Pexp_let(Nonrecursive, bindings, nexp) } ]]] ->
        let wb = List.map
            (fun ({ pvb_pat; pvb_expr } as binding) ->
               { binding with
                 pvb_pat = mapper.pat mapper pvb_pat;
                 pvb_expr = expr_mapper { mapper with expr = expr_mapper } pvb_expr;
               })
            bindings in
        let next = mapper.expr mapper nexp in
        { expr with pexp_desc = Pexp_let(Nonrecursive, wb, next) }
      (* [%hw ] expression *)
      | [%expr [%hw [%e? e]]] ->
        [%expr [%e expr_mapper { mapper with expr = expr_mapper } e]]
      (* Constant *)
      | { pexp_desc = Pexp_constant(Pconst_integer(_, Some('h'))) } ->
        const_mapper expr
      (* Default mapper *)
      | _ -> default_mapper.expr mapper expr
    end;
    (* Structure item mapper *)
    structure_item = begin fun mapper stri ->
      match stri with
      (* [%hw let pat = <expr>] or 'let%hw pat = <expr>' *)
      | [%stri [%%hw let [%p? var] = [%e? e0]]] ->
        [%stri let [%p mapper.pat mapper var] = 
          [%e expr_mapper { mapper with expr = expr_mapper } e0]]
      (* Default mapper *)
      | _ -> default_mapper.structure_item mapper stri
    end
  }

let () = register "hw" mapper
