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

let (++) ~signed a b =
  let hw_a = [%expr [%e a]]
  and hw_b = [%expr [%e b]]
  in
  if signed=`unsigned then
    [%expr uresize [%e hw_a] (max (width [%e hw_a]) (width [%e hw_b]))]
  else
    [%expr sresize [%e hw_a] (max (width [%e hw_a]) (width [%e hw_b]))]

(* Expression mapper *)

let check_index_format expr =
  match expr.pexp_desc with
  | Pexp_constant(Pconst_integer(_, _))
  | Pexp_apply(_, _)
  | Pexp_ident(_) -> ()
  | _ -> location_exn ~loc:expr.pexp_loc "Invalid signal subscript format"

(*
  rules:
    1. in [%hw ...] only allow +ve constants
    2. in [%hws ...] leading bit always represents sign
    3. outside [%hw{s} ...] smallest bit pattern that represents constant

     | general |  %hw | %hws
-----------------------------
-10  | 10110   |      | 10110
 -9  | 10111   |      | 10111
 -8  |  1000   |      |  1000
 -7  |  1001   |      |  1001
 -6  |  1010   |      |  1010
 -5  |  1011   |      |  1011
 -4  |   100   |      |   100
 -3  |   101   |      |   101
 -2  |    10   |      |    10
 -1  |     1   |      |     1
  0  |     0   |    0 |     0
  1  |     1   |    1 |    01
  2  |    10   |   10 |   010
  3  |    11   |   11 |   011
  4  |   100   |  100 |  0100
  5  |   101   |  101 |  0101
  6  |   110   |  110 |  0110
  7  |   111   |  111 |  0111
  8  |  1000   | 1000 | 01000
  9  |  1001   | 1001 | 01001
 10  |  1010   | 1010 | 01010
*)
let consti_mapper ~loc ~signed v = 
  let rec nbits x = match x with 0 | 1 -> 1 | x -> 1 + (nbits (x/2)) in
  let rec sbits i = if i >= -1 then nbits (abs i) else 1 + sbits (abs (i+1)) in
  let v = int_of_string v in
  let nbits = 
    match signed with
    | `unsigned when v < 0 -> 
      location_exn ~loc "Invalid constant format - expecting unsigned value"
    | `signed when v > 0 -> 1 + nbits v
    | _ when v < 0 -> sbits v
    | _ -> nbits v
  in
  [%expr consti [%e int nbits] [%e int v]]

let const_mapper ~signed = function
  | { pexp_desc = Pexp_constant(Pconst_integer(txt, Some('h'))) } as expr
    when String.length txt > 2 && String.sub txt ~pos:0 ~len:2 = "0b" ->
    let l = String.length txt - 2 in
    let s = String.sub txt ~pos:2 ~len:l in
    let v = { expr with pexp_desc = Pexp_constant(Pconst_string(s, None)) } in
    [%expr constb [%e v]] 
  | { pexp_desc = Pexp_constant(Pconst_integer(txt, Some('h'))); pexp_loc } ->
    consti_mapper ~loc:pexp_loc ~signed txt
  | { pexp_loc } -> location_exn ~loc:pexp_loc "Invalid constant format"

let expr_mapper ~signed m expr =
  let (++) = (++) ~signed in
  (* Check the type of the expression *)
  begin match expr with 
    (* Bitwise operators *)
    | [%expr [%e? a] lor  [%e? b]] -> Some [%expr [%e a ++ b] |:  [%e b ++ a]]
    | [%expr [%e? a] land [%e? b]] -> Some [%expr [%e a ++ b] &:  [%e b ++ a]]
    | [%expr [%e? a] lxor [%e? b]] -> Some [%expr [%e a ++ b] ^:  [%e b ++ a]]
    | [%expr         lnot [%e? a]] -> Some [%expr             ~:  [%e      a]]
    (* Arithmetic operators *)
    | [%expr [%e? a] +    [%e? b]] -> Some [%expr [%e a ++ b] +:  [%e b ++ a]]
    | [%expr [%e? a] *    [%e? b]] -> Some (if signed=`signed 
                                            then [%expr [%e a ++ b] *+  [%e b ++ a]]
                                            else [%expr [%e a ++ b] *:  [%e b ++ a]])
    | [%expr [%e? a] -    [%e? b]] -> Some [%expr [%e a ++ b] -:  [%e b ++ a]]
    (* Comparison operators *)
    | [%expr [%e? a] <    [%e? b]] -> Some (if signed=`signed 
                                            then [%expr [%e a ++ b] <+  [%e b ++ a]]
                                            else [%expr [%e a ++ b] <:  [%e b ++ a]])
    | [%expr [%e? a] <=   [%e? b]] -> Some (if signed=`signed 
                                            then [%expr [%e a ++ b] <=+  [%e b ++ a]]
                                            else [%expr [%e a ++ b] <=:  [%e b ++ a]])
    | [%expr [%e? a] >    [%e? b]] -> Some (if signed=`signed 
                                            then [%expr [%e a ++ b] >+  [%e b ++ a]]
                                            else [%expr [%e a ++ b] >:  [%e b ++ a]])
    | [%expr [%e? a] >=   [%e? b]] -> Some (if signed=`signed 
                                            then [%expr [%e a ++ b] >=+  [%e b ++ a]]
                                            else [%expr [%e a ++ b] >=:  [%e b ++ a]])
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
    | [%expr [%hw if [%e? cnd] then [%e? e0] else [%e? e1]]] ->
      Some [%expr mux2 [%e cnd] [%e e0 ++ e1] [%e e1 ++ e0]]
    (* Constant *)
    | { pexp_desc = Pexp_constant(Pconst_integer(_, Some('h'))) } ->
      Some (const_mapper ~signed expr)
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
      let let_binding ~signed bindings nexp = 
        let wb = List.map
            (fun ({ pvb_pat; pvb_expr } as binding) ->
               { binding with
                 pvb_pat = mapper.pat mapper pvb_pat;
                 pvb_expr = expr_mapper ~signed { mapper with expr = expr_mapper ~signed} pvb_expr;
               })
            bindings in
        let next = mapper.expr mapper nexp in
        { expr with pexp_desc = Pexp_let(Nonrecursive, wb, next) }
      in
      match expr with
      (* let%hw expression *)
      | [%expr [%hw [%e? { pexp_desc = Pexp_let(Nonrecursive, bindings, nexp) } ]]] ->
        let_binding ~signed:`unsigned bindings nexp
      | [%expr [%hws [%e? { pexp_desc = Pexp_let(Nonrecursive, bindings, nexp) } ]]] ->
        let_binding ~signed:`signed bindings nexp
      (* [%hw ] expression *)
      | [%expr [%hw [%e? e]]] ->
        [%expr [%e expr_mapper ~signed:`unsigned 
                     { mapper with expr = expr_mapper ~signed:`unsigned } e]]
      | [%expr [%hws [%e? e]]] ->
        [%expr [%e expr_mapper ~signed:`signed 
                     { mapper with expr = expr_mapper ~signed:`signed } e]]
      (* Constant *)
      | { pexp_desc = Pexp_constant(Pconst_integer(_, Some('h'))) } ->
        const_mapper ~signed:`smallest expr
      (* Default mapper *)
      | _ -> default_mapper.expr mapper expr
    end;
    (* Structure item mapper *)
    structure_item = begin fun mapper stri ->
      match stri with
      (* [%hw let pat = <expr>] or 'let%hw pat = <expr>' *)
      | [%stri [%%hw let [%p? var] = [%e? e0]]] ->
        [%stri let [%p mapper.pat mapper var] = 
          [%e expr_mapper ~signed:`unsigned 
                { mapper with expr = expr_mapper ~signed:`unsigned } e0]]
      | [%stri [%%hws let [%p? var] = [%e? e0]]] ->
        [%stri let [%p mapper.pat mapper var] = 
          [%e expr_mapper ~signed:`signed 
                { mapper with expr = expr_mapper ~signed:`signed } e0]]
      (* Default mapper *)
      | _ -> default_mapper.structure_item mapper stri
    end
  }

let () = register "hw" mapper
