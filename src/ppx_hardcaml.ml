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

let uresize a b =
  let hw_a = [%expr [%e a]]
  and hw_b = [%expr [%e b]]
  in
  [%expr uresize [%e hw_a] (max (width [%e hw_a]) (width [%e hw_b]))]

(* Expression mapper *)

let expr_mapper m = function
  (* Bitwise operators with right-hand constant *)
  | [%expr [%e? a] lor  [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] |:.  [%e b]]
  | [%expr [%e? a] land [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] &:.  [%e b]]
  | [%expr [%e? a] lxor [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] ^:.  [%e b]]
  (* Arithmetic operators with right-hand constant *)
  | [%expr [%e? a] +    [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] +:.  [%e b]]
  | [%expr [%e? a] *    [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] *:.  [%e b]]
  | [%expr [%e? a] -    [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] -:.  [%e b]]
  (* Comparison operators with right-hand constant *)
  | [%expr [%e? a] <    [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] <:.  [%e b]]
  | [%expr [%e? a] <=   [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] <=:. [%e b]]
  | [%expr [%e? a] >    [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] >:.  [%e b]]
  | [%expr [%e? a] >=   [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] >=:. [%e b]]
  | [%expr [%e? a] ==   [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] ==:. [%e b]]
  | [%expr [%e? a] <>   [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> m.expr m [%expr [%e a] <>:. [%e b]]
  (* Bitwise operators *)
  | [%expr [%e? a] lor  [%e? b]] -> m.expr m [%expr [%e uresize a b] |:  [%e uresize b a]]
  | [%expr [%e? a] land [%e? b]] -> m.expr m [%expr [%e uresize a b] &:  [%e uresize b a]]
  | [%expr [%e? a] lxor [%e? b]] -> m.expr m [%expr [%e uresize a b] ^:  [%e uresize b a]]
  | [%expr         lnot [%e? a]] -> m.expr m [%expr                  ~:  [%e           a]]
  (* Arithmetic operators *)
  | [%expr [%e? a] +    [%e? b]] -> m.expr m [%expr [%e uresize a b] +:  [%e uresize b a]]
  | [%expr [%e? a] *    [%e? b]] -> m.expr m [%expr [%e uresize a b] *:  [%e uresize b a]]
  | [%expr [%e? a] -    [%e? b]] -> m.expr m [%expr [%e uresize a b] -:  [%e uresize b a]]
  (* Comparison operators *)
  | [%expr [%e? a] <    [%e? b]] -> m.expr m [%expr [%e uresize a b] <:  [%e uresize b a]]
  | [%expr [%e? a] <=   [%e? b]] -> m.expr m [%expr [%e uresize a b] <=: [%e uresize b a]]
  | [%expr [%e? a] >    [%e? b]] -> m.expr m [%expr [%e uresize a b] >:  [%e uresize b a]]
  | [%expr [%e? a] >=   [%e? b]] -> m.expr m [%expr [%e uresize a b] >=: [%e uresize b a]]
  | [%expr [%e? a] ==   [%e? b]] -> m.expr m [%expr [%e uresize a b] ==: [%e uresize b a]]
  | [%expr [%e? a] <>   [%e? b]] -> m.expr m [%expr [%e uresize a b] <>: [%e uresize b a]]
  (* Concatenation operator *)
  | [%expr [%e? a] @    [%e? b]] -> m.expr m [%expr [%e uresize a b] @:  [%e uresize b a]]
  (* Process valid signal index operator *)
  | [%expr [%e? s].[[%e? i0], [%e? i1]]] -> m.expr m [%expr select [%e s] [%e i0] [%e i1]]
  (* Process valid signal single bit operator *)
  | [%expr [%e? s].[[%e? i]]] -> m.expr m [%expr bit [%e s] [%e i]]
  (* if/then/else construct *)
  | [%expr if [%e? cnd] then [%e? e0] else [%e? e1]] -> m.expr m [%expr mux2 [%e cnd] [%e e0] [%e e1]]
  (* Constant *)
  | { pexp_desc = Pexp_constant(Pconst_integer(txt, Some('h'))) } as expr ->
    let tconst = { expr with pexp_desc = Pexp_constant(Pconst_integer(txt, None)) } in
    m.expr m [%expr consti (HardCaml.Utils.nbits [%e tconst]) [%e tconst]] 
  (* Default *)
  | expr -> default_mapper.expr m expr

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
