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

let getr ({ pexp_attributes } as expr) =
  let rec scanner = function
    | [] -> false, []
    | ({ txt = "hwrec" }, _) :: tl -> 
      let a, b = scanner tl in ( a || true, b)
    | hd :: tl ->
      let a, b = scanner tl in ( a, hd :: b)
  in
  let found, nattrs = scanner pexp_attributes in
  (found, { expr with pexp_attributes = nattrs })

let setr ~r ({ pexp_attributes } as expr) =
  let nattrs = if r
    then (Location.mknoloc "hwrec", PStr([])) :: pexp_attributes
    else pexp_attributes
  in
  { expr with pexp_attributes = nattrs }

let ewrap ~r expr =
  [%expr [%hw [%e setr ~r expr]]]

let uresize ~r a b =
  let hw_a = [%expr [%e ewrap ~r a]]
  and hw_b = [%expr [%e ewrap ~r b]]
  in
  [%expr uresize [%e hw_a] (max (width [%e hw_a]) (width [%e hw_b]))]

(* Expression mapper *)

open Ppx_core.Std

let expr_mapper ~loc ~path:_ bexpr =
  let r, expr = getr bexpr in
  match bexpr with
  (* Bitwise operators with right-hand constant *)
  | [%expr [%e? a] lor  [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] |:.  [%e ewrap ~r b]]
  | [%expr [%e? a] land [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] &:.  [%e ewrap ~r b]]
  | [%expr [%e? a] lxor [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] ^:.  [%e ewrap ~r b]]
  (* Arithmetic operators with right-hand constant *)
  | [%expr [%e? a] +    [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] +:.  [%e ewrap ~r b]]
  | [%expr [%e? a] *    [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] *:.  [%e ewrap ~r b]]
  | [%expr [%e? a] -    [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] -:.  [%e ewrap ~r b]]
  (* Comparison operators with right-hand constant *)
  | [%expr [%e? a] <    [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] <:.  [%e ewrap ~r b]]
  | [%expr [%e? a] <=   [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] <=:. [%e ewrap ~r b]]
  | [%expr [%e? a] >    [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] >:.  [%e ewrap ~r b]]
  | [%expr [%e? a] >=   [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] >=:. [%e ewrap ~r b]]
  | [%expr [%e? a] ==   [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] ==:. [%e ewrap ~r b]]
  | [%expr [%e? a] <>   [%e? { pexp_desc = Pexp_constant(_) } as b ]] -> [%expr [%e ewrap ~r a] <>:. [%e ewrap ~r b]]
  (* Bitwise operators *)
  | [%expr [%e? a] lor  [%e? b]] -> [%expr [%e uresize ~r a b] |:  [%e uresize ~r b a]]
  | [%expr [%e? a] land [%e? b]] -> [%expr [%e uresize ~r a b] &:  [%e uresize ~r b a]]
  | [%expr [%e? a] lxor [%e? b]] -> [%expr [%e uresize ~r a b] ^:  [%e uresize ~r b a]]
  | [%expr         lnot [%e? a]] -> [%expr                     ~:  [%e ewrap   ~r   a]]
  (* Arithmetic operators *)
  | [%expr [%e? a] +    [%e? b]] -> [%expr [%e uresize ~r a b] +:  [%e uresize ~r b a]]
  | [%expr [%e? a] *    [%e? b]] -> [%expr [%e uresize ~r a b] *:  [%e uresize ~r b a]]
  | [%expr [%e? a] -    [%e? b]] -> [%expr [%e uresize ~r a b] -:  [%e uresize ~r b a]]
  (* Comparison operators *)
  | [%expr [%e? a] <    [%e? b]] -> [%expr [%e uresize ~r a b] <:  [%e uresize ~r b a]]
  | [%expr [%e? a] <=   [%e? b]] -> [%expr [%e uresize ~r a b] <=: [%e uresize ~r b a]]
  | [%expr [%e? a] >    [%e? b]] -> [%expr [%e uresize ~r a b] >:  [%e uresize ~r b a]]
  | [%expr [%e? a] >=   [%e? b]] -> [%expr [%e uresize ~r a b] >=: [%e uresize ~r b a]]
  | [%expr [%e? a] ==   [%e? b]] -> [%expr [%e uresize ~r a b] ==: [%e uresize ~r b a]]
  | [%expr [%e? a] <>   [%e? b]] -> [%expr [%e uresize ~r a b] <>: [%e uresize ~r b a]]
  (* Concatenation operator *)
  | [%expr [%e? a] @    [%e? b]] -> [%expr [%e uresize ~r a b] @:  [%e uresize ~r b a]]
  (* Process valid signal index operator *)
  | [%expr [%e? s].[[%e? i0], [%e? i1]]] -> [%expr select [%e s] [%e ewrap ~r i0] [%e ewrap ~r i1]]
  (* Process valid signal single bit operator *)
  | [%expr [%e? s].[[%e? i]]] -> [%expr bit [%e ewrap ~r s] [%e ewrap ~r i]]
  (* Process function calls *)
  | { pexp_desc = Pexp_apply(ident, ops) } ->
    List.fold_left
      ~f:(fun acc (_, e) -> [%expr [%e acc] [%e ewrap ~r e]])
      ~init:[%expr [%e ident]]
      ops
  (* fun construct *)
  | [%expr fun [%p? pat] -> [%e? expr]] ->
    [%expr fun [%p pat] -> [%e ewrap ~r expr]]
  (* if/then/else construct *)
  | [%expr if [%e? cnd] then [%e? e0] else [%e? e1]] ->
    [%expr mux2 [%e ewrap ~r cnd] [%e ewrap ~r e0] [%e ewrap ~r e1]]
  (* Let construct *)
  | { pexp_desc = Pexp_let(Nonrecursive, bindings, nexpr) } ->
    let wb = List.map
        (fun ({ pvb_expr } as binding) -> { binding with pvb_expr = ewrap ~r pvb_expr })
        bindings in
    let next = if r then ewrap ~r nexpr else nexpr in
    { expr with pexp_desc = Pexp_let(Nonrecursive, wb, next) }
  (* List construct *)
  | { pexp_desc = Pexp_construct (({ txt = Lident ("::"); loc } as ident), Some (nexpr)) } -> 
    let next = ewrap ~r nexpr in
    { expr with pexp_desc = Pexp_construct (ident, Some (next)) }
  (* Tuple construct *)
  | { pexp_desc = Pexp_tuple (lexprs) } ->
    let next = List.map (fun e -> ewrap ~r e) lexprs in
    { expr with pexp_desc = Pexp_tuple (next) }
  (* Constant *)
  | { pexp_desc = Pexp_constant(Pconst_integer(txt, Some('h'))) } ->
    let tconst = { expr with pexp_desc = Pexp_constant(Pconst_integer(txt, None)) } in
    [%expr consti (HardCaml.Utils.nbits [%e tconst]) [%e tconst]] 
  (* Default *)
  | _ -> expr

let expr_extension =
  Extension.V2.declare
    "hw"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    expr_mapper

(* Structure mapper *)

let rec str_parser ~loc = function
  | [] -> []
  | ({ pvb_expr } as vb) :: tl ->
    let next = ewrap ~r:true pvb_expr in
    { vb with pvb_expr = next } :: (str_parser ~loc tl)

let str_mapper ~loc ~path:_ ({ pstr_desc; pstr_loc } as str_item) = 
  match pstr_desc with
  | Pstr_value (Nonrecursive, vbs) ->
    { str_item with pstr_desc = Pstr_value (Nonrecursive, str_parser ~loc vbs) }
  | _ -> str_item

let pstr_item str_item =
  let open Ast_pattern in
  pstr (str_item ^:: nil)

let str_extension =
  Extension.V2.declare
    "hw"
    Extension.Context.structure_item
    Ast_pattern.(pstr_item __)
    str_mapper
;;

(* Driver registration *)

let () =
  Ppx_driver.register_transformation "hw"
    ~extensions:[ expr_extension ; str_extension ]
;;
