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
    2. in [%hw.signed ...] leading bit always represents sign
    3. outside [%hw{.signed} ...] smallest bit pattern that represents constant

     | general |  %hw | %hw.signed
----------------------------------
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

let match_mapper ~loc resize sel cases = 
  let is_catchall case =
    let rec is_catchall_pat p = match p.ppat_desc with
      | Ppat_any -> true
      | _ -> false
    in
    case.pc_guard = None && is_catchall_pat case.pc_lhs
  in

  (* no exceptions *)
  let exns, cases =
    List.partition 
      ~f:(function
      | {pc_lhs = [%pat? exception [%p? _]]; _} -> true
      | _ -> false) cases
  in
  let () = if exns <> [] then location_exn ~loc "exceptions are not supported" in
  
  (* must have (1) wildcard case *)
  let wildcard,cases = List.partition ~f:is_catchall cases in
  let default = match wildcard with [x] -> x.pc_rhs | _ -> location_exn ~loc "expecting wildcard" in

  (* extract lhs of cases *)
  let cases = 
    List.map
    ~f:(function
      | { pc_lhs={ppat_desc=Ppat_constant(Pconst_integer(i, None)); _}; 
          pc_guard=None; pc_rhs } ->
        int_of_string i, pc_rhs 
      | _ -> location_exn ~loc "match pattern must be an (unguarded) integer")
    cases
  in

  (* sort the cases *)
  let cases = List.sort ~cmp:(fun (a,_) (b,_) -> compare a b) cases in

  (* check that each case is unique *)
  let check_unique_cases cases = 
    let module S = Set.Make(struct type t = int let compare = compare end) in
    let add s (i,_) = S.add i s in
    let s = List.fold_left ~f:add ~init:S.empty cases in
    if S.cardinal s <> List.length cases then
      location_exn ~loc "match patterns must be unique"
  in
  check_unique_cases cases;

  (* turn cases into an [(int*signal) list] expression *)
  let cases = List.fold_right 
    ~f:(fun (x,y) l -> [%expr ([%e int x], [%e y]) :: [%e l]]) cases ~init:[%expr []] 
  in

  [%expr
    (fun resize sel cases default -> (* this should be in a library *)

      let resize_cases cases default = 
        let w = List.fold_left (fun m (_,x) -> max m (width x)) (width default) cases in
        (List.map (fun (x,y) -> x, resize y w) cases), resize default w
      in

      let out_of_range_cases sgn sel cases = 
        let w = width sel in
        let min,max,msk = 
          if sgn then 
            let w = 1 lsl (w-1) in
            -w, w-1, (w lsl 1)-1
          else
            let w = 1 lsl w in
            0, w-1, w-1
        in
        List.map (fun (x,y) -> x land msk, y) @@
        List.filter (fun (x,_) -> x >= min && x <= max) cases
      in

      let rec f sel c def = 
        match width sel, c with
        | 0, [] -> def
        | 0, ((0,d)::_) -> d
        | 0, _ -> def
        | _, [] -> def
        | _ ->
          let e, o = List.partition (fun (i,_) -> (i land 1) = 0) c in
          let e, o = 
            let shift (a,b) = a lsr 1, b in
            List.map shift e, List.map shift o
          in
          let sel2 = lsb sel in
          let sel = try msbs sel with _ -> empty in
          mux2 sel2 (f sel o def) (f sel e def)
      in

      let sgn = (fst @@ List.hd cases) < 0 in
      let cases,default = resize_cases cases default in
      let cases = out_of_range_cases sgn sel cases in
      f sel cases default)
    [%e resize] [%e sel] [%e cases] [%e default] 
  ] 

let expr_mapper ~signed m expr =
  let resize = if signed=`signed then [%expr sresize] else [%expr uresize] in
  let app f a b = [%expr
    let a,b = [%e a], [%e b] in
    let w = max (width a) (width b) in
    let a,b = [%e resize] a w, [%e resize] b w in
    [%e f] a b
  ] in
  let mul, lt, lte, gt, gte = 
    if signed=`signed then
      [%expr ( *+ )], [%expr (<+)], [%expr (<=+)], [%expr (>+)], [%expr (>=+)]
    else
      [%expr ( *: )], [%expr (<:)], [%expr (<=:)], [%expr (>:)], [%expr (>=:)]
  in

  (* Check the type of the expression *)
  begin match expr with 
    (* Bitwise operators *)
    | [%expr [%e? a] lor  [%e? b]] -> `Recurse (app [%expr (|:)] a b)
    | [%expr [%e? a] land [%e? b]] -> `Recurse (app [%expr (&:)] a b)
    | [%expr [%e? a] lxor [%e? b]] -> `Recurse (app [%expr (^:)] a b)
    | [%expr         lnot [%e? a]] -> `Recurse [%expr ~: [%e a]]
    (* Arithmetic operators *)
    | [%expr [%e? a] +    [%e? b]] -> `Recurse (app [%expr (+:)] a b)
    | [%expr [%e? a] *    [%e? b]] -> `Recurse (app mul a b)
    | [%expr [%e? a] -    [%e? b]] -> `Recurse (app [%expr (-:)] a b)
    (* Comparison operators *)
    | [%expr [%e? a] <    [%e? b]] -> `Recurse (app lt  a b)
    | [%expr [%e? a] <=   [%e? b]] -> `Recurse (app lte a b)
    | [%expr [%e? a] >    [%e? b]] -> `Recurse (app gt  a b)
    | [%expr [%e? a] >=   [%e? b]] -> `Recurse (app gte a b)
    | [%expr [%e? a] ==   [%e? b]] -> `Recurse (app [%expr (==:)] a b)
    | [%expr [%e? a] <>   [%e? b]] -> `Recurse (app [%expr (<>:)] a b)
    (* Concatenation operator *)
    | [%expr [%e? a] @    [%e? b]] -> `Recurse [%expr a @: b]
    (* Process valid signal index operator *)
    | [%expr [%e? s].[[%e? i0], [%e? i1]]] ->
      check_index_format i0;
      check_index_format i1;
      `Recurse [%expr select [%e s] [%e i0] [%e i1]]
    (* Process valid signal single bit operator *)
    | [%expr [%e? s].[[%e? i]]] ->
      check_index_format i;
      `Recurse [%expr bit [%e s] [%e i]]
    (* if/then/else construct *)
    | [%expr [%hw if [%e? cnd] then [%e? e0] else [%e? e1]]] ->
      `Recurse (app [%expr mux2 [%e cnd]] e0 e1)
    (* mux *)
    | [%expr [%hw [%e? { pexp_desc=Pexp_match(sel, cases); pexp_loc=loc }]]] ->
      let sel = m.expr m sel in
      let cases = List.map (fun c -> { c with pc_rhs = m.expr m c.pc_rhs }) cases in
      `Return (match_mapper ~loc resize sel cases)
    (* Constant *)
    | { pexp_desc = Pexp_constant(Pconst_integer(_, Some('h'))) } ->
      `Recurse (const_mapper ~signed expr)
    (* Default *)
    | expr -> `Default
  end
  (* Call the proper mapper if the expression was rewritten or not *)
  |> function
  | `Recurse (expr) -> m.expr m expr
  | `Return (expr) -> expr
  | `Default -> default_mapper.expr m expr

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
      | [%expr [%hw.signed [%e? { pexp_desc = Pexp_let(Nonrecursive, bindings, nexp) } ]]] ->
        let_binding ~signed:`signed bindings nexp
      (* [%hw ] expression *)
      | [%expr [%hw [%e? e]]] ->
        [%expr [%e expr_mapper ~signed:`unsigned 
                     { mapper with expr = expr_mapper ~signed:`unsigned } e]]
      | [%expr [%hw.signed [%e? e]]] ->
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
      | [%stri [%%hw.signed let [%p? var] = [%e? e0]]] ->
        [%stri let [%p mapper.pat mapper var] = 
          [%e expr_mapper ~signed:`signed 
                { mapper with expr = expr_mapper ~signed:`signed } e0]]
      (* Default mapper *)
      | _ -> default_mapper.structure_item mapper stri
    end
  }

let () = register "hw" mapper
