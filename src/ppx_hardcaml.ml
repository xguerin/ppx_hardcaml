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

(* Helpers *)

let mksym =
  let i = ref 1000 in
  fun () ->
    incr i; let i = !i in
    sprintf "__ppx_hardcaml_%d" i

(* Exception *)

let location_exn ~loc msg =
  Location.Error (Location.error ~loc msg)
  |> raise
;;

(* Attributes *)

let get_recur_attr ({ pexp_attributes } as expr) =
  let rec scanner = function
    | [] -> false, []
    | ({ txt = "hwrec" }, _) :: tl -> 
      let a, b = scanner tl in ( a || true, b)
    | hd :: tl ->
      let a, b = scanner tl in ( a, hd :: b)
  in
  let found, nattrs = scanner pexp_attributes in
  (found, { expr with pexp_attributes = nattrs })

let set_recur_attr ~recur ~loc ({ pexp_attributes } as expr) =
  let nattrs = if recur
    then (Location.mkloc "hwrec" loc, PStr([])) :: pexp_attributes
    else pexp_attributes
  in
  { expr with pexp_attributes = nattrs }

(* Wrappers *)

let wrap_expr ~recur ~loc ({ pexp_loc } as expr) =
  let ext = Location.mkloc "hw" loc in
  let bse = set_recur_attr ~recur ~loc expr in
  let evl = Pstr_eval(bse, []) in 
  let str = PStr([{ pstr_desc = evl ; pstr_loc = pexp_loc }])
  in
  { expr with pexp_desc = Pexp_extension(ext, str) }

let wrap_let_binding ~recur ~loc ({ pvb_pat; pvb_expr; pvb_loc; pvb_attributes } as binding) =
  { binding with pvb_expr = wrap_expr ~recur ~loc pvb_expr }

(* Binary operators conversion *)

type binop_t =
  | LeftIsConstInt
  | RightIsSignal
  | RightIsConstInt

let binop_decorate ~typ v =
  match typ with
  | LeftIsConstInt
  | RightIsSignal -> v
  | RightIsConstInt -> v ^ "."

let hw_binop = [ ("lor" , "|:" )
               ; ("land", "&:" )
               ; ("lxor", "^:" )
               ; ("lnot", "~:" )
               ; ("+"   , "+:" )
               ; ("-"   , "-:" )
               ; ("*"   , "*:" )
               ; ("<"   , "<:" )
               ; ("<="  , "<=:")
               ; (">"   , ">:" )
               ; (">="  , ">=:")
               ; ("=="  , "==:")
               ; ("<>"  , "<>:")
               ; ("@"   , "@:" ) ]

let is_hw_binop op = List.mem_assoc op hw_binop

let to_hw_ident ~loc ~typ op =
  let hw_op = try List.assoc op hw_binop |> binop_decorate ~typ with
    | Not_found -> op
  in
  { txt = Lident(hw_op); loc } 

(* Scenarios *)

let mkbinopexpr ~recur ~loc ~typ expr label strn op0 op1 =
  let hw_ident = to_hw_ident ~loc ~typ strn in
  let hw_label = { label with pexp_desc = Pexp_ident(hw_ident) } in
  let hw_op0 = wrap_expr ~recur ~loc op0 in
  let hw_op1 = wrap_expr ~recur ~loc op1 in
  { expr with pexp_desc = Pexp_apply(hw_label, [ (Nolabel, hw_op0);
                                                 (Nolabel, hw_op1) ]) }

let mkbinop ~recur ~loc expr label strn op0 op1 = 
  match op0.pexp_desc, op1.pexp_desc with
  (* 0 + 0 -> ?? *)
  | Pexp_constant(Pconst_integer(_, _)), Pexp_constant(Pconst_integer(_, _)) ->
    location_exn ~loc "Hardware binary operation requires a signal"
  (* sig + 0 -> sig +:. 0 *)
  | _, Pexp_constant(Pconst_integer(_, _)) ->
    mkbinopexpr ~recur ~loc ~typ:RightIsConstInt expr label strn op0 op1
  (* 0 + sig -> ((fun sig -> consti (width sig) 0 +: sig) sig *)
  | Pexp_constant(Pconst_integer(_, _)), _ ->
    let wop0 = [%expr (consti (width [%e op1]) [%e op0])] in
    let tsym = mksym () in
    let esym = evar ~loc tsym in
    let psym = pvar ~loc tsym in
    let wbop = mkbinopexpr ~recur ~loc ~typ:LeftIsConstInt expr label strn wop0 esym in
    [%expr ((fun [%p psym] -> [%e wbop]) [%e op1])]
  (* sig + sig -> sig +: sig *)
  | _ ->
    let max_expr = [%expr max (width [%e op0]) (width [%e op1])] in
    let uresize0 = [%expr uresize [%e op0] [%e max_expr]] in
    let uresize1 = [%expr uresize [%e op1] [%e max_expr]] in
    mkbinopexpr ~recur ~loc ~typ:RightIsSignal expr label strn uresize0 uresize1

let mkfncall ~recur ~loc expr label strn ops = 
  let hw_ops   = List.map (fun (l, e) -> (l, wrap_expr ~recur ~loc e)) ops
  and hw_ident = to_hw_ident ~loc ~typ:RightIsSignal strn in
  let hw_label = { label with pexp_desc = Pexp_ident(hw_ident) } in
  { expr with pexp_desc = Pexp_apply(hw_label, hw_ops) }

let mksinglebit ~loc expr label var bit =
  let hw_ident = { txt = Lident("bit"); loc } in
  let hw_label = { label with pexp_desc = Pexp_ident(hw_ident) } in
  let hw_ops   = [ var; (Nolabel, bit) ] in
  { expr with pexp_desc = Pexp_apply(hw_label, hw_ops) }

let mkbitrange ~loc expr label var v0 v1 =
  let hw_ident = { txt = Lident("select"); loc } in
  let hw_label = { label with pexp_desc = Pexp_ident(hw_ident) } in
  let hw_ops   = [ var; (Nolabel, v0); (Nolabel, v1) ] in
  { expr with pexp_desc = Pexp_apply(hw_label, hw_ops) }

let rec do_apply ~recur ~loc expr = 
  match expr.pexp_desc with
  (* Process binary operators *)
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Lident(strn); loc }) } as label,
      [ (_, op0); (_ , op1) ]
    ) when is_hw_binop strn ->
    mkbinop ~recur ~loc expr label strn op0 op1
  (* Process function calls *)
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Lident(strn); loc }) } as label,
      ops
    ) ->
    mkfncall ~recur ~loc expr label strn ops
  (* Process valid signal single bit operator *)
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Ldot(Lident("String"), "get"); loc }) } as label,
      [ var_tuple;
        (_, ({ pexp_desc = Pexp_constant(Pconst_integer(_, _)) } as hw_bit))
      ])
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Ldot(Lident("String"), "get"); loc }) } as label,
      [ var_tuple;
        (_, ({ pexp_desc = Pexp_ident(_) } as hw_bit))
      ]) ->
    mksinglebit ~loc expr label var_tuple hw_bit
  (* Process valid signal index operator *)
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Ldot(Lident("String"), "get"); loc }) } as label,
      [ var_tuple;
        (_, { pexp_desc = Pexp_tuple ([
            { pexp_desc = Pexp_constant(Pconst_integer(_, _)) } as hw_v0int;
            { pexp_desc = Pexp_constant(Pconst_integer(_, _)) } as hw_v1int
          ])})
      ])
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Ldot(Lident("String"), "get"); loc }) } as label,
      [ var_tuple;
        (_, { pexp_desc = Pexp_tuple ([
            { pexp_desc = Pexp_ident(_) } as hw_v0int;
            { pexp_desc = Pexp_ident(_) } as hw_v1int
          ])})
      ])
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Ldot(Lident("String"), "get"); loc }) } as label,
      [ var_tuple;
        (_, { pexp_desc = Pexp_tuple ([
            { pexp_desc = Pexp_constant(Pconst_integer(_, _)) } as hw_v0int;
            { pexp_desc = Pexp_ident(_) } as hw_v1int
          ])})
      ])
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Ldot(Lident("String"), "get"); loc }) } as label,
      [ var_tuple;
        (_, { pexp_desc = Pexp_tuple ([
            { pexp_desc = Pexp_ident(_) } as hw_v0int;
            { pexp_desc = Pexp_constant(Pconst_integer(_, _)) } as hw_v1int
          ])})
      ]) ->
    mkbitrange ~loc expr label var_tuple hw_v0int hw_v1int
  (* Process invalid signal index operator *)
  | Pexp_apply(
      { pexp_desc = Pexp_ident({ txt = Ldot(Lident("String"), "get"); loc }) },
      _
    ) ->
    location_exn ~loc "Invalid signal subscript format"
  | _ ->
    location_exn ~loc "[%hw] unsupported expression"

let do_let ~recur ~loc bindings =
  List.map (wrap_let_binding ~recur ~loc) bindings

(* Expression mapper *)

open Ppx_core.Std

let expr_mapper ~loc ~path:_ ({ pexp_desc; pexp_loc; pexp_attributes } as bexpr) =
  let recur, expr = get_recur_attr bexpr in
  match pexp_desc with
  | Pexp_apply(_, _) ->
    do_apply ~recur ~loc expr
  | Pexp_let(Nonrecursive, bindings, nexpr) ->
    let wb = do_let ~recur:true ~loc bindings in
    let next = if recur then wrap_expr ~recur ~loc nexpr else nexpr in
    { expr with pexp_desc = Pexp_let(Nonrecursive, wb, next) }
  | Pexp_construct (({ txt = Lident ("::"); loc } as ident), Some (nexpr)) -> 
    let next = wrap_expr ~recur ~loc nexpr in
    { expr with pexp_desc = Pexp_construct (ident, Some (next)) }
  | Pexp_tuple (lexprs) ->
    let next = List.map (fun e -> wrap_expr ~recur ~loc:pexp_loc e) lexprs in
    { expr with pexp_desc = Pexp_tuple (next) }
  | Pexp_fun (label, exp_opt, pat, nexpr) ->
    let next = wrap_expr ~recur ~loc nexpr in
    { expr with pexp_desc = Pexp_fun (label, exp_opt, pat, next) }
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
    let next = wrap_expr ~recur:true ~loc pvb_expr in
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
    ~extensions:[ expr_extension  ; str_extension ]
;;
