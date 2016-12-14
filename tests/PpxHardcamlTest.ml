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

open OUnit2
open HardCaml
open Bits.Comb.IntbitsList

(*
 * Signal indexing test
 *)

let single_bit_indexing context =
  let s0 = const "10101010" in
  let rs = const "1" in
  assert_equal [%hw s0.[1]] rs

let bit_range context =
  let s0 = const "10101010" in
  let rs = const "1010" in
  assert_equal [%hw s0.[3,0]] rs

let var_single_bit_indexing context =
  let s0 = const "10101010" in
  let rs = const "1" in
  let n0 = 1 in
  assert_equal [%hw s0.[n0]] rs

let var_bit_range context =
  let s0 = const "10101010" in
  let rs = const "1010" in
  let n0 = 3 in
  let n1 = 0 in
  assert_equal [%hw s0.[n0,n1]] rs

(*
 * Binary operators
 *)

let signal_signal_binop context =
  let s0 = const "10101010" in
  let s1 = const "10001000" in
  assert_equal [%hw (s0 lor  s1)] s0;
  assert_equal [%hw (s0 land s1)] s1

let signal_int_binop context =
  let s0 = const "10101010" in
  let s1 = const "10001000" in
  assert_equal [%hw (s0 lor  0x88)] s0;
  assert_equal [%hw (s0 land 0x88)] s1

let auto_resize_binop context =
  let s0 = consti 10 2 in
  let s1 = consti  6 2 in
  assert_equal [%hw s0 == s1] (const "1")

let multi_part_binop context =
  let a, b, c = consti 2 0, consti 2 1, consti 2 2 in
  assert_equal [%hw a + b + c] (consti 2 3)

(*
 * Inline functions
 *)

let inline_function context =
  let s0 = const "10101010" in
  let s1 = const "10001000" in
  let%hw do_orr x y = x lor y in
  assert_equal (do_orr s0 s1) s0

(*
 * Structural let item
 *)

let%hw combine_signals a b =
  let sub_a = a.[11,08]
  and sub_b = b.[15,12]
  in
  sub_a @ sub_b

let structural_let context =
  let s0 = const "16'h0F00" in
  let s1 = const "16'hF000" in
  assert_equal (combine_signals s0 s1) (const "8'hFF")

(*
 * Inline recursion let
 *)

let inline_ext_rec_let context =
  let s0 = const "16'h0F00" in
  let s1 = const "16'hF000" in
  let%hw res =
    let sub_0 = s0.[11,08]
    and sub_1 = s1.[15,12]
    in
    sub_0 @ sub_1
  in
  assert_equal res (const "8'hFF")

(*
 * Immediates
 *)

let%hw immediate_const context =
  let x = 1h and y = 0xdh and z = 0b1010h in
  let pow2 n x = x @ zero n in
  let sum = x + y + (pow2 3 (2h + z)) in
  assert_equal sum 206h

(*
 * Test suite definition
 *)

let suite = "PpxHardcamlTest" >::: [
    "single_bit_indexing"     >:: single_bit_indexing;
    "bit_range"               >:: bit_range;
    "var_single_bit_indexing" >:: var_single_bit_indexing;
    "var_bit_range"           >:: var_bit_range;
    "signal_signal_binop"     >:: signal_signal_binop;
    "signal_int_binop"        >:: signal_int_binop;
    "auto_resize_binop"       >:: auto_resize_binop;
    "multi_part_binop"        >:: multi_part_binop;
    "inline_function"         >:: inline_function;
    "structural_let"          >:: structural_let;
    "inline_ext_rec_let"      >:: inline_ext_rec_let;
    "immediate_const"         >:: immediate_const;
  ]

let () = run_test_tt_main suite
