(* $Id: field.mli,v 1.23 2013-04-06 08:33:57 deraugla Exp $ *)

open Pnums;
open Poly;

type field α β =
  { zero : α;
    one : α;
    add : α → α → α;
    sub : α → α → α;
    neg : α → α;
    mul : α → α → α;
    div : α → α → α;
    (* extra *)
    minus_one : α;
    normalise : α → α;
    nth_root : α → int → α;
    compare : α → α → int;
    eq : α → α → bool;
    gcd : α → α → α;
    neg_factor : α → option α;
    of_i : I.t → α;
    of_q : Q.t → α;
    of_a : A₂.t → α;
    of_complex : complex β → α;
    of_float_string : string → α;
    to_q : α → option Q.t;
    to_a : α → option A₂.t;
    to_complex : α → complex β;
    to_string : α → string;
    float_round_zero : α → α;
    complex_round_zero : complex β → complex β;
    complex_mul : complex β → complex β → complex β;
    cpoly_roots : list (complex β) → list (complex β);
    complex_to_string : bool → complex β → string }
;

type alg_cl_field α β =
  { ac_field : field α β;
    ac_roots : polynomial α → list (α * int) }
;
