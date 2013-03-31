(* $Id: field.mli,v 1.6 2013-03-31 07:02:57 deraugla Exp $ *)

open Pnums;

type field α =
  { zero : α;
    one : α;
    add : α → α → α;
    sub : α → α → α;
    neg : α → α;
    mul : α → α → α;
    div : α → α → α;
    (* extra *)
    minus_one : α;
    norm : α → α;
    compare : α → α → int;
    eq : α → α → bool;
    le : α → α → bool;
    lt : α → α → bool;
    imul : int → α → α;
    gcd : α → α → α;
    neg_factor : α → option α;
    of_i : I.t → α;
    of_q : Q.t → α;
    of_a : A₂.t → α;
    of_complex : complex → α;
    of_float_string : string → α;
    to_q : α → option Q.t;
    to_a : α → option A₂.t;
    to_complex : α → complex;
    to_string : α → string;
    float_round_zero : α → α }
;
