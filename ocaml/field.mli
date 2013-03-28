(* $Id: field.mli,v 1.4 2013-03-28 21:37:59 deraugla Exp $ *)

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
    eq : α → α → bool;
    imul : int → α → α;
    gcd : α → α → α;
    neg_factor : α → option α;
    of_i : I.t → α;
    of_q : Q.t → α;
    of_a : A₂.t → α;
    of_complex : complex → α;
    of_float_string : string → α;
    to_a : α → option A₂.t;
    to_q : α → option Q.t;
    to_complex : α → complex;
    to_string : α → string }
;
