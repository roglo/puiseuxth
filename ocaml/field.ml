(* $Id: field.ml,v 1.3 2013-06-23 17:34:52 deraugla Exp $ *)

open Pnums;

type field α β =
  { zero : α;
    one : α;
    add : α → α → α;
    sub : α → α → α;
    neg : α → α;
    mul : α → α → α;
    div : α → α → α;
    is_zero : α → bool;
    ext : β }
;

value zero fld = fld.zero;
value one fld = fld.one;
value add fld = fld.add;
value mul fld = fld.mul;
value is_zero fld = fld.is_zero;

type ext α β =
  { minus_one : α;
    equal : α → α → bool;
    normalise : α → α;
    nth_root : α → int → α;
    compare : α → α → int;
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
