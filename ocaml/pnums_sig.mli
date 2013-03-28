(* $Id: pnums_sig.mli,v 1.4 2013-03-28 16:23:14 deraugla Exp $ *)

type complex_a α = Cpoly.complex α == { re : α; im : α };
type complex = complex_a float;

type field α =
  { zero : α;
    one : α;
    add : α → α → α;
    sub : α → α → α;
    neg : α → α;
    mul : α → α → α;
    div : α → α → α;
    (* extra *)
    eq : α → α → bool;
    imul : int → α → α;
    neg_factor : α → option α;
    k_to_string : α → string }
;

module type Csig =
  sig
    type t = α;
    type i = α;
    type q = α;
    type a₂ = α;
    value zero : t;
    value one : t;
    value minus_one : t;
    value neg : t → t;
    value add : t → t → t;
    value sub : t → t → t;
    value mul : t → t → t;
    value muli : t → i → t;
    value mulq : t → q → t;
    value mula : t → a₂ → t;
    value div : t → t → t;
    value power : t → t → t;
    value gcd : t → t → t;
    value norm : t → t;
    value eq : t → t → bool;
    value neg_factor : t → option t;
    value to_expr : t → MLast.expr;
    value to_string : bool → t → string;
    value to_complex : t → complex;
    value to_q : t → option q;
    value to_a : t → option a₂;
    value of_i : i → t;
    value of_q : q → t;
    value of_a : a₂ → t;
    value of_expr : MLast.expr → t;
    value of_float_string : string → t;
    value of_complex : complex → t;
    value check : t → unit;
  end;
