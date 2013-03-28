(* $Id: pnums_sig.mli,v 1.8 2013-03-28 20:06:16 deraugla Exp $ *)

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
