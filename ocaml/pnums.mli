(* $Id: pnums.mli,v 1.26 2013-05-26 23:19:52 deraugla Exp $ *)

exception Overflow;

value gcd : int → int → int;
value lcm : int → int → int;

value sup_string_of_string : string → string;
value inf_string_of_string : string → string;

module I :
  sig
    type t = α;
    value of_int : int → t;
    value to_int : t → int;
    value zero : t;
    value one : t;
    value two : t;
    value minus_one : t;
    value succ : t → t;
    value pred : t → t;
    value neg : t → t;
    value abs : t → t;
    value add : t → t → t;
    value addi : t → int → t;
    value sub : t → t → t;
    value mul : t → t → t;
    value muli : t → int → t;
    value div : t → t → t;
    value modi : t → int → int;
    value modn : t → t → t;
    value incr : ref t → unit;
    value compare : t → t → int;
    value eq : t → t → bool;
    value lt : t → t → bool;
    value gt : t → t → bool;
    value ge : t → t → bool;
    value eq : t → t → bool;
    value min : t → t → t;
    value gcd : t → t → t;
    value lcm : t → t → t;
    value os : string → t;
    value ts : t → string;
    value to_float : t → float;
  end;

module Q :
  sig
    type t = α;
    value rnum : t → I.t;
    value rden : t → I.t;
    value make : I.t → I.t → t;
    value zero : t;
    value one : t;
    value norm : t → t;
    value neg : t → t;
    value add : t → t → t;
    value addi : t → I.t → t;
    value sub : t → t → t;
    value mul : t → t → t;
    value muli : t → I.t → t;
    value div : t → t → t;
    value divi : t → I.t → t;
    value compare : t → t → int;
    value eq : t → t → bool;
    value le : t → t → bool;
    value lt : t → t → bool;
    value min : t → t → t;
    value max : t → t → t;
    value of_i : I.t → t;
    value of_expr_if_any : MLast.expr → option t;
    value of_expr : MLast.expr → t;
    value to_expr : t → MLast.expr;
    value to_string : t → string;
  end
;

module A₂ :
  sig
    (* a + b √d *)
    type t = { a : Q.t; b : Q.t; d : I.t };
    value make : Q.t → Q.t → I.t → t;
    value zero : t;
    value one : t;
    value norm : t → t;
    value neg : t → t;
    value add : t → t → t;
    value addi : t → I.t → t;
    value addq : t → Q.t → t;
    value sub : t → t → t;
    value mul : t → t → t;
    value muli : t → I.t → t;
    value mulq : t → Q.t → t;
    value div : t → t → t;
    value divi : t → I.t → t;
    value gcd : t → t → t;
    value of_i : I.t → t;
    value of_q : Q.t → t;
    value of_expr : MLast.expr → option t;
    value to_string : bool → t → string;
    value to_expr : t → MLast.expr;
  end
;

type complex α = Cpoly.complex α == { re : α; im : α };

module C :
  sig
    type t = 'abstract;
    value zero : t;
    value one : t;
    value minus_one : t;
    value neg : t → t;
    value add : t → t → t;
    value sub : t → t → t;
    value mul : t → t → t;
    value muli : t → I.t → t;
    value mulq : t → Q.t → t;
    value mula : t → A₂.t → t;
    value div : t → t → t;
    value gcd : t → t → t;
    value normalise : t → t;
    value nth_root : t → int → t;
    value compare : t → t → int;
    value eq : t → t → bool;
    value neg_factor : t → option (t);
    value to_expr : t → MLast.expr;
    value to_string : bool → t → string;
    value to_complex : t → complex float;
    value to_q : t → option Q.t;
    value to_a : t → option A₂.t;
    value of_i : I.t → t;
    value of_q : Q.t → t;
    value of_a : A₂.t → t;
    value of_expr : MLast.expr → t;
    value of_float_string : string → t;
    value of_complex : complex float → t;
    value check : t → unit;
    value float_round_zero : t → t;
    value complex_round_zero : complex float → complex float;
    value complex_mul : complex float → complex float → complex float;
    value complex_nth_root : complex float → int → complex float;
    value cpoly_roots : list (complex float) → list (complex float);
    value complex_to_string : bool → complex float → string;
  end;

module M :
  sig
    open Cpoly;
    type t = 'abstract;
    value zero : t;
    value one : t;
    value minus_one : t;
    value neg : t → t;
    value add : t → t → t;
    value sub : t → t → t;
    value mul : t → t → t;
    value muli : t → I.t → t;
    value mulq : t → Q.t → t;
    value mula : t → A₂.t → t;
    value div : t → t → t;
    value gcd : t → t → t;
    value normalise : t → t;
    value nth_root : t → int → t;
    value compare : t → t → int;
    value eq : t → t → bool;
    value neg_factor : t → option (t);
    value to_expr : t → MLast.expr;
    value to_string : bool → t → string;
    value to_complex : t → complex Mfl.t;
    value to_q : t → option Q.t;
    value to_a : t → option A₂.t;
    value of_i : I.t → t;
    value of_q : Q.t → t;
    value of_a : A₂.t → t;
    value of_expr : MLast.expr → t;
    value of_float_string : string → t;
    value of_complex : complex Mfl.t → t;
    value check : t → unit;
    value float_round_zero : t → t;
    value complex_round_zero : complex Mfl.t → complex Mfl.t;
    value complex_mul : complex Mfl.t → complex Mfl.t → complex Mfl.t;
    value complex_nth_root : complex Mfl.t → int → complex Mfl.t;
    value cpoly_roots : list (complex Mfl.t) → list (complex Mfl.t);
    value complex_to_string : bool → complex Mfl.t → string;
  end;

value factor : I.t → list I.t;

value ios : string → int;
value soi : int → string;

value not_impl : string → α → β;
