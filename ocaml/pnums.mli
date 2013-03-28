(* $Id: pnums.mli,v 1.2 2013-03-28 16:07:39 deraugla Exp $ *)

open Pnums_sig;

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

value complex_zero : complex;
value complex_mul : complex → complex → complex;
value complex_power : complex → complex → complex;
value complex_to_string : bool → complex → string;

module C : Csig with type i = I.t and type q = Q.t and type a₂ = A₂.t;

value factor : I.t → list I.t;

value ios : string → int;
value soi : int → string;

value not_impl : string → α → β;
