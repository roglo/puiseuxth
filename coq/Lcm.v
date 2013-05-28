(* $Id: Lcm.v,v 1.1 2013-05-28 18:36:40 deraugla Exp $ *)

Require Import Utf8.
Require Import Arith.

Fixpoint f_nlcm (n a b x y : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      if lt_dec x y then f_nlcm n' a b (x + a) y
      else if lt_dec y x then f_nlcm n' a b x (y + b)
      else x
  end.

Definition lcm (a b : nat) : nat := f_nlcm (a * b) a b a b.
