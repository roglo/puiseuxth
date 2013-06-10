(* $Id: Lcm.v,v 1.2 2013-06-10 19:50:58 deraugla Exp $ *)

(*
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
*)
