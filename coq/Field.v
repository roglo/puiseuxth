(* $Id: Field.v,v 1.4 2013-07-08 20:14:43 deraugla Exp $ *)

Require Import Utf8.

Set Implicit Arguments.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    mul : α → α → α;
    fld_eq : α → α → bool;
    add_comm : ∀ a b, fld_eq (add a b) (add b a) = true;
    fld_eq_refl : ∀ a, fld_eq a a = true }.
