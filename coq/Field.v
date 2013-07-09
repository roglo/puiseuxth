(* $Id: Field.v,v 1.5 2013-07-09 04:29:10 deraugla Exp $ *)

Require Import Utf8.

Set Implicit Arguments.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    mul : α → α → α;
    fld_eq : α → α → bool;
    fld_eq_refl : ∀ a, fld_eq a a = true;
    fld_eq_comm : ∀ a b, fld_eq a b = fld_eq b a;
    add_comm : ∀ a b, fld_eq (add a b) (add b a) = true }.
