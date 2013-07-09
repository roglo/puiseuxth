(* $Id: Field.v,v 1.8 2013-07-09 20:16:39 deraugla Exp $ *)

Require Import Utf8.

Set Implicit Arguments.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    mul : α → α → α;
    fld_eq : α → α → bool;
    fld_eq_refl : ∀ a,
      fld_eq a a = true;
    fld_eq_comm : ∀ a b,
      fld_eq a b = fld_eq b a;
    fld_add_comm : ∀ a b,
      fld_eq (add a b) (add b a) = true;
    fld_add_assoc : ∀ a b c,
      fld_eq (add (add a b) c) (add a (add b c)) = true }.
