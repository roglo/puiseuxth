(* $Id: Field.v,v 1.9 2013-07-26 09:21:09 deraugla Exp $ *)

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
    fld_eq_sym : ∀ a b,
      fld_eq a b = fld_eq b a;
    fld_add_comm : ∀ a b,
      fld_eq (add a b) (add b a) = true;
    fld_add_assoc : ∀ a b c,
      fld_eq (add (add a b) c) (add a (add b c)) = true }.
