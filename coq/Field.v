(* $Id: Field.v,v 1.12 2013-07-28 04:46:39 deraugla Exp $ *)

Require Import Utf8.

Set Implicit Arguments.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    mul : α → α → α;
    fld_eq : α → α → Prop;
    fld_eq_refl : ∀ a, fld_eq a a;
    fld_eq_sym : ∀ a b, fld_eq a b → fld_eq b a;
    fld_eq_trans : ∀ a b c, fld_eq a b → fld_eq b c → fld_eq a c;
    fld_add_comm : ∀ a b, fld_eq (add a b) (add b a);
    fld_add_assoc : ∀ a b c, fld_eq (add (add a b) c) (add a (add b c));
    fld_add_neutral : ∀ a, fld_eq (add zero a) a }.
