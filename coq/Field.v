(* $Id: Field.v,v 1.3 2013-07-08 15:05:40 deraugla Exp $ *)

Require Import Utf8.

Set Implicit Arguments.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    mul : α → α → α;
    fld_eq : α → α → bool;
    add_comm : ∀ a b, fld_eq (add a b) (add b a) = true }.
