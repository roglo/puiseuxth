(* $Id: Field.v,v 1.1 2013-06-23 16:52:46 deraugla Exp $ *)

Require Import Utf8.

Set Implicit Arguments.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    mul : α → α → α;
    is_zero : α → bool }.
