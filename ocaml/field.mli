(* $Id: field.mli,v 1.2 2013-03-28 20:10:11 deraugla Exp $ *)

open Pnums;

type field α =
  { zero : α;
    one : α;
    add : α → α → α;
    sub : α → α → α;
    neg : α → α;
    mul : α → α → α;
    div : α → α → α;
    (* extra *)
    minus_one : α;
    norm : α → α;
    eq : α → α → bool;
    imul : int → α → α;
    neg_factor : α → option α;
    of_i : I.t → α;
    to_string : α → string }
;
