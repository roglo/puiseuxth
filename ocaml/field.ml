(* $Id: field.ml,v 1.1 2013-03-28 20:01:35 deraugla Exp $ *)

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
    to_string : α → string }
;
