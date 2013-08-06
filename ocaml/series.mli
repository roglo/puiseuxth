(* $Id: series.mli,v 1.6 2013-08-06 14:19:15 deraugla Exp $ *)

type series α =
  { terms : int → α;
    stop : option int }
;
value terms : series α → int → α;
value stop : series α → option int;

type coseries α =
  [ Term of α and Lazy.t (coseries α)
  | End ]
;

value coseries_nth : int → coseries α → option α;
value coseries_map : (α → β) → coseries α → coseries β;
