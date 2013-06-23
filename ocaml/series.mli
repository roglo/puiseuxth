(* $Id: series.mli,v 1.2 2013-06-23 17:03:51 deraugla Exp $ *)

type series α =
  [ Term of α and Lazy.t (series α)
  | End ]
;

value series_nth : int → series α → option α;
value series_map : (α → β) → series α → series β;
