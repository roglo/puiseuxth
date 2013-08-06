(* $Id: series.mli,v 1.8 2013-08-06 19:27:56 deraugla Exp $ *)

type series α =
  { terms : int → α;
    stop : option int }
;
value terms : series α → int → α;
value stop : series α → option int;

value series_nth : int → series α → option α;

type coseries α =
  [ Term of α and Lazy.t (coseries α)
  | End ]
;

value coseries_nth : int → coseries α → option α;
value coseries_map : (α → β) → coseries α → coseries β;

open Field;

value series_of_coseries : field α _ → coseries α → series α;
