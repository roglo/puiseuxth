(* $Id: series.mli,v 1.10 2013-08-07 08:20:06 deraugla Exp $ *)

open Field;

type series α =
  { terms : int → α;
    stop : option int }
;
value terms : series α → int → α;
value stop : series α → option int;

value series_nth : int → series α → option α;
value series_add : field α _ → series α → series α → series α;

(* *)

type coseries α =
  [ Term of α and Lazy.t (coseries α)
  | End ]
;

value coseries_nth : int → coseries α → option α;
value coseries_map : (α → β) → coseries α → coseries β;

value series_of_coseries : field α _ → coseries α → series α;
value coseries_of_series : series α → coseries α;
