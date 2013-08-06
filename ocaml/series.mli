(* $Id: series.mli,v 1.4 2013-08-06 08:36:17 deraugla Exp $ *)

open Field;

type series α =
  { terms : int → α;
    stop : option int }
;
value terms : series α → int → α;
value stop : series α → option int;

value series_nth : int → series α → option α;
value series_add : field α _ → series α → series α → series α;
