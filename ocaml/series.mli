(* $Id: series.mli,v 1.5 2013-08-06 09:04:25 deraugla Exp $ *)

open Field;

type series α =
  { terms : int → α;
    stop : option int }
;
value terms : series α → int → α;
value stop : series α → option int;

value series_nth : int → series α → option α;
