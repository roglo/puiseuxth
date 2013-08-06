(* $Id: series.mli,v 1.3 2013-08-06 06:12:49 deraugla Exp $ *)

type series α =
  { terms : int → α;
    stop : option int }
;

value series_nth : int → series α → option α;
