(* $Id: series.mli,v 1.1 2013-06-23 16:46:04 deraugla Exp $ *)

type series α =
  [ Term of α and Lazy.t (series α)
  | End ]
;

(*
value series_hd : series α → option α;
value series_tl : series α → option (series α);
value series_nth_tl : int → series α → option (series α);
*)
value series_nth : int → series α → option α;
value series_map : (α → β) → series α → series β;
