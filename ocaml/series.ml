(* $Id: series.ml,v 1.5 2013-08-06 09:04:25 deraugla Exp $ *)

#load "./pa_coq.cmo";

Record series α :=
  { terms : nat → α;
    stop : option nat }.

Definition series_nth α n (s : series α) :=
  match stop s with
  | Some st => if lt_dec n st then Some (terms s n) else None
  | None => None
  end.
