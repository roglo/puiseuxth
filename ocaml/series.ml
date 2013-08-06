(* $Id: series.ml,v 1.4 2013-08-06 08:36:17 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Field;

Record series α :=
  { terms : nat → α;
    stop : option nat }.

Definition series_nth α n (s : series α) :=
  match stop s with
  | Some st => if lt_dec n st then Some (terms s n) else None
  | None => None
  end.

Definition series_add fld s₁ s₂ :=
  {| terms i := add fld (terms s₁ i) (terms s₂ i);
     stop :=
       match stop s₁ with
       | Some st₁ =>
           match stop s₂ with
           | Some st₂ => Some (max st₁ st₂)
           | None => None
           end
       | None => None
       end |}.
