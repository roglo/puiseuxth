(* $Id: series.ml,v 1.6 2013-08-06 14:19:15 deraugla Exp $ *)

#load "./pa_coq.cmo";

Record series α :=
  { terms : nat → α;
    stop : option nat }.

CoInductive coseries α :=
  | Term : α → coseries α → coseries α
  | End : coseries α.

Definition coseries_hd α (s : coseries α) :=
  match s with
  | Term a _ => Some a
  | End => None
  end.

Definition coseries_tl α (s : coseries α) : option (coseries α) :=
  match s with
  | Term _ t => Some t
  | End => None
  end.

Fixpoint coseries_nth_tl α (n : nat) (s : coseries α) : option (coseries α) :=
  match n with
  | O => Some s
  | S m =>
      match coseries_tl s with
      | None => None
      | Some t => coseries_nth_tl m t
      end
  end.

Definition coseries_nth α (n : nat) (s : coseries α) : option α :=
  match coseries_nth_tl n s with
  | None => None
  | Some t => coseries_hd t
  end.

CoFixpoint coseries_map α β (f : α → β) s :=
  match s with
  | Term a t => Term (f a) (coseries_map f t)
  | End => End _
  end.
