(* $Id: Series.v,v 1.7 2013-06-10 12:29:07 deraugla Exp $ *)

Require Import Utf8.

Set Implicit Arguments.

CoInductive series α := Term : α → series α → series α | End : series α.

Definition series_hd α (s : series α) :=
  match s with
  | Term a _ => Some a
  | End => None
  end.

Definition series_tl α (s : series α) : option (series α) :=
  match s with
  | Term _ t => Some t
  | End => None
  end.

Fixpoint series_nth_tl α (n : nat) (s : series α) : option (series α) :=
  match n with
  | O => Some s
  | S m =>
      match series_tl s with
      | None => None
      | Some t => series_nth_tl m t
      end
  end.

Definition series_nth α (n : nat) (s : series α) : option α :=
  match series_nth_tl n s with
  | None => None
  | Some t => series_hd t
  end.

CoFixpoint series_map α β (f : α → β) s :=
  match s with
  | Term a t => Term (f a) (series_map f t)
  | End => End _
  end.

CoInductive series_forall α P (s : series α) : Prop :=
  | TermAndFurther : ∀ a t,
      s = Term a t → P a → series_forall P t → series_forall P s
  | EndOk :
      s = End _ → series_forall P s.
