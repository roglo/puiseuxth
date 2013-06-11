(* $Id: Series.v,v 1.8 2013-06-11 02:45:05 deraugla Exp $ *)

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

Lemma series_eta : ∀ α (s : series α),
  s = (match s with Term t₁ s₁ => Term t₁ s₁ | End => End _ end).
Proof.
intros α s.
destruct s; reflexivity.
Qed.

CoInductive series_forall α P (s : series α) : Prop :=
  | TermAndFurther : ∀ a t,
      s = Term a t → P a → series_forall P t → series_forall P s
  | EndOk :
      s = End _ → series_forall P s.

Lemma series_forall_inv : ∀ α (P : α → Prop) t s,
  series_forall P (Term t s)
  → P t ∧ series_forall P s.
Proof.
intros α P t s H.
inversion H; [ idtac | discriminate H0 ].
injection H0; intros; subst s t; split; assumption.
Qed.
