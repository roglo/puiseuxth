(* $Id: Series.v,v 1.10 2013-06-19 16:29:38 deraugla Exp $ *)

Require Import Utf8.

Set Implicit Arguments.

Inductive series α :=
  | Term : α → (unit → series α) → series α
  | End : series α.

Definition series_hd α (s : series α) :=
  match s with
  | Term a _ => Some a
  | End => None
  end.

Definition series_tl α (s : series α) : option (series α) :=
  match s with
  | Term _ t => Some (t tt)
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

Fixpoint series_map α β (f : α → β) s :=
  match s with
  | Term a t => Term (f a) (λ tt, series_map f (t tt))
  | End => End _
  end.

Lemma series_eta : ∀ α (s : series α),
  s = (match s with Term t₁ s₁ => Term t₁ s₁ | End => End _ end).
Proof.
intros α s.
destruct s; reflexivity.
Qed.

Inductive series_forall α P (s : series α) : Prop :=
  | TermAndFurther : ∀ a t,
      s = Term a t → P a → series_forall P (t tt) → series_forall P s
  | EndOk :
      s = End _ → series_forall P s.

Lemma series_forall_inv : ∀ α (P : α → Prop) t s,
  series_forall P (Term t s)
  → P t ∧ series_forall P (s tt).
Proof.
intros α P t s H.
inversion H; [ idtac | discriminate H0 ].
injection H0; intros; subst s t; split; assumption.
Qed.

Lemma series_forall_map : ∀ α (P Q : _ → Prop) (s : series α),
  (∀ x, P x → Q x) → series_forall P s → series_forall Q s.
Proof.
intros α P Q s Hx H.
induction s as [t₁ s₁ IHs| ].
 apply series_forall_inv in H.
 destruct H as (H₁, H₂).
 eapply TermAndFurther; [ reflexivity | apply Hx, H₁ | idtac ].
 eapply IHs; eassumption.

 constructor; reflexivity.
Qed.
