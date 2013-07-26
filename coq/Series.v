(* $Id: Series.v,v 1.19 2013-07-26 15:28:40 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Require Import Field.

Set Implicit Arguments.

CoInductive series α :=
  | Term : α → series α → series α
  | End : series α.

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

CoInductive eq_series α fld (s₁ s₂ : series α) : Prop :=
  | eq_ser_term : ∀ hd₁ hd₂ tl₁ tl₂,
      s₁ = Term hd₁ tl₁
      → s₂ = Term hd₂ tl₂
        → fld_eq fld hd₁ hd₂ = true
          → eq_series fld tl₁ tl₂
            → eq_series fld s₁ s₂
  | eq_ser_end :
      s₁ = End _
      → s₂ = End _
        → eq_series fld s₁ s₂.

Theorem eq_series_refl : ∀ α (fld : field α), reflexive _ (eq_series fld).
Proof.
cofix IHs.
intros α fld s.
destruct s as [t s₂| ].
 eapply eq_ser_term; try reflexivity.
  apply fld_eq_refl.

  apply IHs.

 apply eq_ser_end; reflexivity.
Qed.

Theorem eq_series_sym : ∀ α (fld : field α), symmetric _ (eq_series fld).
Proof.
cofix IHs.
intros α fld s₁ s₂ H.
destruct s₁ as [t₁ s₁| ], s₂ as [t₂ s₂| ].
 eapply eq_ser_term; try reflexivity.
  inversion H; [ idtac | discriminate H0 ].
  injection H0; clear H0; intros; subst hd₁ tl₁.
  injection H1; clear H1; intros; subst hd₂ tl₂.
  rewrite fld_eq_sym; assumption.

  apply IHs.
  inversion H; [ idtac | discriminate H0 ].
  injection H0; clear H0; intros; subst hd₁ tl₁.
  injection H1; clear H1; intros; subst hd₂ tl₂.
  assumption.

 inversion H; [ discriminate H1 | discriminate H0 ].

 inversion H; [ discriminate H0 | discriminate H1 ].

 apply eq_series_refl.
Qed.

Theorem eq_series_trans : ∀ α (fld : field α), transitive _ (eq_series fld).
Proof.
cofix IHs.
intros α fld s₁ s₂ s₃ H₁ H₂.
inversion H₁; subst; [ idtac | assumption ].
inversion H₂; subst; [ idtac | discriminate H ].
inversion H; subst.
eapply eq_ser_term; try reflexivity.
 eapply fld_eq_trans; eassumption.

 eapply IHs; eassumption.
Qed.

Add Parametric Relation α (fld : field α) : (series α) (eq_series fld)
 reflexivity proved by (eq_series_refl fld)
 symmetry proved by (eq_series_sym (fld := fld))
 transitivity proved by (eq_series_trans (fld := fld))
 as eq_series_rel.

Lemma series_eta : ∀ α (s : series α),
  s = (match s with Term t₁ s₁ => Term t₁ s₁ | End => End _ end).
Proof.
intros α s.
destruct s; reflexivity.
Qed.

Lemma series_forall_inv : ∀ α (P : α → Prop) t s,
  series_forall P (Term t s)
  → P t ∧ series_forall P s.
Proof.
intros α P t s H.
inversion H; [ idtac | discriminate H0 ].
injection H0; intros; subst s t; split; assumption.
Qed.

Lemma series_forall_map : ∀ α (P Q : _ → Prop) (s : series α),
  (∀ x, P x → Q x) → series_forall P s → series_forall Q s.
Proof.
cofix IHs.
intros α P Q s Hx H.
destruct s as [t₁ s₁| ].
 apply series_forall_inv in H.
 destruct H as (H₁, H₂).
 eapply TermAndFurther; [ reflexivity | apply Hx, H₁ | idtac ].
 eapply IHs; eassumption.

 constructor; reflexivity.
Qed.
