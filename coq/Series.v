(* $Id: Series.v,v 1.24 2013-07-26 23:43:22 deraugla Exp $ *)

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

CoInductive eq_series α fld : series α → series α → Prop :=
  | eq_ser_term : ∀ t₁ t₂ s₁ s₂,
      fld_eq fld t₁ t₂
      → eq_series fld s₁ s₂
        → eq_series fld (Term t₁ s₁) (Term t₂ s₂)
  | eq_ser_end :
      eq_series fld (End _) (End _).

Lemma eq_series_inv_term : ∀ α (fld : field α) t₁ t₂ s₁ s₂,
  eq_series fld (Term t₁ s₁) (Term t₂ s₂)
  → fld_eq fld t₁ t₂ ∧ eq_series fld s₁ s₂.
Proof.
intros α fld t₁ t₂ s₁ s₂ H.
inversion H; split; assumption.
Qed.

Lemma eq_series_inv_term_end : ∀ α (fld : field α) t s,
  ¬ eq_series fld (Term t s) (End _).
Proof.
intros α fld t s H.
inversion H; contradiction.
Qed.

Lemma eq_series_inv_end_term : ∀ α (fld : field α) t s,
  ¬ eq_series fld (End _) (Term t s).
Proof.
intros α fld t s H.
inversion H; contradiction.
Qed.

Lemma eq_series_inv : ∀ α (fld : field α) s₁ s₂,
  eq_series fld s₁ s₂
  → (∃ t₁ t₂ s₃ s₄,
     s₁ = Term t₁ s₃ ∧ s₂ = Term t₂ s₄ ∧
     fld_eq fld t₁ t₂ ∧ eq_series fld s₃ s₄)
    ∨ (s₁ = End _ ∧ s₂ = End _).
Proof.
intros α fld s₁ s₂ H.
inversion H; [ left | right ].
 exists t₁, t₂, s₁0, s₂0.
 split; [ reflexivity | idtac ].
 split; [ reflexivity | idtac ].
 split; assumption.

 split; reflexivity.
Qed.

Theorem eq_series_refl : ∀ α (fld : field α), reflexive _ (eq_series fld).
Proof.
cofix IHs.
intros α fld s.
destruct s as [t s₂| ].
 eapply eq_ser_term; try reflexivity; [ apply fld_eq_refl | apply IHs ].

 apply eq_ser_end; reflexivity.
Qed.

Theorem eq_series_sym : ∀ α (fld : field α), symmetric _ (eq_series fld).
Proof.
cofix IHs.
intros α fld s₁ s₂ H.
destruct s₁ as [t₁ s₁| ], s₂ as [t₂ s₂| ].
 eapply eq_ser_term; try reflexivity.
  apply eq_series_inv_term in H; destruct H.
  apply fld_eq_sym; assumption.

  apply eq_series_inv_term in H; destruct H.
  apply IHs; assumption.

 apply eq_series_inv_term_end in H; contradiction.

 apply eq_series_inv_end_term in H; contradiction.

 assumption.
Qed.

Theorem eq_series_trans : ∀ α (fld : field α), transitive _ (eq_series fld).
Proof.
cofix IHs.
intros α fld s₁ s₂ s₃ H₁ H₂.
inversion H₁; subst; [ idtac | assumption ].
inversion H₂; subst; constructor.
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

CoFixpoint series_add α (fld : field α) s₁ s₂ :=
  match s₁ with
  | Term c₁ ss₁ =>
      match s₂ with
      | Term c₂ ss₂ => Term (add fld c₁ c₂) (series_add fld ss₁ ss₂)
      | End => s₁
      end
  | End => s₂
  end.

Lemma series_add_comm : ∀ α (fld : field α) s₁ s₂,
  eq_series fld (series_add fld s₁ s₂) (series_add fld s₂ s₁).
Proof.
cofix IHs; intros.
rewrite series_eta.
remember (series_add fld s₁ s₂) as x.
rewrite series_eta in Heqx; subst x.
simpl.
destruct s₁ as [t₁ s₃| ].
 destruct s₂ as [t₂ s₄| ].
  constructor; try reflexivity; [ apply fld_add_comm | apply IHs ].

  constructor; try reflexivity; apply fld_eq_refl.

 destruct s₂; reflexivity.
Qed.

Lemma series_add_assoc : ∀ α (fld : field α) s₁ s₂ s₃,
  eq_series fld
    (series_add fld (series_add fld s₁ s₂) s₃)
    (series_add fld s₁ (series_add fld s₂ s₃)).
Proof.
cofix IHs; intros.
rewrite series_eta; symmetry.
rewrite series_eta; symmetry.
simpl.
destruct s₁ as [t₁ ss₁| ].
 destruct s₂ as [t₂ ss₂| ].
  destruct s₃ as [t₃ ss₃| ].
   constructor.
    apply fld_add_assoc.

    Focus 1.
bbb.
