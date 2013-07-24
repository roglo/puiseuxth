(* $Id: Series.v,v 1.16 2013-07-24 15:15:47 deraugla Exp $ *)

Require Import Utf8.

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

CoInductive EqSer α equ (s₁ s₂ : series α) : Prop :=
  | eq_ser_term : ∀ hd₁ hd₂ tl₁ tl₂,
      s₁ = Term hd₁ tl₁
      → s₂ = Term hd₂ tl₂
        → equ hd₁ hd₂ = true
          → EqSer equ tl₁ tl₂
            → EqSer equ s₁ s₂
  | eq_ser_end :
      s₁ = End _
      → s₂ = End _
        → EqSer equ s₁ s₂.

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
