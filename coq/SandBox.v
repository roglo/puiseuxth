(* $Id: SandBox.v,v 2.82 2013-11-19 14:16:11 deraugla Exp $ *)

Require Import Utf8.
Require Import ZArith.
Require Import NPeano.

Require Import Nbar.
Require Import Field.
Require Import Series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_add_compat.

Set Implicit Arguments.

Section fld.

Variable α : Type.
Variable fld : field α.
Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≈ b" := (eq_ps fld a b) (at level 70).
Notation "a ≐ b" := (eq_norm_ps fld a b) (at level 70).

(* ps_mul *)

Fixpoint convol_mul k j s₁ s₂ :=
  match j with
  | O =>
      mul fld (series_nth_fld fld k s₁) (series_nth_fld fld O s₂)
  | S j₁ =>
      add fld
        (mul fld (series_nth_fld fld (k - j) s₁) (series_nth_fld fld j s₂))
        (convol_mul k j₁ s₁ s₂)
  end.

Fixpoint convol_comm_mul k i s₁ s₂ :=
  match i with
  | O =>
      mul fld (series_nth_fld fld 0 s₁) (series_nth_fld fld k s₂)
  | S i₁ =>
      add fld
        (mul fld (series_nth_fld fld i s₁) (series_nth_fld fld (k - i) s₂))
        (convol_comm_mul k i₁ s₁ s₂)
  end.

Definition series_mul s₁ s₂ :=
  {| terms k := convol_mul k k s₁ s₂;
     stop := Nbar.add (stop s₁) (stop s₂) |}.

Definition nz_mul nz₁ nz₂ :=
  {| nz_terms := series_mul (nz_terms nz₁) (nz_terms nz₂);
     nz_valnum := (nz_valnum nz₁ * nz_valnum nz₂)%Z;
     nz_comden := nz_comden nz₁ * nz_comden nz₂ |}.

Definition ps_mul (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => NonZero (nz_mul nz₁ nz₂)
      | Zero => ps₂
      end
  | Zero => ps₁
  end.

(* faux.
Lemma yyy : ∀ s₁ s₂ i k, convol_mul k i s₁ s₂ ≍ convol_comm_mul k i s₁ s₂.
Proof.
bbb.
*)

Lemma convol_mul_comm : ∀ s₁ s₂ j k,
  convol_mul k j s₁ s₂ ≍ convol_comm_mul k j s₂ s₁.
Proof.
intros s₁ s₂ j k.
induction j; simpl.
 rewrite fld_mul_comm; reflexivity.

 rewrite IHj.
 rewrite fld_mul_comm; reflexivity.
Qed.

Lemma series_mul_comm : ∀ s₁ s₂, series_mul s₁ s₂ ≃ series_mul s₂ s₁.
Proof.
series_mul_comm < Show Script.
intros s₁ s₂.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.add_comm.
destruct (Nbar.lt_dec (fin i) (stop s₂ + stop s₁)) as [H₁| H₁].
 rewrite convol_mul_comm.
bbb.

Lemma nz_norm_mul_comm : ∀ nz₁ nz₂,
  normalise_nz fld (nz_mul nz₁ nz₂) ≐ normalise_nz fld (nz_mul nz₂ nz₁).
Proof.
intros nz₁ nz₂.
unfold normalise_nz; simpl.
bbb.

Theorem ps_mul_comm : ∀ ps₁ ps₂, ps_mul ps₁ ps₂ ≈ ps_mul ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_mul; simpl.
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
 constructor.
 apply nz_norm_mul_comm.

 destruct ps₂; reflexivity.
qed.

Theorem ps_mul_ident : ∀ ps, ps_mul (ps_one fld) ps ≈ ps.
Proof.
intros ps.
unfold ps_mul; simpl.
destruct ps as [nz| ]; [ idtac | reflexivity ].
unfold cm_factor; simpl.
rewrite Z.mul_1_r.
apply eq_non_zero_ps with (k₁ := xH) (k₂ := xH); try reflexivity; simpl.
rewrite series_stretch_1.
rewrite series_stretch_1 in |- * at 2.
apply eq_series_base; simpl.
bbb.
 intros i.
 destruct i; simpl.
  unfold series_nth; simpl.
  rewrite Nat.add_0_r.
  destruct (lt_dec 0 (Pos.to_nat (nz_comden nz))) as [H| H].
   rewrite Nbar.mul_1_r.
   remember (stop (nz_terms nz)) as st.
   destruct st as [st| ]; simpl.
    destruct (lt_dec 0 st) as [H₁| H₁].
     rewrite Nat.mod_0_l; simpl.
      rewrite fld_mul_ident; reflexivity.

      apply Pos2Nat_ne_0.

     apply not_gt in H₁.
     apply Nat.le_0_r in H₁.
     subst st.
Focus 1.
bbb.

intros ps.
unfold ps_mul; simpl.
destruct ps as [nz| ]; [ idtac | reflexivity ].
unfold cm_factor; simpl.
rewrite Z.mul_1_r.
constructor 1 with (k₁ := xH) (k₂ := xH); try reflexivity; simpl.
rewrite series_stretch_1.
rewrite series_stretch_1 in |- * at 2.
constructor; simpl.
 intros i.
 remember
  (sum_mul_coeff fld 1 i
     (series_stretch fld (Pos.to_nat (nz_comden nz))
        {| terms := λ _ : nat, one fld; stop := 1 |})
     (series_stretch fld (Pos.to_nat 1) (nz_terms nz))) as x.
 symmetry in Heqx.
 destruct x as [x| ].
  unfold series_nth; simpl.
  rewrite Nat.add_0_r.
  destruct (lt_dec 0 (Pos.to_nat (nz_comden nz))) as [| Bad].
   rewrite Nbar.mul_1_r.
   remember (stop (nz_terms nz)) as st.
   symmetry in Heqst.
   destruct st as [st| ].
    destruct (lt_dec i st) as [H| H].
     rewrite Nat.mod_0_l; [ simpl | apply Pos2Nat_ne_0 ].
     rewrite divmod_div.
     rewrite Nat.div_1_r.
     rewrite fld_mul_ident.
bbb.

Definition ps_fld : field (puiseux_series α) :=
  {| zero := ps_zero;
     one := ps_one;
     add := ps_add fld;
     mul := ps_mul fld;
     fld_eq := eq_ps fld;
     fld_eq_refl := eq_ps_refl fld;
     fld_eq_sym := eq_ps_sym (fld := fld);
     fld_eq_trans := eq_ps_trans (fld := fld);
     fld_add_comm := ps_add_comm;
     fld_add_assoc := ps_add_assoc;
     fld_add_0_l := ps_add_ident;
     fld_add_compat := ps_add_compat;
     fld_mul_ident := ps_mul_ident |}.

End fld₄.
