(* $Id: SandBox.v,v 2.127 2013-11-29 13:43:36 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Nbar.
Require Import Misc.
(*
Require Import Field.
*)
Require Import Series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_add_compat.

Set Implicit Arguments.

(*
Section fld.

Variable α : Type.
Variable fld : Field.t α.
Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (Field.eq fld a b) (at level 70).
Notation "a ≈ b" := (eq_ps fld a b) (at level 70).
Notation "a ≐ b" := (eq_norm_ps fld a b) (at level 70).

Delimit Scope fld_scope with fld.
Notation "0" := (Field.zero fld) : fld_scope.
Notation "1" := (Field.one fld) : fld_scope.
*)

(* ps_mul *)

Definition nz_mul nz₁ nz₂ :=
  {| nz_terms :=
       series_mul (nz_terms nz₁) (nz_terms nz₂);
     nz_valnum :=
       (nz_valnum nz₁ * ' nz_comden nz₂ + nz_valnum nz₂ * ' nz_comden nz₁)%Z;
     nz_comden :=
       nz_comden nz₁ * nz_comden nz₂ |}.

Definition ps_mul (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => NonZero (nz_mul nz₁ nz₂)
      | Zero => ps₂
      end
  | Zero => ps₁
  end.

Delimit Scope ps_scope with ps.
Notation "a + b" := (ps_add fld a b) : ps_scope.
Notation "a * b" := (ps_mul a b) : ps_scope.

Lemma nz_norm_mul_comm : ∀ nz₁ nz₂,
  normalise_nz (nz_mul nz₁ nz₂) ≐ normalise_nz (nz_mul nz₂ nz₁).
Proof.
intros nz₁ nz₂.
unfold normalise_nz; simpl.
rewrite series_mul_comm.
remember (series_mul (nz_terms nz₂) (nz_terms nz₁)) as x.
remember (null_coeff_range_length fld x 0) as n eqn:Hn .
symmetry in Hn; subst x.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; constructor; simpl.
 unfold gcd_nz; simpl.
 rewrite series_mul_comm.
 f_equal; [ f_equal; apply Z.add_comm | f_equal ].
 f_equal; [ f_equal; apply Z.add_comm | idtac ].
 rewrite Pos.mul_comm; reflexivity.

 rewrite Pos.mul_comm, series_mul_comm.
 unfold gcd_nz; simpl.
 do 3 f_equal.
 f_equal; [ f_equal; apply Z.add_comm | idtac ].
 rewrite Pos.mul_comm; reflexivity.

 unfold gcd_nz; simpl.
 rewrite Pos.mul_comm, series_mul_comm.
 remember (nz_valnum nz₁ * ' nz_comden nz₂)%Z as x eqn:Hx .
 remember (nz_valnum nz₂ * ' nz_comden nz₁)%Z as y eqn:Hy .
 replace (x + y)%Z with (y + x)%Z by apply Z.add_comm.
 reflexivity.
Qed.

Theorem ps_mul_comm : ∀ ps₁ ps₂, ps_mul ps₁ ps₂ ≈ ps_mul ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_mul; simpl.
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
 constructor.
 apply nz_norm_mul_comm.

 destruct ps₂; reflexivity.
Qed.

Lemma fold_series_1 :
  {| terms := λ _, Lfield.one fld; stop := 1 |} = series_1.
Proof. reflexivity. Qed.

Theorem ps_mul_1_l : ∀ ps, ps_mul ps_one ps ≈ ps.
Proof.
intros ps; simpl.
destruct ps as [nz| ]; [ constructor | reflexivity ].
unfold normalise_nz; simpl.
rewrite fold_series_1, series_mul_1_l.
remember (null_coeff_range_length fld (nz_terms nz) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; constructor; simpl.
 rewrite series_mul_1_l.
 unfold gcd_nz; simpl.
 rewrite Z.mul_1_r; reflexivity.

 rewrite series_mul_1_l.
 unfold gcd_nz; simpl.
 rewrite Z.mul_1_r; reflexivity.

 rewrite series_mul_1_l.
 unfold gcd_nz; simpl.
 rewrite Z.mul_1_r; reflexivity.
Qed.

Theorem ps_mul_1_r : ∀ ps, ps_mul ps ps_one ≈ ps.
Proof. intros ps. rewrite ps_mul_comm. apply ps_mul_1_l. Qed.

Theorem ps_mul_0_l : ∀ ps, ps_mul ps_zero ps ≈ ps_zero.
Proof. intros ps; constructor. Qed.

Theorem ps_mul_0_r : ∀ ps, ps_mul ps ps_zero ≈ ps_zero.
Proof. intros ps. rewrite ps_mul_comm. apply ps_mul_0_l. Qed.

Theorem ps_neq_1_0 : not (ps_one ≈ ps_zero).
Proof.
intros H.
inversion_clear H.
inversion_clear H0.
pose proof (H O) as H₁.
unfold series_nth_fld in H₁.
simpl in H₁.
destruct (Nbar.lt_dec 0 0) as [H₂| H₂].
 revert H₂; apply Nbar.lt_irrefl.

 destruct (Nbar.lt_dec 0 1) as [H₃| H₃].
  apply Lfield.neq_1_0 in H₁; contradiction.

  apply H₃, Nbar.lt_0_1.
Qed.

Theorem ps_mul_assoc : ∀ ps₁ ps₂ ps₃,
  ps_mul ps₁ (ps_mul ps₂ ps₃) ≈ ps_mul (ps_mul ps₁ ps₂) ps₃.
Proof.
intros ps₁ ps₂ ps₃.
unfold ps_mul; simpl.
destruct ps₁ as [nz₁| ]; [ idtac | reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
destruct ps₃ as [nz₃| ]; [ constructor | reflexivity ].
unfold normalise_nz; simpl.
rewrite series_mul_assoc.
remember (series_mul (nz_terms nz₁) (nz_terms nz₂)) as s₁₂.
remember (series_mul s₁₂ (nz_terms nz₃)) as s₁₂₃; subst s₁₂.
remember (null_coeff_range_length fld s₁₂₃ 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; constructor; simpl.
 rewrite series_mul_assoc, <- Heqs₁₂₃.
 unfold gcd_nz; simpl.
 f_equal.
  apply Z.add_cancel_r.
  do 2 rewrite Pos2Z.inj_mul; ring.

  do 2 f_equal.
   do 2 rewrite Pos2Z.inj_mul; ring.

   rewrite Pos.mul_assoc; reflexivity.

 rewrite series_mul_assoc, <- Heqs₁₂₃.
 do 2 f_equal.
  do 4 rewrite Pos2Z.inj_mul.
  rewrite Z.mul_assoc; reflexivity.

  unfold gcd_nz; simpl.
  do 2 f_equal.
   do 2 rewrite Pos2Z.inj_mul; ring.

   rewrite Pos.mul_assoc; reflexivity.

 rewrite series_mul_assoc, <- Heqs₁₂₃.
 apply eq_series_eq.
 do 2 f_equal.
 unfold gcd_nz; simpl.
 do 2 f_equal.
  do 2 rewrite Pos2Z.inj_mul; ring.

  rewrite Pos.mul_assoc; reflexivity.
Qed.

Lemma eq_nz_mul_compat_r : ∀ nz₁ nz₂ nz₃,
  eq_nz nz₁ nz₂
  → eq_nz (nz_mul nz₁ nz₃) (nz_mul nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃ Heq.
induction Heq.
constructor; simpl.
 rewrite H, H0; reflexivity.

 rewrite H0; reflexivity.

 rewrite H1; reflexivity.
Qed.

Lemma eq_nz_mul_compat_l : ∀ nz₁ nz₂ nz₃,
  eq_nz nz₁ nz₂
  → eq_nz (nz_mul nz₃ nz₁) (nz_mul nz₃ nz₂).
Proof.
intros nz₁ nz₂ nz₃ Heq.
induction Heq.
constructor; simpl.
 rewrite H, H0; reflexivity.

 rewrite H0; reflexivity.

 rewrite H1; reflexivity.
Qed.

Lemma series_mul_stretch_mul_inf : ∀ a b k,
  series_mul (series_stretch k a) b
  ≃ series_mul_inf (series_stretch k (series_inf fld a))
      (series_inf fld b).
Proof.
intros a b l.
constructor; intros k.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin k) ∞) as [H| H]; [ clear H | exfalso ].
 remember (stop a * fin (Pos.to_nat l) + stop b)%Nbar as x.
 destruct (Nbar.lt_dec (fin k) x) as [H₁| H₁]; subst x.
  unfold convol_mul, convol_mul_inf.
  apply sigma_compat; intros i Hi.
  apply sigma_compat; intros j Hj.
  rewrite <- Lfield.mul_assoc.
  destruct (eq_nat_dec (i + j) k) as [H₂| H₂].
   rewrite H₂, delta_id.
   do 2 rewrite Lfield.mul_1_l.
   simpl.
   destruct (zerop (i mod Pos.to_nat l)) as [H₃| H₃].
    apply Nat.mod_divides in H₃; auto.
    destruct H₃ as (c, Hc).
    rewrite Hc.
    rewrite series_nth_fld_mul_stretch.
    rewrite Nat.mul_comm.
    rewrite Nat.div_mul; auto.
    rewrite series_nth_inf.
    reflexivity.

    rewrite shifted_in_stretched; [ reflexivity | assumption ].

   rewrite delta_neq; [ idtac | assumption ].
   do 2 rewrite Lfield.mul_0_l; reflexivity.

  symmetry.
  apply Nbar.nlt_ge in H₁.
  unfold convol_mul_inf.
  apply all_0_sigma_0; intros i.
  apply all_0_sigma_0; intros j.
  destruct (eq_nat_dec (i + j) k) as [H₂| H₂].
   rewrite H₂, delta_id.
   rewrite Lfield.mul_1_l.
   simpl.
   destruct (zerop (i mod Pos.to_nat l)) as [H₃| H₃].
    apply Nat.mod_divides in H₃; auto.
    destruct H₃ as (c, Hc).
    rewrite Hc.
    rewrite Nat.mul_comm.
    rewrite Nat.div_mul; auto.
    rewrite series_nth_inf.
    simpl.
    unfold series_nth_fld; simpl.
    destruct (Nbar.lt_dec (fin c) (stop a)) as [H₃| H₃].
     destruct (Nbar.lt_dec (fin j) (stop b)) as [H₄| H₄].
      rewrite <- H₂ in H₁.
      rewrite Nbar.fin_inj_add in H₁.
      apply Nbar.nlt_ge in H₁.
      exfalso; apply H₁.
      apply Nbar.lt_trans with (m := (fin i + stop b)%Nbar).
       apply Nbar.add_lt_mono_l; [ idtac | assumption ].
       intros H; discriminate H.

       remember (stop b) as st eqn:Hst .
       symmetry in Hst.
       destruct st as [st| ].
        apply Nbar.add_lt_mono_r; [ intros H; discriminate H | idtac ].
        rewrite Hc.
        rewrite Nbar.fin_inj_mul.
        rewrite Nbar.mul_comm.
        apply Nbar.mul_lt_mono_pos_r.
         apply Nbar.fin_lt_mono, Pos2Nat.is_pos.

         intros H; discriminate H.

         intros H; discriminate H.

         assumption.

        exfalso; apply H₁; simpl.
        rewrite Nbar.add_comm; constructor.

      rewrite Lfield.mul_0_r; reflexivity.

     rewrite Lfield.mul_0_l; reflexivity.

    rewrite Lfield.mul_0_l; reflexivity.

   rewrite delta_neq; [ idtac | assumption ].
   do 2 rewrite Lfield.mul_0_l; reflexivity.

 apply H; constructor.
Qed.

(*
Notation "'Σ' ( i = b , e ) ' ' f" := (sigma fld b e (λ i, f))
  (at level 0, i at level 0, b at level 0, e at level 0, f at level 60).
Lemma inserted_0_sigma : ∀ f g k n,
  (∀ i, i mod n ≠ O → f i ≍ 0%fld)
  → (∀ i, f (n * i)%nat ≍ g i)
    → Σ (i = 0, k * n)   f i ≍ Σ (i = 0, k)   g i.
Proof.
intros f g k n Hf Hfg.
bbb.
*)

(* faux ; exemple pour k > 1 :
   - terme de gauche : a₀b₀ + 0 x + ...
   - terme de droite : a₀b₀ + a₀b₁x + ...
Lemma zzz : ∀ a b k,
  series_stretch k (series_mul a b)
  ≃ series_mul (series_stretch k a) b.
Proof.
intros a b k.
rewrite series_mul_stretch_mul_inf.
rewrite series_mul_mul_inf.
remember (series_inf fld a) as aa eqn:Haa .
remember (series_inf fld b) as bb eqn:Hbb .
constructor; intros i.
rewrite series_nth_mul_inf; simpl.
destruct (zerop (i mod Pos.to_nat k)) as [H₁| H₁].
 apply Nat.mod_divides in H₁; auto.
 destruct H₁ as (j, Hj).
 rewrite Hj in |- * at 1.
 rewrite series_nth_fld_mul_stretch.
 rewrite series_nth_mul_inf.
 unfold series_mul_inf; simpl.
 unfold convol_mul_inf.
 rewrite Nat.mul_comm in Hj; rewrite Hj.
bbb.
 rewrite inserted_0_sigma.
*)

(* faux car nécessite lemme zzz ci-dessus, lequel est faux
Lemma normalise_nz_adjust_nz_mul_0_r : ∀ nz₁ nz₂ k,
  normalise_nz (nz_mul nz₁ nz₂) ≐
  normalise_nz (nz_mul (adjust_nz 0 k nz₁) nz₂).
Proof.
intros nz₁ nz₂ k.
rewrite nz_adjust_eq with (n := O) (k := k).
unfold nz_mul; simpl.
unfold adjust_nz; simpl.
do 2 rewrite Z.sub_0_r.
rewrite Pos2Z.inj_mul, Z.mul_assoc.
rewrite Z.mul_shuffle0.
rewrite <- Z.mul_add_distr_r.
rewrite Pos_mul_shuffle0.
do 2 rewrite series_shift_0.
apply normalise_nz_morph.
constructor; try reflexivity; simpl.
bbb.
*)

(* faux car faux pour n = 0 du lemme ci-dessus qui est faux
Lemma normalise_nz_adjust_nz_mul_r : ∀ nz₁ nz₂ n k,
  normalise_nz (nz_mul nz₁ nz₂) ≐
  normalise_nz (nz_mul (adjust_nz n k nz₁) nz₂).
Proof.
intros nz₁ nz₂ n k.
rewrite nz_adjust_eq with (n := n) (k := k).
unfold nz_mul; simpl.
unfold adjust_nz; simpl.
symmetry.
rewrite Pos2Z.inj_mul, Z.mul_assoc.
rewrite Z.mul_sub_distr_r.
rewrite Z.mul_shuffle0.
rewrite <- Z.add_sub_swap.
rewrite <- Z.mul_add_distr_r.
rewrite Pos_mul_shuffle0.
bbb.
assert
 (series_mul (series_shift n (series_stretch k (nz_terms nz₁)))
    (nz_terms nz₂) ≃
  series_shift n
    (series_stretch k (series_mul (nz_terms nz₁) (nz_terms nz₂)))).
 Focus 2.
 rewrite H.
bbb.

intros nz₁ nz₂ n k.
rewrite eq_norm_ps_mul_adjust_0_l with (k := k).
apply normalise_nz_adjust_nz_mul.
bbb.
*)

(* exercice *)
Lemma yyy : ∀ nz n,
  normalise_nz nz ≐ normalise_nz (nz_mul (nz_monom 1%fld (Qnat n)) nz).
Proof.
intros nz n.
unfold nz_mul; simpl.
rewrite series_mul_1_l, Z.mul_1_r.
bbb.

(* exercice *)
Lemma zzz : ∀ nz n k,
  normalise_nz nz
  ≐ normalise_nz (nz_mul (nz_monom 1%fld (Qnat n)) (adjust_nz 0 k nz)).
Proof.
intros nz n k.
bbb.

Lemma nz_norm_mul_compat_r : ∀ nz₁ nz₂ nz₃,
  normalise_nz nz₁ ≐ normalise_nz nz₂
  → normalise_nz (nz_mul nz₁ nz₃) ≐ normalise_nz (nz_mul nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃ Heq.
remember (normalise_nz nz₁) as ps₁ eqn:Hps₁ .
remember (normalise_nz nz₂) as ps₂ eqn:Hps₂ .
symmetry in Hps₁, Hps₂.
destruct ps₁ as [nz'₁| ].
 destruct ps₂ as [nz'₂| ]; [ idtac | inversion Heq ].
 remember Hps₁ as H; clear HeqH.
 apply normalised_exists_adjust in H.
 destruct H as (n₁, (k₁, H)).
 apply eq_nz_mul_compat_r with (nz₃ := nz₃) in H.
 rewrite H; clear H.
 remember Hps₂ as H; clear HeqH.
 apply normalised_exists_adjust in H.
 destruct H as (n₂, (k₂, H)).
 apply eq_nz_mul_compat_r with (nz₃ := nz₃) in H.
 rewrite H; clear H.
 rewrite nz_norm_mul_comm; symmetry.
 rewrite nz_norm_mul_comm; symmetry.
 remember (normalise_nz nz₃) as ps₃ eqn:Hps₃ .
 symmetry in Hps₃.
 destruct ps₃ as [nz'₃| ].
  remember Hps₃ as H; clear HeqH.
  apply normalised_exists_adjust in H.
  destruct H as (n₃, (k₃, H)).
  remember H as H₁; clear HeqH₁.
  apply eq_nz_mul_compat_r with (nz₃ := adjust_nz n₁ k₁ nz'₁) in H₁.
  rewrite H₁; clear H₁.
  remember H as H₁; clear HeqH₁.
  apply eq_nz_mul_compat_r with (nz₃ := adjust_nz n₂ k₂ nz'₂) in H₁.
  rewrite H₁; clear H₁.
  unfold nz_mul; simpl.
  inversion Heq; subst.
  inversion H2; subst.
  rewrite <- H0, <- H1, <- H3.
bbb.

Theorem ps_mul_compat_r : ∀ ps₁ ps₂ ps₃,
  ps₁ ≈ ps₂
  → (ps₁ * ps₃)%ps ≈ (ps₂ * ps₃)%ps.
Proof.
intros ps₁ ps₂ ps₃ H₁₂.
destruct ps₃ as [nz₃| ]; [ idtac | do 2 rewrite ps_mul_0_r; reflexivity ].
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ]; [ idtac | simpl ].
  constructor.
  apply nz_norm_mul_compat_r.
  inversion H₁₂; assumption.
bbb.

Definition ps_fld α : Lfield.t (puiseux_series α) :=
  {| Lfield.zero := @ps_zero α;
     Lfield.one := @ps_one α fld;
     Lfield.add := @ps_add α fld;
     Lfield.mul := @ps_mul;
     Lfield.opp := @ps_opp α fld;
(*
     Lfield.inv := 0;
*)
     Lfield.eq := @eq_ps α fld;
     Lfield.eq_refl := @eq_ps_refl α fld;
     Lfield.eq_sym := @eq_ps_sym α fld;
     Lfield.eq_trans := @eq_ps_trans α fld;
     Lfield.neq_1_0 := @ps_neq_1_0;
     Lfield.add_comm := @ps_add_comm α fld;
     Lfield.add_assoc := @ps_add_assoc α fld;
     Lfield.add_0_l := @ps_add_0_l α fld;
     Lfield.add_opp_l := @ps_add_opp_l α fld;
     Lfield.add_compat_l := @ps_add_compat_l α fld;
     Lfield.mul_comm := @ps_mul_comm;
     Lfield.mul_assoc := @ps_mul_assoc;
     Lfield.mul_1_l := @ps_mul_1_l;
     Lfield.mul_compat_l := @ps_mul_compat_l
(*
     Lfield.mul_inv_l := 0;
     Lfield.mul_add_distr_l := 0
*)
   |}.

End fld.

Add Parametric Morphism α (fld : Lfield.t α) : (ps_mul fld)
with signature eq_ps fld ==> eq_ps fld ==> eq_ps fld
as ps_mul_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
bbb.
