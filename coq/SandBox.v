(* $Id: SandBox.v,v 2.88 2013-11-20 00:46:21 deraugla Exp $ *)

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

Definition δ i j := if eq_nat_dec i j then one fld else zero fld.

Fixpoint sigma_aux b len f :=
  match len with
  | O => f b
  | S len₁ => add fld (f b) (sigma_aux (S b) len₁ f)
  end.

Definition sigma b e f := sigma_aux b (e - b) f.

Notation "'Σ' ( i = b ) ' ' e f" := (sigma b e (λ i, f))
  (at level 0, i at level 0, b at level 0, e at level 0, f at level 10).

Definition convol_mul a b k :=
  Σ (i = 0)   k Σ (j = 0)   k
    (mul fld (δ (i + j) k)
       (mul fld (series_nth_fld fld i a) (series_nth_fld fld j b))).

Definition series_mul a b :=
  {| terms k := convol_mul a b k;
     stop := Nbar.add (stop a) (stop b) |}.

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

Lemma sigma_sigma_comm : ∀ f i₀ i₁ j₀ j₁,
  Σ (i = i₀)   i₁ Σ (j = j₀)   j₁ (f i j)
  ≍ Σ (j = j₀)   j₁ Σ (i = i₀)   i₁ (f i j).
Proof.
Abort. (*
bbb.
*)

bbb.
faire un fld_mul_shuffle0 !

Lemma sigma_sigma_mul_mul_comm : ∀ a b i₁ i₂ j₁ j₂ k,
  Σ (i = i₁)   i₂
  Σ (j = j₁)   j₂
  mul fld (δ (i + j) k)
    (mul fld (series_nth_fld fld i a) (series_nth_fld fld j b))
  ≍ Σ (j = j₁)   j₂
    Σ (i = i₁)   i₂
    mul fld (δ (j + i) k)
      (mul fld (series_nth_fld fld j b) (series_nth_fld fld i a)).
Proof.
intros.
unfold sigma; simpl.
revert i₁ j₁ j₂.
induction i₂; intros; [ simpl | idtac ].
 revert i₁ j₁.
 induction j₂; intros; [ simpl | idtac ].
  rewrite Nat.add_comm.
  remember (series_nth_fld fld i₁ a) as x.
  remember (series_nth_fld fld j₁ b) as y.
  remember (mul fld x y) as z.
  assert (z ≍ mul fld x y) as H by (subst; reflexivity).
  rewrite fld_mul_comm in H.
  rewrite H; reflexivity.

  destruct j₁.
   Focus 1.
   rewrite Nat.sub_0_r.
   simpl.
   rewrite Nat.add_0_r.
   (* ouille *)
bbb.
*)

Lemma series_mul_comm : ∀ a b, series_mul a b ≃ series_mul b a.
Proof.
intros a b.
constructor; intros k.
unfold series_nth_fld; simpl.
rewrite Nbar.add_comm.
destruct (Nbar.lt_dec (fin k) (stop b + stop a)) as [H₁| H₁].
 unfold convol_mul.
 apply sigma_sigma_mul_mul_comm.

 reflexivity.
qed.

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
