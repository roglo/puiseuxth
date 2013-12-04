(* $Id: Puiseux_series.v,v 2.77 2013-12-04 11:03:11 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Series.
Require Import Nbar.

Set Implicit Arguments.

Section Axioms.

(* [null_coeff_range_length rng s n] returns the number of consecutive
   null coefficients in the series [s], from the [n]th one. *)
Definition null_coeff_range_length : ∀ α, Lfield.r α → series α → nat → Nbar.
Admitted.

Definition null_coeff_range_length_prop s n v :=
  match v with
  | fin k =>
      (∀ i, (i < k)%nat → (series_nth_rng rng (n + i) s = 0)%rng) ∧
      (series_nth_rng rng (n + k) s ≠ 0)%rng
  | ∞ =>
      (∀ i, (series_nth_rng rng (n + i) s = 0)%rng)
  end.

Axiom null_coeff_range_length_iff : ∀ s n v,
  null_coeff_range_length rng s n = v ↔ null_coeff_range_length_prop s n v.

(* [greatest_series_x_power rng s n] returns the greatest nat value [k]
   such that [s], starting at index [n], is a series in [x^k]. *)
Definition greatest_series_x_power : ∀ α,
  Lfield.r α → series α → nat → positive.
Admitted.

Fixpoint nth_null_coeff_range_length s n b :=
  match null_coeff_range_length rng s (S b) with
  | fin p =>
      match n with
      | O => S p
      | S n₁ => nth_null_coeff_range_length s n₁ (S b + p)%nat
      end
  | ∞ => O
  end.

Definition is_a_series_in_x_power s b k :=
  ∀ n, (Pos.to_nat k | nth_null_coeff_range_length s n b).

Definition is_the_greatest_series_x_power s b k :=
  is_a_series_in_x_power s b k ∧
  (∀ k', (k < k')%positive
   → ∃ n, ¬(Pos.to_nat k' | nth_null_coeff_range_length s n b)).

Axiom greatest_series_x_power_iff : ∀ s n k,
  greatest_series_x_power rng s n = k ↔
  is_the_greatest_series_x_power s n k.

End Axioms.

Definition series_stretch k s :=
  {| terms i :=
       if zerop (i mod Pos.to_nat k) then
         series_nth_rng rng (i / Pos.to_nat k) s
       else 0%rng;
     stop :=
       stop s * fin (Pos.to_nat k) |}.

Definition series_shift n s :=
  {| terms i := if lt_dec i n then 0%rng else terms s (i - n);
     stop := stop s + fin n |}.

Record nz_ps α := mknz
  { nz_terms : series α;
    nz_valnum : Z;
    nz_comden : positive }.

Inductive puiseux_series α :=
  | NonZero : nz_ps α → puiseux_series α
  | Zero : puiseux_series α.

Definition series_shrink k (s : series α) :=
  {| terms i := terms s (i * Pos.to_nat k);
     stop := Nbar.div_sup (stop s) (fin (Pos.to_nat k)) |}.

Definition series_left_shift n (s : series α) :=
  {| terms i := terms s (n + i);
     stop := stop s - fin n |}.

Definition normalise_series n k (s : series α) :=
  series_shrink k (series_left_shift n s).

Definition gcd_nz n k (nz : nz_ps α) :=
  Z.gcd (Z.gcd (nz_valnum nz + Z.of_nat n) (' nz_comden nz)) (' k).

Definition normalise_nz nz :=
  match null_coeff_range_length rng (nz_terms nz) 0 with
  | fin n =>
      let k := greatest_series_x_power rng (nz_terms nz) n in
      let g := gcd_nz n k nz in
      NonZero
        {| nz_terms := normalise_series n (Z.to_pos g) (nz_terms nz);
           nz_valnum := (nz_valnum nz + Z.of_nat n) / g;
           nz_comden := Z.to_pos (' nz_comden nz / g) |}
  | ∞ =>
      Zero _
  end.

(*
Definition normalise_ps ps :=
  match ps with
  | NonZero nz => normalise_nz nz
  | Zero => ps
  end.
*)

Inductive eq_nz : nz_ps α → nz_ps α → Prop :=
  | eq_nz_base : ∀ nz₁ nz₂,
      nz_valnum nz₁ = nz_valnum nz₂
      → nz_comden nz₁ = nz_comden nz₂
        → (nz_terms nz₁ = nz_terms nz₂)%ser
          → eq_nz nz₁ nz₂.

Inductive eq_norm_ps : puiseux_series α → puiseux_series α → Prop :=
  | eq_norm_ps_base : ∀ nz₁ nz₂,
      eq_nz nz₁ nz₂ → eq_norm_ps (NonZero nz₁) (NonZero nz₂)
  | eq_norm_ps_zero :
      eq_norm_ps (Zero _) (Zero _).

Inductive eq_ps : puiseux_series α → puiseux_series α → Prop :=
  | eq_ps_base : ∀ nz₁ nz₂,
      eq_norm_ps (normalise_nz nz₁) (normalise_nz nz₂)
      → eq_ps (NonZero nz₁) (NonZero nz₂)
  | eq_ps_zero_r : ∀ nz,
      eq_series (nz_terms nz) series_0
      → eq_ps (NonZero nz) (Zero _)
  | eq_ps_zero_l : ∀ nz,
      eq_series (nz_terms nz) series_0
      → eq_ps (Zero _) (NonZero nz)
  | eq_ps_zero :
      eq_ps (Zero _) (Zero _).

Definition ps_zero : puiseux_series α := Zero _.

Definition nz_monom (c : α) pow :=
  {| nz_terms := {| terms i := c; stop := 1 |};
     nz_valnum := Qnum pow;
     nz_comden := Qden pow |}.

Definition ps_monom c pow := NonZero (nz_monom c pow).
Definition ps_const c : puiseux_series α := ps_monom c 0.
Definition ps_one := ps_const 1%rng.

Definition nz_zero :=
  {| nz_terms := series_0;
     nz_valnum := 0;
     nz_comden := 1 |}.

Notation "a ≐ b" := (eq_norm_ps a b) (at level 70).

Delimit Scope nz_scope with nz.
Notation "a = b" := (eq_nz a b) : nz_scope.
Notation "a ≠ b" := (not (eq_nz a b)) : nz_scope.
Notation "0" := nz_zero : nz_scope.

Delimit Scope ps_scope with ps.
Notation "a = b" := (eq_ps a b) : ps_scope.
Notation "a ≠ b" := (not (eq_ps a b)) : ps_scope.
Notation "0" := ps_zero : ps_scope.
Notation "1" := ps_one : ps_scope.

(*
Definition series_head (s : series α) :=
  {| terms := terms s; stop := 1 |}.

Definition series_tail (s : series α) :=
  {| terms i := terms s (S i); stop := stop s - 1 |}.

Definition nz_head nz :=
  match stop (nz_terms nz) with
  | fin 0 => nz
  | _ =>
      {| nz_terms := series_head (nz_terms nz);
         nz_valnum := nz_valnum nz;
         nz_comden := nz_comden nz |}
  end.

Definition nz_tail nz :=
  match stop (nz_terms nz) with
  | fin 0 => nz
  | _ =>
      {| nz_terms := series_tail (nz_terms nz);
         nz_valnum := nz_valnum nz + 1;
         nz_comden := nz_comden nz |}
  end.

Theorem null_series : ∀ s,
  series_nth 0 s = None
  → ∀ i : nat, series_nth_rng rng i s = 0%rng.
Proof.
intros s H i.
unfold series_nth_rng; simpl.
unfold series_nth in H.
remember (stop s) as st; symmetry in Heqst.
destruct st as [st| ]; [ idtac | discriminate H ].
destruct (lt_dec 0 st) as [Hlt| Hge]; [ discriminate H | clear H ].
apply not_gt in Hge.
apply Nat.le_0_r in Hge.
subst st.
destruct (Nbar.lt_dec (fin i) 0) as [Hlt| ]; [ idtac | reflexivity ].
inversion Hlt as [a b H d e| ]; subst.
exfalso; revert H; apply Nat.nle_succ_0.
Qed.
*)

Lemma series_stretch_1 : ∀ s, (series_stretch 1 s = s)%ser.
Proof.
intros s.
unfold series_stretch; simpl.
constructor; intros i.
unfold series_nth_rng; simpl.
rewrite divmod_div, Nbar.mul_1_r, Nat.div_1_r.
destruct (Nbar.lt_dec (fin i) (stop s)); reflexivity.
Qed.

Theorem eq_nz_refl : reflexive _ eq_nz.
Proof. intros nz; constructor; reflexivity. Qed.

Theorem eq_nz_sym : symmetric _ eq_nz.
Proof. intros nz₁ nz₂ H; induction H; constructor; symmetry; assumption. Qed.

Theorem eq_nz_trans : transitive _ eq_nz.
Proof.
intros nz₁ nz₂ nz₃ H₁ H₂.
induction H₁, H₂.
constructor; etransitivity; eassumption.
Qed.

Theorem eq_norm_ps_refl : reflexive _ eq_norm_ps.
Proof.
intros ps.
destruct ps as [nz| ]; [ idtac | constructor ].
constructor; constructor; reflexivity.
Qed.

Theorem eq_norm_ps_sym : symmetric _ eq_norm_ps.
Proof.
intros ps₁ ps₂ H.
induction H; constructor; apply eq_nz_sym; assumption.
Qed.

Theorem eq_norm_ps_trans : transitive _ eq_norm_ps.
Proof.
intros ps₁ ps₂ ps₃ H₁ H₂.
inversion H₁; subst.
 inversion H₂; subst; constructor.
 eapply eq_nz_trans; eassumption.

 inversion H₂; subst; constructor.
Qed.

(*
Lemma series_inf_shift : ∀ a n,
  (series_inf rng (series_shift n a) = series_shift n (series_inf rng a))%ser.
Proof.
intros a n.
constructor; intros i.
unfold series_nth_rng; simpl.
unfold series_nth_rng; simpl.
destruct (Nbar.lt_dec (fin i) ∞) as [H₁| H₁]; [ clear H₁ | exfalso ].
 destruct (lt_dec i n) as [H₂| H₂].
  destruct (Nbar.lt_dec (fin i) (stop a + fin n)); reflexivity.

  apply Nat.nlt_ge in H₂.
  destruct (Nbar.lt_dec (fin i) (stop a + fin n)) as [H₃| H₃].
   destruct (Nbar.lt_dec (fin (i - n)) (stop a)) as [H₄| H₄].
    reflexivity.

    exfalso; apply H₄.
    rewrite Nbar.fin_inj_sub.
    apply Nbar.lt_add_lt_sub_l; [ idtac | assumption ].
    apply Nbar.le_fin; assumption.

   destruct (Nbar.lt_dec (fin (i - n)) (stop a)) as [H₄| H₄].
    exfalso; apply H₃.
    apply Nbar.lt_sub_lt_add_r; [ idtac | assumption ].
    intros H; discriminate H.

    reflexivity.

 apply H₁; constructor.
Qed.
*)

(* mmmm... probablement faux... à réfléchir...
Lemma zzz : ∀ a b n k,
  series_mul rng (series_shift n (series_stretch k a)) b
  ≃ series_shift n (series_stretch k (series_mul rng a b)).
Proof.
intros a b n k.
rewrite series_inf_eq; symmetry.
rewrite series_inf_eq; symmetry.
rewrite series_inf_mul; symmetry.
rewrite series_inf_shift.
constructor; intros i.
unfold series_nth_rng; simpl.
destruct (Nbar.lt_dec (fin i) ∞) as [H₁| H₁]; [ clear H₁ | exfalso ].
 destruct (lt_dec i n) as [H₁| H₁].
  symmetry.
  unfold convol_mul_inf.
  apply all_0_sigma_0; intros l.
  apply all_0_sigma_0; intros j.
  simpl.
  destruct (eq_nat_dec (l + j) i) as [H₂| H₂].
   rewrite H₂, delta_id, Lfield.mul_1_l.
   unfold series_nth_rng at 1.
   remember terms as f; simpl; subst f.
   remember (stop a * fin (Pos.to_nat k) + fin n)%Nbar as x.
   destruct (Nbar.lt_dec (fin l) x) as [H₃| H₃]; subst x.
    simpl.
    destruct (lt_dec l n) as [H₄| H₄].
     rewrite Lfield.mul_0_l; reflexivity.

     exfalso; omega.

    rewrite Lfield.mul_0_l; reflexivity.

   rewrite delta_neq; [ idtac | assumption ].
   do 2 rewrite Lfield.mul_0_l; reflexivity.

  symmetry.
  apply Nat.nlt_ge in H₁.
*)

Add Parametric Relation : (nz_ps α) eq_nz
 reflexivity proved by eq_nz_refl
 symmetry proved by eq_nz_sym
 transitivity proved by eq_nz_trans
 as eq_nz_rel.

Add Parametric Relation : (puiseux_series α) eq_norm_ps
 reflexivity proved by eq_norm_ps_refl
 symmetry proved by eq_norm_ps_sym
 transitivity proved by eq_norm_ps_trans
 as eq_norm_ps_rel.

Lemma mul_lt_mono_positive_r : ∀ a b c,
  (fin a < b)%Nbar
  → (fin (a * Pos.to_nat c) < b * fin (Pos.to_nat c))%Nbar.
Proof.
intros a b c Hab.
rewrite Nbar.fin_inj_mul.
apply Nbar.mul_lt_mono_pos_r.
 constructor; apply Pos2Nat.is_pos.

 intros H; discriminate H.

 intros H; discriminate H.

 assumption.
Qed.

Add Parametric Morphism : (@mknz α)
  with signature eq_series ==> eq ==> eq ==> eq_nz
  as mknz_morphism.
Proof.
intros a b Hab v n.
constructor; auto.
Qed.

Add Parametric Morphism : (null_coeff_range_length rng)
  with signature eq_series ==> eq ==> eq
  as null_coeff_range_length_morph.
Proof.
intros s₁ s₂ Heq n.
remember (null_coeff_range_length rng s₁ n) as n₁ eqn:Hn₁ .
remember (null_coeff_range_length rng s₂ n) as n₂ eqn:Hn₂ .
symmetry in Hn₁, Hn₂.
apply null_coeff_range_length_iff in Hn₁.
apply null_coeff_range_length_iff in Hn₂.
destruct n₁ as [n₁| ].
 destruct Hn₁ as (Hiz₁, Hnz₁).
 destruct n₂ as [n₂| ].
  destruct Hn₂ as (Hiz₂, Hnz₂).
  apply Nbar.fin_inj_wd.
  destruct (lt_eq_lt_dec n₁ n₂) as [[Hlt| Hneq]| Hgt].
   exfalso; apply Hnz₁.
   rewrite Heq.
   apply Hiz₂; assumption.

   assumption.

   exfalso; apply Hnz₂.
   rewrite <- Heq.
   apply Hiz₁; assumption.

  exfalso; apply Hnz₁; rewrite Heq; apply Hn₂.

 destruct n₂ as [n₂| ]; [ idtac | reflexivity ].
 destruct Hn₂ as (Hiz₂, Hnz₂).
 exfalso; apply Hnz₂; rewrite <- Heq; apply Hn₁.
Qed.

(*
Add Parametric Morphism α (rng : Lfield.t α) :
    (greatest_series_x_power_lim rng)
  with signature eq ==> (eq_series rng) ==> eq ==> eq
  as greatest_series_x_power_lim_morph.
Proof.
intros cnt s₁ s₂ Heq n.
revert n.
induction cnt; intros; [ reflexivity | simpl ].
rewrite Heq.
remember (null_coeff_range_length rng s₂ (S n)) as p eqn:Hp .
symmetry in Hp.
destruct p as [p| ]; [ idtac | reflexivity ].
rewrite IHcnt; reflexivity.
Qed.
*)

Add Parametric Morphism : nth_null_coeff_range_length
  with signature eq_series ==> eq ==> eq ==> eq
  as nth_null_coeff_range_length_morph.
Proof.
intros s₁ s₂ Heq c n.
revert n.
induction c; intros; simpl; rewrite Heq; [ reflexivity | idtac ].
destruct (null_coeff_range_length rng s₂ (S n)); [ apply IHc | reflexivity ].
Qed.

Add Parametric Morphism : (greatest_series_x_power rng)
  with signature eq_series ==> eq ==> eq
  as greatest_series_x_power_morph.
Proof.
intros s₁ s₂ Heq n.
remember (greatest_series_x_power rng s₂ n) as k eqn:Hk .
symmetry in Hk.
apply greatest_series_x_power_iff in Hk.
apply greatest_series_x_power_iff.
unfold is_the_greatest_series_x_power in Hk |- *.
destruct Hk as (Hz, Hnz).
split.
 intros cnt.
 rewrite Heq; apply Hz.

 intros k₁ Hk₁.
 apply Hnz in Hk₁.
 destruct Hk₁ as (m, Hm).
 exists m; rewrite Heq; assumption.
Qed.

Add Parametric Morphism : series_stretch
  with signature eq ==> eq_series ==> eq_series
  as stretch_morph.
Proof.
intros kp s₁ s₂ Heq.
inversion Heq; subst.
clear Heq; rename H into Heq.
constructor; simpl.
intros i.
unfold series_nth_rng; simpl.
unfold series_nth_rng; simpl.
unfold series_nth_rng in Heq; simpl in Heq.
remember (Pos.to_nat kp) as k.
assert (k ≠ O) as Hk by (subst k; apply Pos2Nat_ne_0).
destruct (zerop (i mod k)) as [Hz| Hnz].
 apply Nat.mod_divides in Hz; [ idtac | assumption ].
 destruct Hz as (c, Hi).
 subst i.
 pose proof (Heq c) as Hc.
 rewrite Nat.mul_comm.
 rewrite Nat.div_mul; [ idtac | assumption ].
 destruct (Nbar.lt_dec (fin (c * k)) (stop s₁ * fin k)) as [Hlt₁| Hge₁].
  destruct (Nbar.lt_dec (fin c) (stop s₂)) as [Hlt₄| Hge₄].
   destruct (Nbar.lt_dec (fin (c * k)) (stop s₂ * fin k)) as [Hlt₃| Hge₃].
    assumption.

    exfalso; apply Hge₃; subst k.
    apply mul_lt_mono_positive_r; assumption.

   destruct (Nbar.lt_dec (fin (c * k)) (stop s₂ * fin k)); assumption.

  destruct (Nbar.lt_dec (fin (c * k)) (stop s₂ * fin k)) as [Hlt₂| ].
   destruct (Nbar.lt_dec (fin c) (stop s₂)) as [Hlt₃| ].
    destruct (Nbar.lt_dec (fin c) (stop s₁)) as [Hlt₄| ].
     exfalso; apply Hge₁; subst k.
     apply mul_lt_mono_positive_r; assumption.

     assumption.

    reflexivity.

   reflexivity.

 destruct (Nbar.lt_dec (fin i) (stop s₁ * fin k)).
  destruct (Nbar.lt_dec (fin i) (stop s₂ * fin k)); reflexivity.

  destruct (Nbar.lt_dec (fin i) (stop s₂ * fin k)); reflexivity.
Qed.

Add Parametric Morphism : series_shrink
  with signature eq ==> eq_series ==> eq_series
  as shrink_morph.
Proof.
intros n s₁ s₂ Heq.
constructor; intros.
unfold series_nth_rng; simpl.
do 2 rewrite Nbar.fold_sub, Nbar.fold_div, Nbar.fold_div_sup.
inversion Heq; subst.
clear Heq; rename H into Heq.
unfold series_nth_rng in Heq; simpl in Heq.
remember (Pos.to_nat n) as nn eqn:Hnn .
symmetry in Hnn.
pose proof (Heq (i * nn)%nat) as Hin.
destruct (Nbar.lt_dec (fin i) (Nbar.div_sup (stop s₁) (fin nn))) as [H₁| H₁].
 destruct (Nbar.lt_dec (fin (i * nn)) (stop s₁)) as [H₃| H₃].
  destruct (Nbar.lt_dec (fin i) (Nbar.div_sup (stop s₂) (fin nn)))
   as [H₂| H₂].
   destruct (Nbar.lt_dec (fin (i * nn)) (stop s₂)) as [H₄| H₄].
    assumption.

    exfalso; apply H₄.
    rewrite Nbar.fin_inj_mul.
    apply Nbar.lt_div_sup_lt_mul_r; assumption.

   destruct (Nbar.lt_dec (fin (i * nn)) (stop s₂)) as [H₄| H₄].
    exfalso; apply H₂.
    rewrite Nbar.fin_inj_mul in H₄.
    apply Nbar.lt_mul_r_lt_div_sup; [ idtac | assumption ].
    destruct nn; [ exfalso; revert Hnn; apply Pos2Nat_ne_0 | idtac ].
    apply Nbar.lt_fin, Nat.lt_succ_r, Nat.le_0_l.

    assumption.

  exfalso; apply H₃.
  rewrite Nbar.fin_inj_mul.
  apply Nbar.lt_div_sup_lt_mul_r; assumption.

 destruct (Nbar.lt_dec (fin (i * nn)) (stop s₁)) as [H₃| H₃].
  exfalso; apply H₁.
  rewrite Nbar.fin_inj_mul in H₃.
  apply Nbar.lt_mul_r_lt_div_sup; [ idtac | assumption ].
  destruct nn; [ exfalso; revert Hnn; apply Pos2Nat_ne_0 | idtac ].
  apply Nbar.lt_fin.
  apply Nat.lt_succ_r, Nat.le_0_l.

  destruct (Nbar.lt_dec (fin i) (Nbar.div_sup (stop s₂) (fin nn)))
   as [H₂| H₂].
   destruct (Nbar.lt_dec (fin (i * nn)) (stop s₂)) as [H₄| H₄].
    assumption.

    exfalso; apply H₄.
    rewrite Nbar.fin_inj_mul.
    apply Nbar.lt_div_sup_lt_mul_r; assumption.

   reflexivity.
Qed.

Add Parametric Morphism : series_shift
  with signature eq ==> eq_series ==> eq_series
  as series_shift_morph.
Proof.
intros n s₁ s₂ Heq.
constructor; intros i.
inversion Heq; subst.
unfold series_nth_rng; simpl.
unfold series_nth_rng in H; simpl in H.
pose proof (H (i - n)%nat) as Hi; clear H.
destruct (lt_dec i n) as [Hlt| Hge].
 destruct (Nbar.lt_dec (fin i) (stop s₁ + fin n)) as [Hlt₁| Hge₁].
  destruct (Nbar.lt_dec (fin i) (stop s₂ + fin n)); reflexivity.

  destruct (Nbar.lt_dec (fin i) (stop s₂ + fin n)); reflexivity.

 apply not_gt in Hge.
 remember (i - n)%nat as m.
 assert (m + n = i)%nat by (subst m; apply Nat.sub_add; assumption).
 subst i; clear Heqm Hge.
 destruct (Nbar.lt_dec (fin (m + n)) (stop s₁ + fin n)) as [Hlt₁| Hge₁].
  destruct (Nbar.lt_dec (fin (m + n)) (stop s₂ + fin n)) as [Hlt₂| Hge₂].
   destruct (Nbar.lt_dec (fin m) (stop s₁)) as [Hlt₃| Hge₃].
    destruct (Nbar.lt_dec (fin m) (stop s₂)) as [Hlt₄| Hge₄].
     assumption.

     exfalso; apply Hge₄; clear Hge₄.
     rewrite Nbar.fin_inj_add in Hlt₂.
     apply Nbar.add_lt_mono_r in Hlt₂; [ assumption | idtac ].
     intros H; discriminate H.

    exfalso; apply Hge₃; clear Hge₃.
    rewrite Nbar.fin_inj_add in Hlt₁.
    apply Nbar.add_lt_mono_r in Hlt₁; [ assumption | idtac ].
    intros H; discriminate H.

   destruct (Nbar.lt_dec (fin m) (stop s₁)) as [Hlt₃| Hge₃].
    destruct (Nbar.lt_dec (fin m) (stop s₂)) as [Hlt₄| Hge₄].
     exfalso; apply Hge₂; clear Hge₂.
     rewrite Nbar.fin_inj_add.
     apply Nbar.add_lt_mono_r; [ idtac | assumption ].
     intros H; discriminate H.

     assumption.

    exfalso; apply Hge₃; clear Hge₃.
    rewrite Nbar.fin_inj_add in Hlt₁.
    apply Nbar.add_lt_mono_r in Hlt₁; [ assumption | idtac ].
    intros H; discriminate H.

  destruct (Nbar.lt_dec (fin (m + n)) (stop s₂ + fin n)) as [Hlt₂| Hge₂].
   destruct (Nbar.lt_dec (fin m) (stop s₁)) as [Hlt₃| Hge₃].
    exfalso; apply Hge₁; clear Hge₁.
    rewrite Nbar.fin_inj_add.
    apply Nbar.add_lt_mono_r; [ idtac | assumption ].
    intros H; discriminate H.

    destruct (Nbar.lt_dec (fin m) (stop s₂)) as [Hlt₄| Hge₄].
     assumption.

     exfalso; apply Hge₄; clear Hge₄.
     rewrite Nbar.fin_inj_add in Hlt₂.
     apply Nbar.add_lt_mono_r in Hlt₂; [ assumption | idtac ].
     intros H; discriminate H.

   reflexivity.
Qed.

Add Parametric Morphism : normalise_series
  with signature eq ==> eq ==> eq_series ==> eq_series
  as normalise_morph.
Proof.
intros n k ps₁ ps₂ Heq.
constructor; intros i.
inversion Heq; subst.
unfold normalise_series.
unfold series_shrink, series_left_shift.
remember Nbar.div_sup as f; simpl; subst f.
do 2 rewrite Nbar.fold_sub.
pose proof (H (n + i * Pos.to_nat k)%nat) as Hi.
remember Nbar.div_sup as f.
unfold series_nth_rng in Hi |- *; simpl.
do 2 rewrite Nbar.fold_sub.
subst f.
remember (fin (Pos.to_nat k)) as fink.
remember (Nbar.div_sup (stop ps₁ - fin n) fink)%Nbar as d₁ eqn:Hd₁ .
remember (Nbar.div_sup (stop ps₂ - fin n) fink)%Nbar as d₂ eqn:Hd₂ .
subst fink.
destruct (Nbar.lt_dec (fin i) d₁) as [H₁| H₁]; subst d₁.
 destruct (Nbar.lt_dec (fin (n + i * Pos.to_nat k)) (stop ps₁)) as [H₂| H₂].
  destruct (Nbar.lt_dec (fin i) d₂) as [H₃| H₃]; subst d₂.
   destruct (Nbar.lt_dec (fin (n + i * Pos.to_nat k)) (stop ps₂)) as [H₄| H₄].
    assumption.

    exfalso; apply H₄.
    apply Nbar.lt_div_sup_lt_mul_r in H₃.
    rewrite Nbar.fin_inj_add, Nbar.add_comm.
    apply Nbar.lt_add_lt_sub_r.
    assumption.

   destruct (Nbar.lt_dec (fin (n + i * Pos.to_nat k)) (stop ps₂)) as [H₄| H₄].
    exfalso; apply H₃.
    apply Nbar.lt_mul_r_lt_div_sup.
     apply Nbar.fin_lt_mono, Pos2Nat.is_pos.

     apply Nbar.lt_add_lt_sub_r.
     rewrite Nbar.add_comm; assumption.

    assumption.

  exfalso; apply H₂.
  apply Nbar.lt_div_sup_lt_mul_r in H₁.
  rewrite Nbar.fin_inj_add, Nbar.add_comm.
  apply Nbar.lt_add_lt_sub_r.
  assumption.

 destruct (Nbar.lt_dec (fin (n + i * Pos.to_nat k)) (stop ps₁)) as [H₂| H₂].
  exfalso; apply H₁.
  apply Nbar.lt_mul_r_lt_div_sup.
   apply Nbar.fin_lt_mono, Pos2Nat.is_pos.

   apply Nbar.lt_add_lt_sub_r.
   rewrite Nbar.add_comm; assumption.

  destruct (Nbar.lt_dec (fin i) d₂) as [H₃| H₃]; subst d₂.
   destruct (Nbar.lt_dec (fin (n + i * Pos.to_nat k)) (stop ps₂)) as [H₄| H₄].
    assumption.

    exfalso; apply H₄.
    apply Nbar.lt_div_sup_lt_mul_r in H₃.
    rewrite Nbar.fin_inj_add, Nbar.add_comm.
    apply Nbar.lt_add_lt_sub_r.
    assumption.

   reflexivity.
Qed.

Add Parametric Morphism : normalise_nz
  with signature eq_nz ==> eq_norm_ps
  as normalise_nz_morph.
Proof.
intros nz₁ nz₂ Heq.
inversion Heq; subst.
unfold normalise_nz.
rewrite H, H0, H1.
remember (null_coeff_range_length rng (nz_terms nz₂) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; constructor.
unfold gcd_nz.
rewrite H, H0.
constructor; simpl; rewrite H1; reflexivity.
Qed.

(*
Add Parametric Morphism α (rng : Lfield.t α) : (@nz_terms α) with 
signature eq_nz rng ==> eq_series rng as nz_terms_morph.
Proof.
intros nz₁ nz₂ Hnz.
inversion Hnz; subst.
constructor.
 intros i.
 inversion H; subst.
 simpl in H2, H3.
bbb.
*)

Theorem eq_ps_refl : reflexive _ eq_ps.
Proof.
intros ps.
destruct ps as [nz| ]; constructor; reflexivity.
Qed.

Theorem eq_ps_sym : symmetric _ eq_ps.
Proof.
intros ps₁ ps₂ H.
induction H; constructor; try assumption; symmetry; assumption.
Qed.

Lemma series_stretch_stretch : ∀ a b s,
  (series_stretch (a * b) s = series_stretch a (series_stretch b s))%ser.
Proof.
intros ap bp s.
unfold series_stretch; simpl.
constructor; simpl.
intros i.
unfold series_nth_rng; simpl.
rewrite Pos2Nat.inj_mul.
remember (Pos.to_nat ap) as a.
remember (Pos.to_nat bp) as b.
assert (a ≠ O) as Ha by (subst a; apply Pos2Nat_ne_0).
assert (b ≠ O) as Hb by (subst b; apply Pos2Nat_ne_0).
rewrite Nbar.fin_inj_mul, Nbar.mul_shuffle0, Nbar.mul_assoc.
remember (Nbar.lt_dec (fin i) (stop s * fin a * fin b)) as n.
destruct n as [Hlt| ]; [ clear Heqn | reflexivity ].
destruct (zerop (i mod (a * b))) as [Hz| Hnz].
 apply Nat.mod_divides in Hz.
  destruct Hz as (c, Hz).
  subst i.
  rewrite Nat.mul_comm, Nat.div_mul.
   destruct (Nbar.lt_dec (fin c) (stop s)) as [Hlt₁| Hge₁].
    rewrite Nat.mul_comm, <- Nat.mul_assoc, Nat.mul_comm.
    rewrite Nat.mod_mul; [ simpl | assumption ].
    rewrite Nat.div_mul; [ simpl | assumption ].
    rewrite Nbar.fin_inj_mul, Nbar.mul_comm.
    destruct (Nbar.lt_dec (fin c * fin b) (stop s * fin b)) as [Hlt₂| Hge₂].
     rewrite Nat.mul_comm, Nat.mod_mul; [ simpl | assumption ].
     rewrite Nat.div_mul; [ simpl | assumption ].
     destruct (Nbar.lt_dec (fin c) (stop s)); [ reflexivity | contradiction ].

     exfalso; apply Hge₂; clear Hge₂.
     apply Nbar.mul_lt_mono_pos_r.
      constructor.
      apply neq_0_lt, Nat.neq_sym; assumption.

      intros H; discriminate H.

      intros H; discriminate H.

      assumption.

    rewrite Nat.mul_assoc, Nat.mul_shuffle0.
    rewrite Nat.mod_mul; [ simpl | assumption ].
    rewrite Nat.div_mul; [ simpl | assumption ].
    rewrite Nbar.fin_inj_mul.
    destruct (Nbar.lt_dec (fin c * fin b) (stop s * fin b)) as [Hlt₂| Hge₂].
     exfalso; apply Hge₁.
     apply Nbar.mul_lt_mono_pos_r in Hlt₂.
      assumption.

      constructor.
      apply neq_0_lt, Nat.neq_sym; assumption.

      intros H; discriminate H.

      intros H; discriminate H.

     reflexivity.

   apply Nat.neq_mul_0; split; assumption.

  apply Nat.neq_mul_0; split; assumption.

 destruct (zerop (i mod a)) as [Hz| ]; [ idtac | reflexivity ].
 apply Nat.mod_divides in Hz; [ idtac | assumption ].
 destruct Hz as (c, Hz).
 subst i.
 rewrite Nat.mul_comm, Nat.div_mul; [ idtac | assumption ].
 destruct (Nbar.lt_dec (fin c) (stop s * fin b)) as [Hlt₁| Hgt₁].
  destruct (zerop (c mod b)) as [Hlt₂| ]; [ idtac | reflexivity ].
  apply Nat.mod_divides in Hlt₂; [ idtac | assumption ].
  destruct Hlt₂ as (c₂, Hlt₂).
  subst c.
  rewrite Nat.mul_assoc, Nat.mul_comm in Hnz.
  rewrite Nat.mod_mul in Hnz.
   exfalso; revert Hnz; apply lt_irrefl.

   apply Nat.neq_mul_0; split; assumption.

  reflexivity.
Qed.

Lemma series_stretch_series_0 : ∀ k, (series_stretch k 0 = 0)%ser.
Proof.
intros k.
constructor; intros i.
unfold series_nth_rng; simpl.
destruct (Nbar.lt_dec (fin i) 0); [ idtac | reflexivity ].
destruct (zerop (i mod Pos.to_nat k)); [ idtac | reflexivity ].
unfold series_nth_rng; simpl.
destruct (Nbar.lt_dec (fin (i / Pos.to_nat k)) 0); reflexivity.
Qed.

Lemma series_stretch_0_if : ∀ k s, (series_stretch k s = 0)%ser → (s = 0)%ser.
Proof.
intros k s Hs.
constructor.
intros i.
inversion Hs; subst.
pose proof (H (i * Pos.to_nat k)%nat) as Hi.
unfold series_nth_rng in Hi; simpl in Hi.
rewrite Nat.mod_mul in Hi; [ simpl in Hi | apply Pos2Nat_ne_0 ].
rewrite Nat.div_mul in Hi; [ simpl in Hi | apply Pos2Nat_ne_0 ].
remember (stop s * fin (Pos.to_nat k))%Nbar as ss.
destruct (Nbar.lt_dec (fin (i * Pos.to_nat k)) ss).
 rewrite Hi.
 unfold series_nth_rng; simpl.
 destruct (Nbar.lt_dec (fin (i * Pos.to_nat k)) 0).
  destruct (Nbar.lt_dec (fin i) 0); reflexivity.

  destruct (Nbar.lt_dec (fin i) 0); reflexivity.

 unfold series_nth_rng; simpl.
 destruct (Nbar.lt_dec (fin i) (stop s)) as [Hlt| Hge].
  exfalso; apply n; clear n Hi.
  subst ss.
  rewrite Nbar.fin_inj_mul.
  apply Nbar.mul_lt_mono_pos_r.
   constructor.
   apply Pos2Nat.is_pos.

   intros HH; discriminate HH.

   intros HH; discriminate HH.

   assumption.

  destruct (Nbar.lt_dec (fin i) 0); reflexivity.
Qed.

Lemma stretch_shift_series_distr : ∀ kp n s,
  (series_stretch kp (series_shift n s) =
   series_shift (n * Pos.to_nat kp) (series_stretch kp s))%ser.
Proof.
intros kp n s.
constructor; intros i.
unfold series_stretch, series_nth_rng; simpl.
remember (Pos.to_nat kp) as k.
assert (k ≠ O) as Hk by (subst k; apply Pos2Nat_ne_0).
destruct (zerop (i mod k)) as [Hz| Hnz].
 apply Nat.mod_divides in Hz; [ idtac | assumption ].
 destruct Hz as (c, Hi).
 subst i.
 rewrite mult_comm.
 rewrite <- Nat.mul_sub_distr_r.
 rewrite Nat.div_mul; [ idtac | assumption ].
 rewrite Nat.div_mul; [ idtac | assumption ].
 rewrite Nat.mod_mul; [ simpl | assumption ].
 rewrite Nbar.fin_inj_mul.
 rewrite Nbar.fin_inj_mul.
 rewrite <- Nbar.mul_add_distr_r.
 rewrite <- Nbar.fin_inj_mul.
 remember (Nbar.lt_dec (fin (c * k)) ((stop s + fin n) * fin k)) as c₁.
 remember (Nbar.lt_dec (fin c) (stop s + fin n)) as c₂.
 remember (lt_dec (c * k) (n * k)) as c₄.
 remember (Nbar.lt_dec (fin (c - n)) (stop s)) as c₅.
 clear Heqc₁ Heqc₂ Heqc₄ Heqc₅.
 destruct c₁ as [H₁| ]; [ idtac | reflexivity ].
 destruct (lt_dec c n) as [Hlt| Hge].
  destruct c₄ as [| H₄]; [ destruct c₂; reflexivity | idtac ].
  destruct c₅ as [H₅| ]; [ idtac | destruct c₂; reflexivity ].
  exfalso; apply H₄.
  apply Nat.mul_lt_mono_pos_r; [ idtac | assumption ].
  rewrite Heqk; apply Pos2Nat.is_pos.

  apply not_gt in Hge.
  remember (c - n)%nat as m.
  assert (m + n = c)%nat by (subst m; apply Nat.sub_add; assumption).
  subst c; clear Heqm Hge.
  destruct c₄ as [H₄| H₄].
   exfalso; apply lt_not_le in H₄; apply H₄.
   rewrite Nat.mul_add_distr_r.
   apply le_plus_r.

   destruct c₂ as [H₂| H₂].
    destruct c₅ as [| H₅]; [ reflexivity | idtac ].
    rewrite Nbar.fin_inj_add in H₂.
    apply Nbar.add_lt_mono_r in H₂; [ idtac | intros H; discriminate H ].
    contradiction.

    destruct c₅ as [H₅| ]; [ idtac | reflexivity ].
    exfalso; apply H₂.
    rewrite Nbar.fin_inj_add.
    apply Nbar.add_lt_mono_r; [ idtac | assumption ].
    intros H; discriminate H.

 rewrite Nbar.fin_inj_mul.
 rewrite <- Nbar.mul_add_distr_r.
 remember (Nbar.lt_dec (fin i) ((stop s + fin n) * fin k)) as c₁.
 remember (lt_dec i (n * k)) as c₂.
 remember (zerop ((i - n * k) mod k)) as c₃.
 remember (Nbar.lt_dec (fin ((i - n * k) / k)) (stop s)) as c₄.
 clear Heqc₁ Heqc₂ Heqc₃ Heqc₄.
 destruct c₁ as [H₁| ]; [ idtac | reflexivity ].
 destruct c₂ as [| H₂]; [ reflexivity | idtac ].
 destruct c₃ as [H₃| ]; [ idtac | reflexivity ].
 destruct c₄ as [H₄| ]; [ idtac | reflexivity ].
 apply Nat.mod_divides in H₃; [ idtac | assumption ].
 destruct H₃ as (c, H₃).
 destruct c as [| c].
  rewrite Nat.mul_0_r in H₃.
  apply Nat.sub_0_le in H₃.
  apply Nat.nlt_ge in H₂.
  apply le_antisym in H₃; [ idtac | assumption ].
  subst i.
  rewrite Nat.mod_mul in Hnz; [ idtac | assumption ].
  exfalso; revert Hnz; apply Nat.lt_irrefl.

  apply Nat.add_sub_eq_nz in H₃.
   rewrite Nat.mul_comm, <- Nat.mul_add_distr_l, Nat.mul_comm in H₃.
   subst i.
   rewrite Nat.mod_mul in Hnz; [ idtac | assumption ].
   exfalso; revert Hnz; apply Nat.lt_irrefl.

   apply Nat.neq_mul_0.
   split; [ assumption | idtac ].
   intros H; discriminate H.
Qed.

Lemma series_shift_shift : ∀ x y ps,
  (series_shift x (series_shift y ps) = series_shift (x + y) ps)%ser.
Proof.
intros x y ps.
constructor; simpl.
intros i.
unfold series_nth_rng; simpl.
rewrite Nbar.add_shuffle0.
rewrite Nbar.fin_inj_add, Nbar.add_assoc.
remember (Nbar.lt_dec (fin i) (stop ps + fin x + fin y)) as c₁.
remember (lt_dec (i - x) y) as c₂.
remember (lt_dec i (x + y)) as c₃.
clear Heqc₁ Heqc₂ Heqc₃.
destruct (lt_dec i x) as [Hlt| Hge].
 destruct c₃ as [H₃| H₃]; [ reflexivity | idtac ].
 destruct c₁ as [c₁| ]; [ idtac | reflexivity ].
 exfalso; apply H₃.
 apply Nat.lt_lt_add_r; assumption.

 destruct c₂ as [H₂| H₂].
  destruct c₃ as [H₃| H₃]; [ reflexivity | idtac ].
  destruct c₁ as [H₁| H₁]; [ idtac | reflexivity ].
  exfalso; apply H₃.
  apply not_gt in Hge.
  apply Nat.lt_sub_lt_add_l; assumption.

  rewrite Nat.sub_add_distr.
  destruct c₃ as [H₃| H₃]; [ idtac | reflexivity ].
  destruct c₁ as [H₁| H₁]; [ idtac | reflexivity ].
  apply not_gt in Hge.
  exfalso; apply H₂.
  unfold lt.
  rewrite <- Nat.sub_succ_l; [ idtac | assumption ].
  apply Nat.le_sub_le_add_l.
  assumption.
Qed.

Theorem series_shift_left_shift : ∀ s n,
  null_coeff_range_length rng s 0 = fin n
  → (series_shift n (series_left_shift n s) = s)%ser.
Proof.
intros s n Hn.
apply null_coeff_range_length_iff in Hn.
simpl in Hn.
destruct Hn as (Hz, Hnz).
constructor; intros i.
unfold series_nth_rng; simpl.
rewrite Nbar.fold_sub.
destruct (Nbar.le_dec (fin n) (stop s)) as [H₁| H₁].
 rewrite Nbar.sub_add; auto.
 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₂| H₂].
  destruct (lt_dec i n) as [H₃| H₃].
   apply Hz in H₃.
   unfold series_nth_rng in H₃.
   destruct (Nbar.lt_dec (fin i) (stop s)) as [H₄| H₄].
    symmetry; assumption.

    contradiction.

   apply Nat.nlt_ge in H₃.
   rewrite Nat.add_sub_assoc; [ idtac | assumption ].
   rewrite Nat.add_comm, Nat.add_sub.
   reflexivity.

  reflexivity.

 apply Nbar.nle_gt in H₁.
 replace (stop s - fin n + fin n)%Nbar with (fin n) .
  destruct (Nbar.lt_dec (fin i) (fin n)) as [H₂| H₂].
   destruct (lt_dec i n) as [H₃| H₃].
    apply Hz in H₃.
    unfold series_nth_rng in H₃.
    destruct (Nbar.lt_dec (fin i) (stop s)) as [H₄| H₄].
     symmetry; assumption.

     reflexivity.

    apply Nbar.fin_lt_mono in H₂.
    contradiction.

   destruct (Nbar.lt_dec (fin i) (stop s)) as [H₃| H₃].
    exfalso; apply H₂.
    eapply Nbar.lt_trans; eassumption.

    reflexivity.

  simpl.
  destruct (stop s) as [st| ]; simpl.
   apply Nbar.fin_lt_mono in H₁.
   apply Nat.lt_le_incl in H₁.
   apply Nat.sub_0_le in H₁.
   rewrite H₁; reflexivity.

   apply Nbar.nle_gt in H₁.
   exfalso; apply H₁; constructor.
Qed.

Theorem series_left_shift_shift : ∀ s n m,
  (m ≤ n)%nat
  → (series_left_shift n (series_shift m s) = series_left_shift (n - m) s)%ser.
Proof.
intros s n m Hmn.
constructor; intros i.
unfold series_nth_rng; simpl.
do 2 rewrite Nbar.fold_sub.
rewrite Nbar.fin_inj_sub.
rewrite Nbar.sub_sub_distr.
 destruct (Nbar.lt_dec (fin i) (stop s + fin m - fin n)) as [H₁| H₁].
  destruct (lt_dec (n + i) m) as [H₂| H₂].
   exfalso; fast_omega Hmn H₂.

   rewrite Nat.add_sub_swap; [ reflexivity | assumption ].

  reflexivity.

 intros H; discriminate H.

 apply Nbar.le_fin; assumption.
Qed.

Theorem series_left_shift_stretch : ∀ s n k,
  (series_left_shift (n * Pos.to_nat k) (series_stretch k s) =
   series_stretch k (series_left_shift n s))%ser.
Proof.
intros s n k.
constructor; intros i.
unfold series_nth_rng; simpl.
do 2 rewrite Nbar.fold_sub.
rewrite Nbar.fin_inj_mul.
rewrite <- Nbar.mul_sub_distr_r; [ idtac | intros H; discriminate H ].
rewrite Nat.add_comm.
rewrite Nat.mod_add; auto.
rewrite Nat.div_add; auto.
remember ((stop s - fin n) * fin (Pos.to_nat k))%Nbar as x eqn:Hx .
destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁]; [ idtac | reflexivity ].
destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂]; [ idtac | reflexivity ].
unfold series_nth_rng; simpl.
rewrite Nbar.fold_sub.
rewrite Nat.add_comm.
destruct (Nbar.lt_dec (fin (n + i / Pos.to_nat k)) (stop s)) as [H₃| H₃].
 destruct (Nbar.lt_dec (fin (i / Pos.to_nat k)) (stop s - fin n)) as [H₄| H₄].
  reflexivity.

  exfalso; apply H₄.
  apply Nbar.lt_add_lt_sub_r.
  rewrite Nbar.add_comm.
  rewrite <- Nbar.fin_inj_add; assumption.

 destruct (Nbar.lt_dec (fin (i / Pos.to_nat k)) (stop s - fin n)) as [H₄| H₄].
  exfalso; apply H₃.
  rewrite Nbar.fin_inj_add.
  rewrite Nbar.add_comm.
  apply Nbar.lt_add_lt_sub_r.
  assumption.

  reflexivity.
Qed.

Theorem eq_ps_trans : transitive _ eq_ps.
Proof.
intros ps₁ ps₂ ps₃ H₁ H₂.
induction H₁.
 inversion H₂; subst.
  constructor; etransitivity; eassumption.

  constructor.
  unfold normalise_nz in H.
  remember (null_coeff_range_length rng (nz_terms nz₁) 0) as n₁ eqn:Hn₁ .
  remember (null_coeff_range_length rng (nz_terms nz₂) 0) as n₂ eqn:Hn₂ .
  symmetry in Hn₁, Hn₂.
  destruct n₁ as [n₁| ].
   destruct n₂ as [n₂| ]; [ idtac | inversion H ].
   apply null_coeff_range_length_iff in Hn₂.
   destruct Hn₂ as (_, Hn₂).
   exfalso; apply Hn₂; rewrite H1.
   unfold series_nth_rng; simpl.
   destruct (Nbar.lt_dec (fin n₂) 0); reflexivity.

   destruct n₂ as [n₂| ]; [ inversion H | idtac ].
   apply null_coeff_range_length_iff in Hn₁.
   constructor; intros i.
   unfold series_nth_rng at 2; simpl.
   destruct (Nbar.lt_dec (fin i) 0); apply Hn₁.

 inversion H₂; subst.
  rename nz0 into nz₃.
  constructor.
  unfold normalise_nz.
  rewrite H, H0.
  remember (null_coeff_range_length rng series_0 0) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ]; [ idtac | reflexivity ].
  apply null_coeff_range_length_iff in Hn.
  destruct Hn as (_, Hn).
  exfalso; apply Hn.
  unfold series_nth_rng; simpl.
  destruct (Nbar.lt_dec (fin n) 0); reflexivity.

  constructor; assumption.

 inversion H₂; constructor; subst.
 unfold normalise_nz in H1.
 rename nz into nz₁.
 remember (null_coeff_range_length rng (nz_terms nz₁) 0) as n₁ eqn:Hn₁ .
 remember (null_coeff_range_length rng (nz_terms nz₂) 0) as n₂ eqn:Hn₂ .
 symmetry in Hn₁, Hn₂.
 destruct n₁ as [n₁| ].
  rewrite H in Hn₁.
  apply null_coeff_range_length_iff in Hn₁.
  destruct Hn₁ as (_, Hn₁).
  exfalso; apply Hn₁.
  unfold series_nth_rng; simpl.
  destruct (Nbar.lt_dec (fin n₁) 0); reflexivity.

  destruct n₂ as [n₂| ]; [ inversion H1 | idtac ].
  apply null_coeff_range_length_iff in Hn₂.
  constructor; intros i.
  unfold series_nth_rng at 2; simpl.
  destruct (Nbar.lt_dec (fin i) 0); apply Hn₂.

 assumption.
Qed.

Add Parametric Relation : (puiseux_series α) eq_ps
 reflexivity proved by eq_ps_refl
 symmetry proved by eq_ps_sym
 transitivity proved by eq_ps_trans
 as eq_ps_rel.

(*
Definition mk_nonzero (s : series α) v c := NonZero (mknz s v c).

Lemma fold_mk_nonzero : ∀ (s : series α) v c,
  NonZero (mknz s v c) = mk_nonzero s v c.
Proof. reflexivity. Qed.

Add Parametric Morphism : mk_nonzero
with signature eq_series rng ==> eq ==> eq ==> eq_ps rng as NonZero_morph.
Proof.
aaa.
*)

(*
Definition valuation (ps : puiseux_series α) :=
  match ps with
  | NonZero nz => Some (nz_valnum nz # nz_comden nz)
  | Zero => None
  end.

Definition valuation_coeff (ps : puiseux_series α) :=
  match ps with
  | NonZero nz => series_nth_rng rng 0 (nz_terms nz)
  | Zero => 0%rng
  end.

Theorem lt_null_coeff_range_length : ∀ s c n,
  (fin n < null_coeff_range_length rng s c)%Nbar
  → (series_nth_rng rng (c + n) s = 0)%rng.
Proof.
intros s c n Hn.
remember (null_coeff_range_length rng s c) as v eqn:Hv .
symmetry in Hv.
apply null_coeff_range_length_iff in Hv.
destruct v as [v| ]; [ idtac | apply Hv ].
destruct Hv as (Hvz, Hvnz).
apply Hvz, Nbar.fin_lt_mono; assumption.
Qed.

Theorem eq_null_coeff_range_length : ∀ s c n,
  null_coeff_range_length rng s c = fin n
  → (series_nth_rng rng (c + n) s ≠ 0)%rng.
Proof.
intros s c n Hn.
apply null_coeff_range_length_iff in Hn.
destruct Hn; assumption.
Qed.
*)

Lemma series_shift_0 : ∀ s, (series_shift 0 s = s)%ser.
Proof.
intros s.
constructor; intros i.
unfold series_shift, series_nth_rng; simpl.
rewrite Nbar.add_0_r, Nat.sub_0_r; reflexivity.
Qed.

Lemma series_nth_shift_S : ∀ s n i,
  series_nth_rng rng i (series_shift n s) =
  series_nth_rng rng (S i) (series_shift (S n) s).
Proof.
intros s n i.
unfold series_nth_rng; simpl.
destruct (Nbar.lt_dec (fin i) (stop s + fin n)) as [Hlt₁| Hge₁].
 destruct (Nbar.lt_dec (fin (S i)) (stop s + fin (S n))) as [Hlt₂| Hge₂].
  destruct (lt_dec i n) as [Hlt₃| Hge₃].
   destruct (lt_dec (S i) (S n)) as [Hlt₄| Hge₄]; [ reflexivity | idtac ].
   apply Nat.succ_lt_mono in Hlt₃; contradiction.

   destruct (lt_dec (S i) (S n)) as [Hlt₄| Hge₄]; [ idtac | reflexivity ].
   apply Nat.succ_lt_mono in Hlt₄; contradiction.

  remember (stop s) as st eqn:Hst .
  symmetry in Hst.
  destruct st as [st| ].
   simpl in Hlt₁.
   apply Nbar.succ_lt_mono in Hlt₁; simpl in Hlt₁.
   rewrite <- Nat.add_succ_r in Hlt₁; contradiction.

   exfalso; apply Hge₂; constructor.

 destruct (Nbar.lt_dec (fin (S i)) (stop s + fin (S n))) as [Hlt₂| Hge₂].
  exfalso; apply Hge₁, Nbar.succ_lt_mono.
  destruct (stop s) as [st| ]; [ idtac | constructor ].
  simpl in Hlt₂ |- *.
  rewrite <- Nat.add_succ_r; assumption.

  reflexivity.
Qed.

Lemma null_coeff_range_length_shift_S : ∀ s c n,
  (c ≤ n)%nat
  → null_coeff_range_length rng (series_shift (S n) s) c =
    NS (null_coeff_range_length rng (series_shift n s) c).
Proof.
intros s c n Hcn.
remember (null_coeff_range_length rng (series_shift n s) c) as u eqn:Hu .
remember (null_coeff_range_length rng (series_shift (S n) s) c) as v eqn:Hv .
symmetry in Hu, Hv.
apply null_coeff_range_length_iff in Hu.
apply null_coeff_range_length_iff in Hv.
destruct u as [u| ].
 destruct Hu as (Hiu, Hu).
 destruct v as [v| ].
  destruct Hv as (Hiv, Hv).
  apply Nbar.fin_inj_wd.
  rewrite series_nth_shift_S in Hu.
  destruct (lt_dec (S u) v) as [Hlt₁| Hge₁].
   rewrite <- Nat.add_succ_r in Hu.
   rewrite Hiv in Hu; [ negation Hu | assumption ].

   apply Nat.nlt_ge in Hge₁.
   destruct v.
    unfold series_nth_rng in Hv; simpl in Hv.
    rewrite Nat.add_0_r in Hv.
    exfalso.
    destruct (Nbar.lt_dec (fin c) (stop s + fin (S n))) as [H₁| H₁].
     destruct (lt_dec c (S n)) as [H₂| H₂].
      apply Hv; reflexivity.

      apply H₂.
      apply -> Nat.succ_le_mono; assumption.

     apply Hv; reflexivity.

    destruct (lt_dec v u) as [Hlt₂| Hge₂].
     apply Hiu in Hlt₂.
     rewrite Nat.add_succ_r in Hv.
     rewrite <- series_nth_shift_S in Hv; contradiction.

     apply Nat.nlt_ge in Hge₂.
     apply le_antisym; [ assumption | idtac ].
     apply Nat.succ_le_mono in Hge₂; assumption.

  rewrite series_nth_shift_S in Hu.
  rewrite <- Nat.add_succ_r in Hu.
  exfalso; apply Hu, Hv.

 destruct v as [v| ]; [ idtac | reflexivity ].
 destruct Hv as (Hiv, Hv).
 destruct v.
  unfold series_nth_rng in Hv; simpl in Hv.
  rewrite Nat.add_0_r in Hv.
  exfalso.
  destruct (Nbar.lt_dec (fin c) (stop s + fin (S n))) as [H₁| H₁].
   destruct (lt_dec c (S n)) as [H₂| H₂].
    apply Hv; reflexivity.

    apply H₂.
    apply -> Nat.succ_le_mono; assumption.

   apply Hv; reflexivity.

  rewrite Nat.add_succ_r in Hv.
  rewrite <- series_nth_shift_S in Hv.
  exfalso; apply Hv, Hu.
Qed.

Theorem null_coeff_range_length_shift : ∀ s n,
  null_coeff_range_length rng (series_shift n s) 0 =
    (fin n + null_coeff_range_length rng s 0)%Nbar.
Proof.
intros s n.
induction n.
 rewrite series_shift_0, Nbar.add_0_l; reflexivity.

 rewrite null_coeff_range_length_shift_S; [ idtac | apply Nat.le_0_l ].
 rewrite IHn; simpl.
 destruct (null_coeff_range_length rng s); reflexivity.
Qed.

Lemma shifted_in_stretched : ∀ s k i,
  (0 < i mod Pos.to_nat k)%nat
  → series_nth_rng rng i (series_stretch k s) = 0%rng.
Proof.
intros s k i Hi.
unfold series_nth_rng; simpl.
unfold series_nth_rng; simpl.
destruct (zerop (i mod Pos.to_nat k)) as [Hz| Hnz].
 exfalso; revert Hi; rewrite Hz; apply Nat.lt_irrefl.

 destruct (Nbar.lt_dec (fin i) (stop s * fin (Pos.to_nat k))); reflexivity.
Qed.

Lemma series_nth_rng_mul_stretch : ∀ s k i,
  series_nth_rng rng (Pos.to_nat k * i) (series_stretch k s) =
  series_nth_rng rng i s.
Proof.
intros s k i.
unfold series_nth_rng; simpl.
rewrite Nat.mul_comm.
rewrite Nat.mod_mul; [ simpl | apply Pos2Nat_ne_0 ].
rewrite Nat.div_mul; [ simpl | apply Pos2Nat_ne_0 ].
unfold series_nth_rng.
remember (fin (i * Pos.to_nat k)) as x.
remember (stop s * fin (Pos.to_nat k))%Nbar as y.
destruct (Nbar.lt_dec x y) as [Hlt₁| Hge₁]; subst x y.
 reflexivity.

 destruct (Nbar.lt_dec (fin i) (stop s)) as [Hlt₂| Hge₂].
  exfalso; apply Hge₁.
  rewrite Nbar.fin_inj_mul.
  apply Nbar.mul_lt_mono_pos_r.
   constructor; apply Pos2Nat.is_pos.

   intros H; discriminate H.

   intros H; discriminate H.

   assumption.

  reflexivity.
Qed.

(*
Lemma zero_series_stretched : ∀ s,
  (∀ i : nat, series_nth_rng rng i s = 0)%rng
  → (∀ n k, series_nth_rng rng n (series_stretch k s) = 0)%rng.
Proof.
intros s H n k.
unfold series_nth_rng; simpl.
remember (stop s * fin (Pos.to_nat k))%Nbar as x.
destruct (Nbar.lt_dec (fin n) x) as [Hlt₁| ]; [ subst x | reflexivity ].
destruct (zerop (n mod Pos.to_nat k)) as [Hz| ]; [ idtac | reflexivity ].
rewrite Nat.mod_divides in Hz; [ idtac | apply Pos2Nat_ne_0 ].
destruct Hz as (c, Hn); subst n.
rewrite Nat.mul_comm.
rewrite Nat.div_mul; [ apply H | apply Pos2Nat_ne_0 ].
Qed.

Lemma zero_stretched_series : ∀ s k,
  (∀ i, series_nth_rng rng i (series_stretch k s) = 0)%rng
  → (∀ n, series_nth_rng rng n s = 0)%rng.
Proof.
intros s k H n.
pose proof (H (Pos.to_nat k * n)%nat) as Hn.
rewrite series_nth_rng_mul_stretch in Hn.
assumption.
Qed.
*)

Lemma stretch_finite_series : ∀ s b k,
  (∀ i, (series_nth_rng rng (b + i) s = 0)%rng)
  → ∀ i,
    (series_nth_rng rng (b * Pos.to_nat k + i) (series_stretch k s) = 0)%rng.
Proof.
intros s b k Hz i.
destruct (zerop (i mod Pos.to_nat k)) as [H₁| H₁].
 apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
 destruct H₁ as (c, H₁).
 subst i.
 rewrite Nat.mul_comm, <- Nat.mul_add_distr_l.
 rewrite series_nth_rng_mul_stretch.
 apply Hz.

 rewrite shifted_in_stretched; [ reflexivity | idtac ].
 rewrite Nat.add_comm.
 rewrite Nat.mod_add; [ assumption | apply Pos2Nat_ne_0 ].
Qed.

Lemma null_coeff_range_length_stretch : ∀ s b k,
  null_coeff_range_length rng (series_stretch k s) (b * Pos.to_nat k) =
    (fin (Pos.to_nat k) * null_coeff_range_length rng s b)%Nbar.
Proof.
intros s b k.
remember (null_coeff_range_length rng s b) as n eqn:Hn .
symmetry in Hn.
apply null_coeff_range_length_iff in Hn.
apply null_coeff_range_length_iff.
rewrite Nbar.mul_comm.
destruct n as [n| ]; simpl.
 destruct Hn as (Hz, Hnz).
 split.
  intros i Hin.
  destruct (zerop (i mod Pos.to_nat k)) as [H₁| H₁].
   apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
   destruct H₁ as (c, H₁).
   rewrite H₁.
   rewrite Nat.mul_comm, <- Nat.mul_add_distr_l.
   rewrite series_nth_rng_mul_stretch.
   apply Hz.
   rewrite H₁ in Hin.
   rewrite Nat.mul_comm in Hin.
   apply Nat.mul_lt_mono_pos_r in Hin; [ assumption | apply Pos2Nat.is_pos ].

   rewrite shifted_in_stretched; [ reflexivity | idtac ].
   rewrite Nat.add_comm.
   rewrite Nat.mod_add; [ assumption | apply Pos2Nat_ne_0 ].

  rewrite <- Nat.mul_add_distr_r.
  rewrite Nat.mul_comm.
  rewrite series_nth_rng_mul_stretch.
  assumption.

 intros i.
 apply stretch_finite_series; assumption.
Qed.

Lemma null_coeff_range_length_stretch_0 : ∀ s k,
  null_coeff_range_length rng (series_stretch k s) 0 =
    (fin (Pos.to_nat k) * null_coeff_range_length rng s 0)%Nbar.
Proof.
intros s k.
rewrite <- null_coeff_range_length_stretch.
rewrite Nat.mul_0_l; reflexivity.
Qed.

Lemma series_nth_add_shift : ∀ s i n,
  (series_nth_rng rng (i + n) (series_shift n s) =
   series_nth_rng rng i s)%rng.
Proof.
intros s i n.
unfold series_nth_rng; simpl.
rewrite Nat.add_sub.
destruct (Nbar.lt_dec (fin (i + n)) (stop s + fin n)) as [H₁| H₁].
 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₂| H₂].
  destruct (lt_dec (i + n) n) as [H₃| H₃]; [ idtac | reflexivity ].
  apply Nat.lt_add_lt_sub_r in H₃.
  rewrite Nat.sub_diag in H₃.
  exfalso; revert H₃; apply Nat.nlt_0_r.

  rewrite Nbar.fin_inj_add in H₁.
  apply Nbar.add_lt_mono_r with (n := fin i) in H₁; [ contradiction | idtac ].
  intros H; discriminate H.

 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₂| H₂]; [ idtac | reflexivity ].
 exfalso; apply H₁.
 rewrite Nbar.fin_inj_add.
 apply Nbar.add_lt_mono_r; [ intros H; discriminate H | assumption ].
Qed.

Lemma null_coeff_range_length_shift_add : ∀ s m n,
  null_coeff_range_length rng (series_shift m s) (m + n) =
  null_coeff_range_length rng s n.
Proof.
intros s m n.
remember (null_coeff_range_length rng s n) as v eqn:Hv .
symmetry in Hv.
apply null_coeff_range_length_iff in Hv.
apply null_coeff_range_length_iff.
destruct v as [v| ].
 destruct Hv as (Hltz, Hnz).
 split.
  intros i Hiv.
  rewrite <- Nat.add_assoc, Nat.add_comm.
  rewrite series_nth_add_shift.
  apply Hltz; assumption.

  rewrite <- Nat.add_assoc, Nat.add_comm.
  rewrite series_nth_add_shift.
  assumption.

 intros i.
 rewrite <- Nat.add_assoc, Nat.add_comm.
 rewrite series_nth_add_shift.
 apply Hv.
Qed.

(*
Lemma greatest_series_x_power_lim_shift : ∀ cnt s n b,
  greatest_series_x_power_lim rng cnt (series_shift n s) (b + n) =
  greatest_series_x_power_lim rng cnt s b.
Proof.
intros cnt s n b.
revert s n b.
induction cnt; intros; [ reflexivity | simpl ].
rewrite <- Nat.add_succ_l, Nat.add_comm.
rewrite null_coeff_range_length_shift_add.
remember (null_coeff_range_length rng s (S b)) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; [ idtac | reflexivity ].
do 2 rewrite divmod_mod.
do 2 f_equal.
rewrite Nat.add_shuffle0.
rewrite <- Nat.add_succ_l.
apply IHcnt.
Qed.
*)

Lemma nth_null_coeff_range_length_shift : ∀ s cnt n b,
  nth_null_coeff_range_length (series_shift n s) cnt (b + n) =
  nth_null_coeff_range_length s cnt b.
Proof.
intros s cnt n b.
revert b.
induction cnt; intros; simpl.
 rewrite <- Nat.add_succ_l, Nat.add_comm.
 rewrite null_coeff_range_length_shift_add.
 destruct (null_coeff_range_length rng s (S b)); reflexivity.

 rewrite <- Nat.add_succ_l, Nat.add_comm.
 rewrite null_coeff_range_length_shift_add.
 remember (null_coeff_range_length rng s (S b)) as m eqn:Hm .
 symmetry in Hm.
 destruct m as [m| ]; [ idtac | reflexivity ].
 rewrite Nat.add_shuffle0.
 rewrite <- Nat.add_succ_l.
 apply IHcnt.
Qed.

Lemma greatest_series_x_power_shift : ∀ n s b,
  greatest_series_x_power rng (series_shift n s) (b + n) =
  greatest_series_x_power rng s b.
Proof.
intros n s b.
remember (greatest_series_x_power rng s b) as k eqn:Hk .
symmetry in Hk.
apply greatest_series_x_power_iff in Hk.
apply greatest_series_x_power_iff.
unfold is_the_greatest_series_x_power in Hk |- *.
destruct Hk as (Hz, Hnz).
split.
 intros cnt.
 rewrite nth_null_coeff_range_length_shift.
 apply Hz.

 intros k₁ Hk₁.
 apply Hnz in Hk₁.
 destruct Hk₁ as (m, Hm).
 exists m; erewrite nth_null_coeff_range_length_shift; assumption.
Qed.

(*
Lemma null_coeff_range_length_succ : ∀ s n,
  null_coeff_range_length rng s (S n) =
  match null_coeff_range_length rng s n with
  | fin O => null_coeff_range_length rng s (S n)
  | fin (S m) => fin m
  | ∞ => ∞
  end.
Proof.
intros s n.
remember (null_coeff_range_length rng s n) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ].
 destruct m as [| m]; [ reflexivity | idtac ].
 apply null_coeff_range_length_iff in Hm.
 apply null_coeff_range_length_iff.
 destruct Hm as (Hz, Hnz).
 split.
  intros i Him.
  rewrite Nat.add_succ_l, <- Nat.add_succ_r.
  apply Hz.
  apply -> Nat.succ_lt_mono; assumption.

  rewrite Nat.add_succ_l, <- Nat.add_succ_r.
  assumption.

 apply null_coeff_range_length_iff in Hm.
 apply null_coeff_range_length_iff.
 intros i.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hm.
Qed.
*)

Lemma null_coeff_range_length_stretch_succ : ∀ s n p k,
  null_coeff_range_length rng s (S n) = fin p
  → null_coeff_range_length rng (series_stretch k s)
      (S (n * Pos.to_nat k)) = fin (S p * Pos.to_nat k - 1).
Proof.
(* à nettoyer *)
intros s n p k Hp.
remember (series_stretch k s) as s₁ eqn:Hs₁ .
remember (null_coeff_range_length rng s₁ (S (n * Pos.to_nat k))) as q eqn:Hq .
symmetry in Hq.
apply null_coeff_range_length_iff in Hq.
destruct q as [q| ].
 destruct Hq as (Hzq, Hnzq).
 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hnzq.
 destruct (zerop (S q mod Pos.to_nat k)) as [H₁| H₁].
  apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
  destruct H₁ as (q', Hq').
  rewrite Hq' in Hnzq.
  rewrite Nat.mul_comm in Hnzq.
  rewrite <- Nat.mul_add_distr_l in Hnzq.
  rewrite Hs₁ in Hnzq.
  rewrite series_nth_rng_mul_stretch in Hnzq.
  apply null_coeff_range_length_iff in Hp.
  destruct Hp as (Hzp, Hnzp).
  rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hnzp.
  apply Nbar.fin_inj_wd.
  assert (q' = S p) as H.
   destruct (lt_eq_lt_dec q' (S p)) as [[H₁| H₁]| H₁].
    exfalso.
    destruct (eq_nat_dec q' p) as [H₂| H₂].
     subst q'.
     clear H₁.
     destruct p as [| p].
      rewrite Nat.mul_0_r in Hq'; discriminate Hq'.

      assert (p < S p)%nat as H by fast_omega .
      apply Hzp in H.
      rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
      rewrite H in Hnzq; apply Hnzq; reflexivity.

     assert (q' < p)%nat as H by fast_omega H₁ H₂.
     destruct q' as [| q'].
      rewrite Nat.mul_0_r in Hq'; discriminate Hq'.

      apply lt_S_n in H₁.
      apply Hzp in H₁.
      rewrite Nat.add_succ_l, <- Nat.add_succ_r in H₁.
      rewrite H₁ in Hnzq; apply Hnzq; reflexivity.

    assumption.

    exfalso.
    assert (Pos.to_nat k * S p - 1 < q)%nat as H.
     Focus 2.
     apply Hzq in H.
     rewrite Nat.add_sub_assoc in H.
      simpl in H.
      rewrite Nat.sub_0_r in H.
      rewrite Nat.mul_comm in H.
      rewrite <- Nat.mul_add_distr_l in H.
      rewrite Hs₁ in H.
      rewrite series_nth_rng_mul_stretch in H.
      rewrite H in Hnzp.
      apply Hnzp; reflexivity.

      remember (Pos.to_nat k) as kn eqn:Hkn .
      symmetry in Hkn.
      destruct kn as [| kn].
       exfalso; revert Hkn; apply Pos2Nat_ne_0.

       simpl; apply le_n_S.
       apply le_0_n.

     apply plus_lt_reg_l with (p := 1%nat).
     simpl.
     rewrite <- Nat.sub_succ_l.
      simpl.
      rewrite Nat.sub_0_r.
      rewrite Hq'.
      apply mult_lt_compat_l.
       assumption.

       apply Pos2Nat.is_pos.

      remember (Pos.to_nat k) as kn eqn:Hkn .
      symmetry in Hkn.
      destruct kn as [| kn].
       exfalso; revert Hkn; apply Pos2Nat_ne_0.

       simpl; apply le_n_S.
       apply le_0_n.

   subst q'.
   rewrite Nat.mul_comm.
   rewrite <- Hq'.
   simpl.
   rewrite Nat.sub_0_r; reflexivity.

  assert (0 < (n * Pos.to_nat k + S q) mod Pos.to_nat k)%nat as H.
   Focus 2.
   apply shifted_in_stretched with (s := s) in H.
   rewrite <- Hs₁ in H.
   rewrite H in Hnzq.
   exfalso; apply Hnzq; reflexivity.

   rewrite Nat.add_comm.
   rewrite Nat.mod_add; [ idtac | apply Pos2Nat_ne_0 ].
   assumption.

 exfalso.
 apply null_coeff_range_length_iff in Hp.
 destruct Hp as (Hzp, Hnzp).
 rewrite <- series_nth_rng_mul_stretch with (k := k) in Hnzp.
 rewrite <- Hs₁ in Hnzp.
 rewrite Nat.mul_add_distr_l in Hnzp.
 rewrite Nat.mul_succ_r in Hnzp.
 rewrite Nat.mul_comm in Hnzp.
 rewrite Nat.add_shuffle0, <- Nat.add_assoc in Hnzp.
 rewrite <- Nat.mul_succ_r in Hnzp.
 remember (Pos.to_nat k) as kn eqn:Hkn .
 symmetry in Hkn.
 destruct kn as [| kn].
  exfalso; revert Hkn; apply Pos2Nat_ne_0.

  simpl in Hnzp.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hnzp.
  rewrite Hq in Hnzp.
  apply Hnzp; reflexivity.
Qed.

Lemma null_coeff_range_length_stretch_succ_inf : ∀ s n k,
  null_coeff_range_length rng s (S n) = ∞
  → null_coeff_range_length rng (series_stretch k s) (S (n * Pos.to_nat k)) =
      ∞.
Proof.
intros s n k Hp.
apply null_coeff_range_length_iff in Hp.
apply null_coeff_range_length_iff.
unfold null_coeff_range_length_prop in Hp |- *.
intros i.
destruct (lt_dec (S i) (Pos.to_nat k)) as [H| H].
 rewrite shifted_in_stretched; [ reflexivity | simpl ].
 rewrite Nat.add_comm.
 rewrite <- Nat.add_succ_l.
 rewrite Nat.mod_add; [ idtac | apply Pos2Nat_ne_0 ].
 rewrite Nat.mod_small; [ idtac | assumption ].
 apply Nat.lt_0_succ.

 apply Nat.nlt_ge in H.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 replace (S i) with (Pos.to_nat k + (S i - Pos.to_nat k))%nat by omega.
 rewrite Nat.add_assoc.
 rewrite Nat.mul_comm.
 rewrite <- Nat.mul_succ_r.
 rewrite Nat.mul_comm.
 apply stretch_finite_series.
 assumption.
Qed.

Lemma series_shrink_shrink : ∀ (s : series α) k₁ k₂,
  (series_shrink (k₁ * k₂) s = series_shrink k₁ (series_shrink k₂ s))%ser.
Proof.
intros s k₁ k₂.
constructor; intros i.
unfold series_shrink; simpl.
unfold series_nth_rng; simpl.
do 3 rewrite Nbar.fold_sub.
do 3 rewrite Nbar.fold_div.
do 3 rewrite Nbar.fold_div_sup.
rewrite Pos2Nat.inj_mul, Nat.mul_assoc.
rewrite Nbar.div_sup_div_sup.
 rewrite Nbar.fin_inj_mul.
 rewrite Nbar.mul_comm.
 reflexivity.

 intros H₁.
 injection H₁; apply Pos2Nat_ne_0.

 apply Nbar.lt_fin, Pos2Nat.is_pos.
Qed.

Lemma series_shrink_stretch : ∀ s k,
  (series_shrink k (series_stretch k s) = s)%ser.
Proof.
intros s k.
constructor; intros i.
unfold series_nth_rng; simpl.
rewrite Nbar.fold_sub.
rewrite Nbar.fold_div.
rewrite Nbar.fold_div_sup.
rewrite Nbar.div_sup_mul.
 rewrite Nat.mod_mul; simpl.
  rewrite Nat.div_mul; simpl.
   unfold series_nth_rng.
   destruct (Nbar.lt_dec (fin i) (stop s)); reflexivity.

   apply Pos2Nat_ne_0.

  apply Pos2Nat_ne_0.

 intros H; apply Nbar.fin_inj_wd in H.
 revert H; apply Pos2Nat_ne_0.

 intros H; discriminate H.
Qed.

Fixpoint rank_of_nonzero_after_from s n i b :=
  match n with
  | O => O
  | S n₁ =>
      if lt_dec b i then
        match null_coeff_range_length rng s (S b) with
        | fin m => S (rank_of_nonzero_after_from s n₁ i (S b + m)%nat)
        | ∞ => O
        end
      else O
  end.

(*
Fixpoint index_of_nonzero_before_from s n i b last_b :=
  match n with
  | O => b
  | S n₁ =>
      if lt_dec b i then
        match null_coeff_range_length rng s (S b) with
        | fin m => index_of_nonzero_before_from s n₁ i (S b + m)%nat b
        | ∞ => b
        end
      else last_b
  end.
*)

Definition rank_of_nonzero_before s i :=
  pred (rank_of_nonzero_after_from s (S i) i 0).

(*
Definition index_of_nonzero_before s i :=
  index_of_nonzero_before_from s (S i) i 0 0.

Lemma ind_of_nz_bef_lt_step : ∀ k m s b i n len,
  (i < n + k + 1
   → b = m + k
     → b < i
       → index_of_nonzero_before_from s n i (S (b + len)) b < i)%nat.
Proof.
intros k m s b i n len Hin Hb Hbi.
revert b i k m len Hin Hb Hbi.
induction n; intros; simpl.
 exfalso; omega.

 remember (S (b + len)) as b₁.
 destruct (lt_dec b₁ i) as [H₁| H₁]; [ idtac | assumption ].
 destruct (null_coeff_range_length rng s (S b₁)) as [len₁| ]; [ idtac | assumption ].
 rewrite <- Nat.add_succ_l, <- Heqb₁.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hin.
 subst b.
 rewrite Nat.add_shuffle0 in Heqb₁.
 rewrite <- Nat.add_succ_r in Heqb₁.
 eapply IHn; eassumption.
Qed.

Lemma index_of_nonzero_before_from_lt : ∀ s n i b last_b,
  (last_b < i
   → i < n
     → index_of_nonzero_before_from s n i b last_b < i)%nat.
Proof.
intros s n i b last_b Hbi Hin.
destruct n; simpl.
 exfalso; fast_omega Hin.

 destruct (lt_dec b i) as [H₁| H₁]; [ clear Hbi | assumption ].
 destruct (null_coeff_range_length rng s (S b)) as [len₁| ]; [ idtac | assumption ].
 apply (ind_of_nz_bef_lt_step O b).
  rewrite <- Nat.add_assoc, Nat.add_comm; assumption.

  rewrite Nat.add_comm; reflexivity.

  assumption.
Qed.

Lemma index_of_nonzero_before_lt : ∀ s i,
  (0 < i
   → index_of_nonzero_before s i < i)%nat.
Proof.
intros s i Hi.
apply index_of_nonzero_before_from_lt; [ assumption | idtac ].
apply Nat.lt_succ_r; reflexivity.
Qed.

Lemma ind_of_nz_bef_rgt_bnd : ∀ k c m s b i n len len₁,
  (i < c + k + 1
   → b = m + k
     → b < i
       → null_coeff_range_length rng s (S n) = fin len
         → null_coeff_range_length rng s (S b) = fin len₁
           → index_of_nonzero_before_from s c i (S (b + len₁)) b = n
             → i ≤ S n + len)%nat.
Proof.
intros k c m s b i n len len₁ Hic Hb Hbi Hlen Hlen₁ Hn.
revert k m b len₁ Hic Hb Hbi Hlen₁ Hn.
induction c; intros; simpl in Hn; [ exfalso; omega | idtac ].
destruct (lt_dec (S (b + len₁)) i) as [H₁| H₁].
 remember (null_coeff_range_length rng s (S (S (b + len₁)))) as len₂ eqn:Hlen₂ .
 symmetry in Hlen₂.
 destruct len₂ as [len₂| ].
  clear Hlen₁.
  rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hic.
  eapply IHc; try eassumption.
  rewrite Hb, Nat.add_shuffle0, Nat.add_succ_r.
  reflexivity.

  subst n.
  rewrite Hlen₂ in Hlen; discriminate Hlen.

 subst n.
 rewrite Hlen₁ in Hlen.
 injection Hlen; clear Hlen; intros; subst len.
 simpl; apply Nat.nlt_ge; assumption.
Qed.

Lemma index_of_nonzero_before_from_right_bound : ∀ s c i b n last_b len,
  (b < i
   → last_b < i
     → i < c
       → index_of_nonzero_before_from s c i b last_b = n
         → null_coeff_range_length rng s (S n) = fin len
           → i ≤ S n + len)%nat.
Proof.
intros s c i b n last_b len Hbi Hli Hic Hn Hlen.
destruct c; simpl in Hn.
 apply Nat.nlt_0_r in Hic; contradiction.

 destruct (lt_dec b i) as [H₁| H₁]; [ idtac | exfalso; omega ].
 remember (null_coeff_range_length rng s (S b)) as len₁ eqn:Hlen₁ .
 symmetry in Hlen₁.
 destruct len₁ as [len₁| ].
  eapply (ind_of_nz_bef_rgt_bnd 0 c); try eassumption.
   rewrite Nat.add_comm, Nat.add_0_r; assumption.

   rewrite Nat.add_0_r; reflexivity.

  subst n.
  rewrite Hlen₁ in Hlen; discriminate Hlen.
Qed.

Lemma index_of_nonzero_before_right_bound : ∀ s i n len,
  (0 < i
   → index_of_nonzero_before s i = n
     → null_coeff_range_length rng s (S n) = fin len
       → i ≤ S n + len)%nat.
Proof.
intros s i n len Hi Hn Hlen.
eapply index_of_nonzero_before_from_right_bound; try eassumption.
apply Nat.lt_succ_r; reflexivity.
Qed.
*)

Lemma series_nth_0_in_interval_from_any : ∀ s i c b k,
  (i < c)%nat
  → (∀ n, (Pos.to_nat k | nth_null_coeff_range_length s n b)%nat)
    → (Pos.to_nat k |
       nth_null_coeff_range_length s
         (pred (rank_of_nonzero_after_from s c (b + i) b)) b)%nat
      → i mod Pos.to_nat k ≠ O
        → (series_nth_rng rng (b + i) s = 0)%rng.
Proof.
(* à nettoyer *)
intros s i c b k Hic Has Hs Hm.
remember (pred (rank_of_nonzero_after_from s c (b + i) b)) as n eqn:Hn .
symmetry in Hn.
destruct c; [ exfalso; omega | simpl in Hn ].
destruct i.
 rewrite Nat.mod_0_l in Hm; [ idtac | apply Pos2Nat_ne_0 ].
 exfalso; apply Hm; reflexivity.

 apply Nat.succ_lt_mono in Hic.
 destruct (lt_dec b (b + S i)) as [H₁| H₁]; [ idtac | exfalso; omega ].
 clear H₁.
 remember (null_coeff_range_length rng s (S b)) as len eqn:Hlen .
 symmetry in Hlen.
 destruct len as [len| ].
  Focus 2.
  rewrite Nat.add_succ_r.
  apply null_coeff_range_length_iff in Hlen; simpl in Hlen.
  apply Hlen.

  simpl in Hn.
  revert i b len n Has Hic Hlen Hn Hs Hm.
  induction c; intros; [ exfalso; fast_omega Hic | idtac ].
  simpl in Hn.
  destruct (lt_dec (S (b + len)) (b + S i)) as [H₁| H₁].
   remember (null_coeff_range_length rng s (S (S (b + len)))) as len₁ eqn:Hlen₁ .
   symmetry in Hlen₁.
   destruct len₁ as [len₁| ].
    destruct n; [ discriminate Hn | idtac ].
    apply Nat.succ_inj in Hn.
    destruct i.
     exfalso; fast_omega H₁.

     apply Nat.succ_lt_mono in Hic.
     replace (b + S (S i))%nat with (S (b + len) + S (i - len))%nat by omega.
     eapply IHc; try eassumption.
      intros m.
      pose proof (Has (S m)) as H.
      simpl in H.
      rewrite Hlen in H.
      assumption.

      omega.

      replace (S (b + len) + S (i - len))%nat with (b + S (S i))%nat by omega.
      simpl.
      apply Hn.

      simpl in Hs.
      rewrite Hlen in Hs.
      assumption.

      replace (S (S i)) with (S (i - len) + S len)%nat in Hm by omega.
      pose proof (Has O) as H.
      simpl in H.
      rewrite Hlen in H.
      rewrite Nat.add_mod in Hm; auto.
      destruct H as (c₁, Hc₁).
      rewrite Hc₁ in Hm.
      rewrite Nat.mod_mul, Nat.add_0_r in Hm; auto.
      rewrite Nat.mod_mod in Hm; auto.

    apply null_coeff_range_length_iff in Hlen₁; simpl in Hlen₁.
    pose proof (Hlen₁ (i - len - 1)%nat) as H.
    replace (b + S i)%nat with (S (S (b + len + (i - len - 1)))) by omega.
    assumption.

   apply Nat.nlt_ge in H₁.
   rewrite Nat.add_succ_r in H₁.
   apply Nat.succ_le_mono in H₁.
   apply Nat.add_le_mono_l in H₁.
   destruct (eq_nat_dec i len) as [H₂| H₂].
    subst n len.
    simpl in Hs.
    rewrite Hlen in Hs.
    destruct Hs as (c₁, Hc₁).
    rewrite Hc₁ in Hm.
    rewrite Nat.mod_mul in Hm; auto.
    exfalso; apply Hm; reflexivity.

    apply null_coeff_range_length_iff in Hlen; simpl in Hlen.
    destruct Hlen as (Hz, Hnz).
    rewrite Nat.add_succ_r.
    apply Hz.
    apply le_neq_lt; assumption.
Qed.

Lemma series_nth_0_in_interval : ∀ s k,
  (∀ n, (Pos.to_nat k | nth_null_coeff_range_length s n 0)%nat)
  → ∀ i,
    (i mod Pos.to_nat k ≠ 0)%nat
    → (series_nth_rng rng i s = 0)%rng.
Proof.
intros s k Hs i Hi.
remember (rank_of_nonzero_before s i) as cnt.
pose proof (Hs cnt) as H.
subst cnt.
unfold rank_of_nonzero_before in H.
destruct i.
 rewrite Nat.mod_0_l in Hi; [ idtac | apply Pos2Nat_ne_0 ].
 exfalso; apply Hi; reflexivity.

 replace (S i) with (0 + S i)%nat in H by reflexivity.
 apply series_nth_0_in_interval_from_any in H; auto.
Qed.

Lemma series_stretch_shrink : ∀ s k,
  (k | greatest_series_x_power rng s 0)%positive
  → (series_stretch k (series_shrink k s) = s)%ser.
Proof.
intros s k Hk.
constructor; intros i.
unfold series_nth_rng; simpl.
rewrite Nbar.fold_sub.
rewrite Nbar.fold_div.
rewrite Nbar.fold_div_sup.
remember (fin (Pos.to_nat k)) as kn eqn:Hkn .
destruct (Nbar.lt_dec (fin i) (Nbar.div_sup (stop s) kn * kn)) as [H₁| H₁].
 destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂].
  unfold series_nth_rng.
  apply Nat.mod_divides in H₂.
   destruct H₂ as (c, Hc).
   rewrite Hc.
   rewrite Nat.mul_comm.
   rewrite Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
   rewrite Nat.mul_comm, <- Hc.
   destruct (Nbar.lt_dec (fin c) (stop (series_shrink k s))) as [H₂| H₂].
    destruct (Nbar.lt_dec (fin i) (stop s)) as [H₃| H₃].
     simpl; rewrite Nat.mul_comm, <- Hc.
     reflexivity.

     exfalso; apply H₃; clear H₃.
     simpl in H₂.
     rewrite Nbar.fold_sub in H₂.
     rewrite Nbar.fold_div in H₂.
     rewrite Nbar.fold_div_sup in H₂.
     apply Nbar.lt_div_sup_lt_mul_r in H₂.
     simpl in H₂.
     rewrite Nat.mul_comm, <- Hc in H₂.
     assumption.

    simpl in H₂.
    rewrite Nbar.fold_sub in H₂.
    rewrite Nbar.fold_div in H₂.
    rewrite Nbar.fold_div_sup in H₂.
    destruct (Nbar.lt_dec (fin i) (stop s)) as [H₃| H₃].
     exfalso; apply H₂; clear H₂.
     apply Nbar.lt_mul_r_lt_div_sup.
      apply Nbar.lt_fin, Pos2Nat.is_pos.

      simpl; rewrite Nat.mul_comm, <- Hc.
      assumption.

     reflexivity.

   apply Pos2Nat_ne_0.

  destruct (Nbar.lt_dec (fin i) (stop s)) as [H₃| H₃].
   destruct Hk as (c, Hk).
   apply greatest_series_x_power_iff in Hk.
   unfold is_the_greatest_series_x_power in Hk.
   destruct Hk as (Hz, Hnz).
   symmetry.
   assert (i mod Pos.to_nat (c * k) ≠ 0)%nat as H.
    intros H.
    apply Nat.mod_divides in H.
     destruct H as (d, Hd).
     rewrite Pos2Nat.inj_mul, Nat.mul_shuffle0 in Hd.
     rewrite Hd in H₂.
     rewrite Nat.mod_mul in H₂; [ idtac | apply Pos2Nat_ne_0 ].
     revert H₂; apply Nat.lt_irrefl.

     apply Pos2Nat_ne_0.

    apply series_nth_0_in_interval with (s := s) in H; [ idtac | assumption ].
    unfold series_nth_rng in H.
    destruct (Nbar.lt_dec (fin i) (stop s)); [ assumption | contradiction ].

   reflexivity.

 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₂| H₂]; [ idtac | reflexivity ].
 exfalso; apply H₁.
 eapply Nbar.lt_le_trans; [ eassumption | idtac ].
 apply Nbar.le_mul_div_sup.
 subst kn.
 intros H.
 injection H; apply Pos2Nat_ne_0.
Qed.

(*
Lemma greatest_series_x_power_lim_stretch : ∀ s n k cnt,
  greatest_series_x_power_lim rng cnt (series_stretch k s) (Pos.to_nat k * n) =
    (Pos.to_nat k * greatest_series_x_power_lim rng cnt s n)%nat.
Proof.
-- à nettoyer
intros s n k cnt.
revert s n k.
induction cnt; intros.
 auto.

 simpl.
 remember
  (null_coeff_range_length rng (series_stretch k s) (S (Pos.to_nat k * n))) as m
  eqn:Hm .
 symmetry in Hm.
 destruct m as [m| ].
  rewrite divmod_mod.
  remember (null_coeff_range_length rng s (S n)) as p eqn:Hp .
  symmetry in Hp.
  destruct p as [p| ].
   rewrite divmod_mod.
   assert (m = Pos.to_nat k * S p - 1)%nat.
    Focus 2.
    subst m.
    rewrite Nat.add_sub_assoc.
     rewrite <- Nat.sub_succ_l.
      rewrite Nat.sub_succ.
      rewrite Nat.sub_0_r.
      rewrite <- Nat.mul_add_distr_l.
      rewrite <- Nat.sub_succ_l.
       rewrite Nat.sub_succ.
       rewrite Nat.sub_0_r.
       rewrite IHcnt.
       rewrite Nat.mul_mod_distr_l.
        rewrite Nat.gcd_mul_mono_l.
        rewrite Nat.add_succ_r.
        reflexivity.

        intros H; discriminate H.

        apply Pos2Nat_ne_0.

       remember (Pos.to_nat k) as kn eqn:Hkn .
       symmetry in Hkn.
       destruct kn.
        exfalso; revert Hkn; apply Pos2Nat_ne_0.

        simpl.
        apply le_n_S, Nat.le_0_l.

      rewrite <- Nat.mul_add_distr_l.
      remember (Pos.to_nat k) as kn eqn:Hkn .
      symmetry in Hkn.
      destruct kn.
       exfalso; revert Hkn; apply Pos2Nat_ne_0.

       simpl.
       rewrite Nat.add_succ_r; simpl.
       apply le_n_S, Nat.le_0_l.

     remember (Pos.to_nat k) as kn eqn:Hkn .
     symmetry in Hkn.
     destruct kn.
      exfalso; revert Hkn; apply Pos2Nat_ne_0.

      simpl.
      apply le_n_S, Nat.le_0_l.

    rewrite Nat.mul_comm in Hm.
    rewrite null_coeff_range_length_stretch_succ with (p := p) in Hm; try assumption.
    symmetry in Hm.
    rewrite Nat.mul_comm.
    injection Hm; intros; assumption.

   rewrite Nat.mul_comm in Hm.
   rewrite null_coeff_range_length_stretch_succ_inf in Hm.
    discriminate Hm.

    assumption.

  rewrite Nat.mul_comm in Hm.
  remember (null_coeff_range_length rng s (S n)) as p eqn:Hp .
  symmetry in Hp.
  destruct p as [p| ]; [ idtac | auto ].
  apply null_coeff_range_length_stretch_succ with (k := k) in Hp.
  rewrite Hm in Hp.
  discriminate Hp.
Qed.
*)

Lemma nth_null_coeff_range_length_stretch : ∀ s b n k,
  nth_null_coeff_range_length (series_stretch k s) n
    (b * Pos.to_nat k) =
  (Pos.to_nat k * nth_null_coeff_range_length s n b)%nat.
Proof.
intros s b n k.
revert b.
induction n; intros.
 simpl.
 remember (null_coeff_range_length rng s (S b)) as len eqn:Hlen .
 symmetry in Hlen.
 destruct len as [len| ].
  erewrite null_coeff_range_length_stretch_succ; eauto .
  rewrite Nat.mul_comm.
  remember (Pos.to_nat k * S len)%nat as x eqn:Hx .
  symmetry in Hx.
  destruct x; simpl.
   apply Nat.mul_eq_0 in Hx.
   destruct Hx as [Hx| Hx]; [ idtac | discriminate Hx ].
   exfalso; revert Hx; apply Pos2Nat_ne_0.

   rewrite Nat.sub_0_r; reflexivity.

  rewrite null_coeff_range_length_stretch_succ_inf; [ idtac | assumption ].
  rewrite Nat.mul_comm; reflexivity.

 simpl.
 remember (null_coeff_range_length rng s (S b)) as len eqn:Hlen .
 symmetry in Hlen.
 destruct len as [len| ].
  erewrite null_coeff_range_length_stretch_succ; eauto .
  rewrite Nat.add_sub_assoc.
   rewrite <- Nat.mul_add_distr_r.
   rewrite Nat.add_succ_r.
   remember (S (b + len) * Pos.to_nat k)%nat as x eqn:Hx .
   symmetry in Hx.
   destruct x; simpl.
    apply Nat.mul_eq_0 in Hx.
    destruct Hx as [Hx| Hx]; [ discriminate Hx | idtac ].
    exfalso; revert Hx; apply Pos2Nat_ne_0.

    rewrite Nat.sub_0_r, <- Hx.
    apply IHn.

   remember (Pos.to_nat k) as kn eqn:Hkn .
   symmetry in Hkn.
   destruct kn; [ exfalso; revert Hkn; apply Pos2Nat_ne_0 | idtac ].
   simpl; apply le_n_S, Nat.le_0_l.

  rewrite null_coeff_range_length_stretch_succ_inf; [ idtac | assumption ].
  rewrite Nat.mul_comm; reflexivity.
Qed.

(*
Lemma stretch_is_not_a_series_in_x_power : ∀ s b k k₁,
  (∃ n,
   Pos.to_nat k * nth_null_coeff_range_length s n b mod
   Pos.to_nat k₁ ≠ 0)%nat
  → ¬is_a_series_in_x_power (series_stretch k s) (b * Pos.to_nat k) k₁.
Proof.
intros s b k k₁ (n, Hn) H.
unfold is_a_series_in_x_power in H.
rewrite <- nth_null_coeff_range_length_stretch in Hn.
apply Hn.
apply Nat.mod_divides; auto.
apply Nat_divides_l, H.
Qed.
*)

Lemma exists_nth_null_coeff_range_length_stretch : ∀ s b k k₁,
  (∃ n, Pos.to_nat k * nth_null_coeff_range_length s n b mod k₁ ≠ 0)%nat
  → (∃ n,
     nth_null_coeff_range_length (series_stretch k s) n
       (b * Pos.to_nat k) mod k₁ ≠ 0)%nat.
Proof.
intros s b k k₁ (n, H).
exists n.
rewrite nth_null_coeff_range_length_stretch.
assumption.
Qed.

(* redéfinition de Plcm: Pos_lcm... euh... pas très joli joli, ça... *)
Definition Pos_lcm a b := Pos.of_nat (Nat.lcm (Pos.to_nat a) (Pos.to_nat b)).

Lemma Pos2Nat_lcm : ∀ a b,
  Pos.to_nat (Pos_lcm a b) = Nat.lcm (Pos.to_nat a) (Pos.to_nat b).
Proof.
intros a b.
unfold Pos_lcm.
rewrite Nat2Pos.id.
 reflexivity.

 intros H.
 apply Nat.lcm_eq_0 in H.
 destruct H; revert H; apply Pos2Nat_ne_0.
Qed.

(*
Lemma series_in_x_power_lcm : ∀ s b k l,
  is_a_series_in_x_power s b k
  → is_a_series_in_x_power s b l
    → is_a_series_in_x_power s b (Pos_lcm k l).
Proof.
intros s b k l Hk Hl.
unfold is_a_series_in_x_power in Hk, Hl |- *.
destruct n.
 pose proof (Hk O) as Hk₀.
 pose proof (Hl O) as Hl₀.
 simpl in Hk₀, Hl₀ |- *.
 remember (null_coeff_range_length rng s (S b)) as len eqn:Hlen .
 symmetry in Hlen.
 destruct len; rewrite Pos2Nat_lcm; apply Nat_lcm_divides; auto.

 pose proof (Hk (S n)) as Hkn.
 pose proof (Hl (S n)) as Hln.
 simpl in Hkn, Hln |- *.
 remember (null_coeff_range_length rng s (S b)) as len eqn:Hlen .
 symmetry in Hlen.
 destruct len; rewrite Pos2Nat_lcm; apply Nat_lcm_divides; auto.
Qed.

Lemma series_in_x_power_divides_greatest : ∀ s b k l,
  is_a_series_in_x_power s b k
  → is_the_greatest_series_x_power s b l
    → (k | l)%positive.
Proof.
intros s b k l Hk Hl.
unfold is_the_greatest_series_x_power in Hl.
destruct Hl as (Hl, Hkl).
remember Hl as Hlcm; clear HeqHlcm.
eapply series_in_x_power_lcm in Hlcm; [ idtac | eexact Hk ].
destruct (lt_dec (Pos.to_nat l) (Pos.to_nat (Pos_lcm k l))) as [H₁| H₁].
 apply Pos2Nat.inj_lt in H₁.
 apply Hkl in H₁.
 unfold is_a_series_in_x_power in Hlcm.
 destruct H₁ as (n, Hn).
 exfalso; apply Hn, Hlcm.

 apply Nat.nlt_ge in H₁.
 rewrite Pos2Nat_lcm in H₁.
 assert (Pos.to_nat k ≠ 0)%nat as Hknz by auto.
 apply Nat_le_lcm_l with (a := Pos.to_nat l) in Hknz.
 rewrite Nat.lcm_comm in Hknz.
 apply Nat.le_antisymm in H₁; [ idtac | assumption ].
 assert (Pos.to_nat k | Pos.to_nat l)%nat as Hdkl.
  rewrite H₁.
  apply Nat_divides_lcm_l.
  
  destruct Hdkl as (c, Hc).
  exists (Pos.of_nat c).
  apply Pos2Nat.inj.
  rewrite Pos2Nat.inj_mul.
  rewrite Nat2Pos.id; [ assumption | idtac ].
  destruct c; [ idtac | intros H; discriminate H ].
  exfalso; revert Hc; apply Pos2Nat_ne_0.
Qed.
*)

Definition is_the_greatest_series_x_power₂ s b k :=
  is_a_series_in_x_power s b k ∧
  (∀ u, (1 < u)%positive
   → ∃ n, ¬(Pos.to_nat (u * k) | nth_null_coeff_range_length s n b)).

Lemma is_the_greatest_series_x_power_equiv : ∀ s b k,
  is_the_greatest_series_x_power s b k
  ↔ is_the_greatest_series_x_power₂ s b k.
Proof.
intros s b k.
split; intros H.
 unfold is_the_greatest_series_x_power in H.
 unfold is_the_greatest_series_x_power₂.
 destruct H as (Hp, Hnp).
 split; [ assumption | idtac ].
 intros n Hn.
 remember (Pos.to_nat n) as nn eqn:Hnn .
 symmetry in Hnn.
 destruct nn; [ exfalso; revert Hnn; apply Pos2Nat_ne_0 | idtac ].
 destruct nn.
  rewrite <- Pos2Nat.inj_1 in Hnn.
  apply Pos2Nat.inj in Hnn.
  subst n; exfalso; revert Hn; apply Pos.lt_irrefl.

  apply Hnp.
  rewrite <- SuccNat2Pos.id_succ in Hnn.
  apply Pos2Nat.inj in Hnn.
  subst n; simpl.
  rewrite Pos.of_nat_succ.
  destruct nn.
   rewrite Pos.mul_comm; simpl.
   replace k with (k * 1)%positive .
    rewrite <- Pos.mul_assoc; simpl.
    apply Pos.mul_lt_mono_l.
    apply Pos2Nat.inj_lt.
    unfold Pos.to_nat; simpl.
    apply Nat.lt_1_2.

    rewrite Pos.mul_1_r; reflexivity.

   replace k with (1 * k)%positive by reflexivity.
   rewrite Pos.mul_assoc.
   apply Pos.mul_lt_mono_r.
   rewrite Pos.mul_1_r.
   apply Pos2Nat.inj_lt.
   rewrite Pos2Nat.inj_succ.
   rewrite Nat2Pos.id; [ idtac | intros H; discriminate H ].
   unfold Pos.to_nat; simpl.
   apply lt_n_S, Nat.lt_0_succ.

 unfold is_the_greatest_series_x_power₂ in H.
 destruct H as (Hp, Hnp).
 split; [ assumption | idtac ].
 intros k₁ Hk₁.
 remember (Pos_lcm k k₁) as kk eqn:Hkk .
 remember Hkk as Hk; clear HeqHk.
 apply Pos2Nat.inj_iff in Hkk.
 rewrite Pos2Nat_lcm in Hkk.
 pose proof (Nat_divides_lcm_l (Pos.to_nat k) (Pos.to_nat k₁)) as Hdl.
 destruct Hdl as (u, Hu).
 rewrite <- Hkk in Hu.
 destruct u; [ exfalso; revert Hu; apply Pos2Nat_ne_0 | idtac ].
 destruct u.
  rewrite Nat.mul_1_l in Hu.
  apply Pos2Nat.inj_iff in Hu.
  move Hu at top; subst kk.
  rewrite Hk in Hk₁.
  apply Pos2Nat.inj_lt in Hk₁.
  rewrite Pos2Nat_lcm in Hk₁.
  apply Nat.nle_gt in Hk₁.
  exfalso; apply Hk₁.
  rewrite Nat.lcm_comm.
  apply Nat_le_lcm_l; auto.

  assert (1 < Pos.of_nat (S (S u)))%positive as H₁.
   apply Pos2Nat.inj_lt.
   rewrite Nat2Pos.id; [ idtac | intros H; discriminate H ].
   rewrite Pos2Nat.inj_1.
   apply lt_n_S, Nat.lt_0_succ.

   apply Hnp in H₁.
   destruct H₁ as (m, Hm).
   rewrite Pos2Nat.inj_mul in Hm.
   rewrite Nat2Pos.id in Hm; [ idtac | intros H; discriminate H ].
   rewrite <- Hu, Hkk in Hm.
   exists m.
   intros H₁; apply Hm.
   unfold is_a_series_in_x_power in Hp.
   pose proof (Hp m) as H₂.
   apply Nat_lcm_divides; auto.
Qed.

(*
Lemma Nat_exists_mul_mod_distr_l : ∀ A (a : A → nat) b c,
  (b ≠ 0
   → c ≠ 0
     → (∃ n, a n mod b ≠ 0)
      → ∃ n, (c * a n) mod (c * b) ≠ 0)%nat.
Proof.
intros A a b c Hb Hc Hn.
destruct Hn as (n, Hn).
exists n.
rewrite Nat.mul_mod_distr_l; try assumption.
intros H; apply Hn.
apply Nat.mul_eq_0 in H.
destruct H; [ contradiction | assumption ].
Qed.
*)

Lemma greatest_series_x_power_stretch : ∀ s b k,
  greatest_series_x_power rng (series_stretch k s) (b * Pos.to_nat k) =
    (k * greatest_series_x_power rng s b)%positive.
Proof.
(* à nettoyer *)
intros s b k.
remember (greatest_series_x_power rng s b) as m eqn:Hm .
symmetry in Hm.
apply greatest_series_x_power_iff.
apply is_the_greatest_series_x_power_equiv.
unfold is_the_greatest_series_x_power₂.
split.
 intros n.
 apply greatest_series_x_power_iff in Hm.
 destruct Hm as (Hm, Hnm).
 unfold is_a_series_in_x_power in Hm.
 rewrite nth_null_coeff_range_length_stretch.
 apply Nat_divides_l.
 apply Nat.mod_divides; auto.
 rewrite Pos2Nat.inj_mul.
 rewrite Nat.mul_mod_distr_l; auto.
 eapply Nat.mul_eq_0; right.
 apply Nat.mod_divides; auto.
 apply Nat_divides_l, Hm.

 intros u Hu.
 rewrite Pos.mul_comm, <- Pos.mul_assoc.
 rewrite Pos2Nat.inj_mul.
 apply greatest_series_x_power_iff in Hm.
 unfold is_the_greatest_series_x_power in Hm.
 destruct Hm as (Hm, Hmk).
 assert (m < m * u)%positive as Hmu.
  Focus 2.
  apply Hmk in Hmu.
  destruct Hmu as (n, Hn).
  exists n.
  intros H₁; apply Hn.
  rewrite nth_null_coeff_range_length_stretch in H₁.
  apply Nat.mod_divide in H₁.
   rewrite Nat.mul_mod_distr_l in H₁; auto.
   apply Nat.mul_eq_0_r in H₁; auto.
   apply Nat.mod_divide; auto.

   rewrite <- Pos2Nat.inj_mul.
   apply Pos2Nat_ne_0.

  apply Pos2Nat.inj_lt.
  apply Pos2Nat.inj_lt in Hu.
  rewrite Pos2Nat.inj_1 in Hu.
  rewrite Pos2Nat.inj_mul.
  remember (Pos.to_nat u) as un eqn:Hun .
  symmetry in Hun.
  destruct un.
   apply Nat.nle_gt in Hu.
   exfalso; apply Hu, Nat.le_0_l.

   destruct un; [ exfalso; revert Hu; apply Nat.lt_irrefl | idtac ].
   remember (Pos.to_nat m) as um eqn:Hum .
   symmetry in Hum.
   destruct um; [ exfalso; revert Hum; apply Pos2Nat_ne_0 | idtac ].
   rewrite Nat.mul_comm; simpl.
   apply lt_n_S.
   rewrite Nat.add_succ_r.
   apply le_n_S.
   apply le_plus_l.
Qed.
