(* $Id: Puiseux_series.v,v 1.718 2013-09-27 11:51:47 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Misc.
Require Import Series.
Require Import Nbar.

Set Implicit Arguments.

(* [first_nonzero fld s] return the position of the first non null
   coefficient in the series [s]. *)
Definition first_nonzero : ∀ α, field α → series α → Nbar.
Admitted.

(*
Definition is_zero : ∀ α, field α → α → bool.
Admitted.

Definition stretching_factor_fin α (fld : field α) n s :=
  let fix loop_i cnt i k :=
    match cnt with
    | O => true
    | S cnt' =>
        if zerop (i mod k) then loop_i cnt' (S i) k
        else if is_zero fld (series_nth_fld fld i s) then loop_i cnt' (S i) k
        else false
    end
  in
  let fix loop_k cnt k :=
    match cnt with
    | O => 1%nat
    | S cnt' => if loop_i n O k then k else loop_k cnt' k
    end
 in
 loop_k n 2.

Definition stretching_factor α fld s :=
  match stop s with
  | fin n => stretching_factor_fin fld n s
  | inf => stretching_factor_inf fld s
  end.
*)

Definition stretching_factor : ∀ α, field α → series α → nat.
Admitted.

Section fld.

Variable α : Type.
Variable fld : field α.
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).
Notation "a ≃ b" := (eq_series fld a b) (at level 70).

Axiom first_nonzero_iff : ∀ s n,
  first_nonzero fld s = n
  ↔ match n with
    | fin k =>
        (∀ i, (i < k)%nat → series_nth_fld fld i s ≍ zero fld) ∧
        series_nth_fld fld k s ≭ zero fld
    | inf =>
        (∀ i, series_nth_fld fld i s ≍ zero fld)
    end.

Definition is_stretching_factor s n k :=
  (k > 1)%nat ∧
  (∀ i, i mod k ≠ O → series_nth_fld fld (n + i) s ≍ zero fld) ∧
  (∀ k₁, (1 < k₁ < k)%nat →
     ∃ i, i mod k₁ ≠ O ∧ series_nth_fld fld (n + i) s ≭ zero fld).

Axiom stretching_factor_iff : ∀ s k,
  stretching_factor fld s = k
  ↔ match first_nonzero fld s with
    | fin n =>
        is_stretching_factor s n k ∨
        (k = 1%nat ∧ ∀ k', not (is_stretching_factor s n k'))
    | ∞ =>
        k = O
    end.

Definition stretch_series k s :=
  {| terms i :=
       if zerop (i mod Pos.to_nat k) then
         series_nth_fld fld (i / Pos.to_nat k) s
       else zero fld;
     stop :=
       stop s * fin (Pos.to_nat k) |}.

Definition series_pad_left n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n);
     stop := stop s + fin n |}.

Record nz_ps α := mknz
  { nz_terms : series α;
    nz_valnum : Z;
    nz_comden : positive }.

Inductive puiseux_series α :=
  | NonZero : nz_ps α → puiseux_series α
  | Zero : puiseux_series α.

Definition div_sup x y := ((x + y - 1) / y)%nat.
Definition Nbar_div_sup x y := Nbar.div (x + y - 1) y.

Definition normalise_series n k (s : series α) :=
  match k with
  | O => series_0 fld
  | S _ =>
      {| terms i := terms s (n + i * k);
         stop := Nbar_div_sup (stop s - fin n) (fin k) |}
  end.

Definition normalise_nz nz :=
  match first_nonzero fld (nz_terms nz) with
  | fin n =>
      let k := stretching_factor fld (nz_terms nz) in
      NonZero
        {| nz_terms := normalise_series n k (nz_terms nz);
           nz_valnum := (nz_valnum nz + Z.of_nat n) / Z.of_nat k;
           nz_comden := Z.to_pos (' nz_comden nz / Z.of_nat k) |}
  | ∞ =>
      Zero _
  end.

Inductive eq_norm_ps : puiseux_series α → puiseux_series α → Prop :=
  | eq_norm_ps_base : ∀ nz₁ nz₂,
      nz_valnum nz₁ = nz_valnum nz₂
      → nz_comden nz₁ = nz_comden nz₂
        → nz_terms nz₁ ≃ nz_terms nz₂
          → eq_norm_ps (NonZero nz₁) (NonZero nz₂)
  | eq_norm_ps_zero :
      eq_norm_ps (Zero _) (Zero _).

Inductive eq_ps : puiseux_series α → puiseux_series α → Prop :=
  | eq_ps_base : ∀ nz₁ nz₂,
      eq_norm_ps (normalise_nz nz₁) (normalise_nz nz₂)
      → eq_ps (NonZero nz₁) (NonZero nz₂)
  | eq_ps_zero_r : ∀ nz,
      eq_series fld (nz_terms nz) (series_0 fld)
      → eq_ps (NonZero nz) (Zero _)
  | eq_ps_zero_l : ∀ nz,
      eq_series fld (nz_terms nz) (series_0 fld)
      → eq_ps (Zero _) (NonZero nz)
  | eq_ps_zero :
      eq_ps (Zero _) (Zero _).

Notation "a ≈ b" := (eq_ps a b) (at level 70).

Definition ps_zero : puiseux_series α := Zero _.

Definition ps_monom (c : α) pow :=
  NonZero
    {| nz_terms := {| terms i := c; stop := 1 |};
       nz_valnum := Qnum pow;
       nz_comden := Qden pow |}.

Definition ps_const c : puiseux_series α := ps_monom c 0.
Definition ps_one := ps_const (one fld).

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
  → ∀ i : nat, series_nth_fld fld i s = zero fld.
Proof.
intros s H i.
unfold series_nth_fld; simpl.
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

Lemma stretch_series_1 : ∀ s, stretch_series 1 s ≃ s.
Proof.
intros s.
unfold stretch_series; simpl.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite divmod_div, Nbar.mul_1_r, Nat.div_1_r.
destruct (Nbar.lt_dec (fin i) (stop s)); reflexivity.
Qed.

Theorem eq_norm_ps_refl : reflexive _ eq_norm_ps.
Proof.
intros ps.
destruct ps as [nz| ]; [ idtac | constructor ].
constructor; reflexivity.
Qed.

Theorem eq_norm_ps_sym : symmetric _ eq_norm_ps.
Proof.
intros ps₁ ps₂ H.
induction H; constructor; symmetry; assumption.
Qed.

Theorem eq_norm_ps_trans : transitive _ eq_norm_ps.
Proof.
intros ps₁ ps₂ ps₃ H₁ H₂.
inversion H₁.
 inversion H₂.
  rewrite <- H3 in H7.
  injection H7; clear H7; intros; subst nz₁0.
  constructor; etransitivity; eassumption.

  rewrite <- H4 in H3; discriminate H3.

 inversion H₂; [ idtac | constructor ].
 rewrite <- H0 in H4; discriminate H4.
Qed.

End fld.

Add Parametric Relation α (fld : field α) : (puiseux_series α)
   (eq_norm_ps fld)
 reflexivity proved by (eq_norm_ps_refl fld)
 symmetry proved by (eq_norm_ps_sym (fld := fld))
 transitivity proved by (eq_norm_ps_trans (fld := fld))
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

Add Parametric Morphism α (fld : field α) : (first_nonzero fld)
with signature (eq_series fld) ==> eq as first_nonzero_morph.
Proof.
intros s₁ s₂ Heq.
remember (first_nonzero fld s₁) as n₁ eqn:Hn₁ .
remember (first_nonzero fld s₂) as n₂ eqn:Hn₂ .
symmetry in Hn₁, Hn₂.
apply first_nonzero_iff in Hn₁.
apply first_nonzero_iff in Hn₂.
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

Add Parametric Morphism α (fld : field α) : (stretching_factor fld)
with signature (eq_series fld) ==> eq as stretching_morph.
Proof.
intros s₁ s₂ Heq.
remember (stretching_factor fld s₁) as k₁ eqn:Hk₁ .
remember (stretching_factor fld s₂) as k₂ eqn:Hk₂ .
symmetry in Hk₁, Hk₂.
apply stretching_factor_iff in Hk₁.
apply stretching_factor_iff in Hk₂.
remember (first_nonzero fld s₁) as n eqn:Hn .
rewrite Heq in Hn.
rewrite <- Hn in Hk₂.
symmetry in Hn.
destruct n as [n| ]; [ idtac | subst; reflexivity ].
destruct Hk₁ as [Hk₁| Hk₁].
 destruct Hk₂ as [Hk₂| Hk₂].
  unfold is_stretching_factor in Hk₁.
  unfold is_stretching_factor in Hk₂.
  destruct Hk₁ as (Hk₁, (Hik₁, Hlt₁)).
  destruct Hk₂ as (Hk₂, (Hik₂, Hlt₂)).
  destruct (lt_eq_lt_dec k₁ k₂) as [[H₁| H₁]| H₁].
   assert (1 < k₁ < k₂)%nat as H₂.
    split; assumption.

    apply Hlt₂ in H₂.
    destruct H₂ as (j, (Hjn, Hnj)).
    exfalso; apply Hnj; rewrite <- Heq.
    apply Hik₁; assumption.

   assumption.

   assert (1 < k₂ < k₁)%nat as H₂.
    split; assumption.

    apply Hlt₁ in H₂.
    destruct H₂ as (j, (Hjn, Hnj)).
    exfalso; apply Hnj; rewrite Heq.
    apply Hik₂; assumption.

  destruct Hk₂ as (Hk₂, Hk').
  subst k₂.
  unfold is_stretching_factor in Hk₁.
  pose proof (Hk' k₁) as Hk'₁.
  exfalso; apply Hk'₁.
  unfold is_stretching_factor.
  destruct Hk₁ as (Hk₁, (Hik₁, Hlt₁)).
  split; [ assumption | idtac ].
  split.
   intros i Him.
   rewrite <- Heq.
   apply Hik₁; assumption.

   intros k₂ Hkk.
   apply Hlt₁ in Hkk.
   destruct Hkk as (i, (Hkk, Hss)).
   exists i.
   split; [ assumption | idtac ].
   rewrite <- Heq; assumption.

 destruct Hk₂ as [Hk₂| Hk₂].
  destruct Hk₁ as (Hk₁, Hk').
  subst k₁.
  unfold is_stretching_factor in Hk₂.
  pose proof (Hk' k₂) as Hk'₂.
  exfalso; apply Hk'₂.
  unfold is_stretching_factor.
  destruct Hk₂ as (Hk₂, (Hik₂, Hlt₂)).
  split; [ assumption | idtac ].
  split.
   intros i Him.
   rewrite Heq.
   apply Hik₂; assumption.

   intros k₁ Hkk.
   apply Hlt₂ in Hkk.
   destruct Hkk as (i, (Hkk, Hss)).
   exists i.
   split; [ assumption | idtac ].
   rewrite Heq; assumption.

  destruct Hk₁, Hk₂; subst; reflexivity.
Qed.

Add Parametric Morphism α (fld : field α) : (stretch_series fld) with 
signature eq ==> (eq_series fld) ==> (eq_series fld) as stretch_morph.
Proof.
intros kp s₁ s₂ Heq.
inversion Heq; subst.
clear Heq; rename H into Heq.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
unfold series_nth_fld; simpl.
unfold series_nth_fld in Heq; simpl in Heq.
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

Add Parametric Morphism α (fld : field α) : (series_pad_left fld) with 
signature eq ==> eq_series fld ==> eq_series fld as series_pad_morph.
Proof.
intros n s₁ s₂ Heq.
constructor; intros i.
inversion Heq; subst.
unfold series_nth_fld; simpl.
unfold series_nth_fld in H; simpl in H.
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

Add Parametric Morphism α (fld : field α) : (@normalise_series α fld) with 
signature eq ==> eq ==> (eq_series fld) ==> (eq_series fld) as normalise_morph.
Proof.
intros n k ps₁ ps₂ Heq.
destruct k as [| k]; [ reflexivity | idtac ].
constructor; intros i.
inversion Heq; subst.
unfold normalise_series.
remember Nbar_div_sup as f; simpl; subst f.
do 2 rewrite Nbar.fold_sub.
remember (S k) as k₁.
assert (0 < k₁)%nat as Hk by (subst k₁; apply Nat.lt_0_succ).
clear k Heqk₁; rename k₁ into k.
pose proof (H (n + i * k)%nat) as Hi.
remember Nbar_div_sup as f.
unfold series_nth_fld in Hi |- *; simpl.
do 2 rewrite Nbar.fold_sub.
subst f; unfold Nbar_div_sup.
remember ((stop ps₁ - fin n + fin k - 1) / fin k)%Nbar as d₁ eqn:Hd₁ .
remember ((stop ps₂ - fin n + fin k - 1) / fin k)%Nbar as d₂ eqn:Hd₂ .
destruct (Nbar.lt_dec (fin i) d₁) as [H₁| H₁]; subst d₁.
 destruct (Nbar.lt_dec (fin (n + i * k)) (stop ps₁)) as [H₂| H₂].
  destruct (Nbar.lt_dec (fin i) d₂) as [H₃| H₃]; subst d₂.
   destruct (Nbar.lt_dec (fin (n + i * k)) (stop ps₂)) as [H₄| H₄].
    assumption.

    exfalso; apply H₄.
    apply Nbar.lt_div_sup_lt_mul_r in H₃.
    rewrite Nbar.fin_inj_add, Nbar.add_comm.
    apply Nbar.lt_add_lt_sub_r.
    assumption.

   destruct (Nbar.lt_dec (fin (n + i * k)) (stop ps₂)) as [H₄| H₄].
    exfalso; apply H₃.
    apply Nbar.lt_mul_r_lt_div_sup.
     apply Nbar.fin_lt_mono; assumption.

     apply Nbar.lt_add_lt_sub_r.
     rewrite Nbar.add_comm; assumption.

    assumption.

  exfalso; apply H₂.
  apply Nbar.lt_div_sup_lt_mul_r in H₁.
  rewrite Nbar.fin_inj_add, Nbar.add_comm.
  apply Nbar.lt_add_lt_sub_r.
  assumption.

 destruct (Nbar.lt_dec (fin (n + i * k)) (stop ps₁)) as [H₂| H₂].
  exfalso; apply H₁.
  apply Nbar.lt_mul_r_lt_div_sup.
   apply Nbar.fin_lt_mono; assumption.

   apply Nbar.lt_add_lt_sub_r.
   rewrite Nbar.add_comm; assumption.

  destruct (Nbar.lt_dec (fin i) d₂) as [H₃| H₃]; subst d₂.
   destruct (Nbar.lt_dec (fin (n + i * k)) (stop ps₂)) as [H₄| H₄].
    assumption.

    exfalso; apply H₄.
    apply Nbar.lt_div_sup_lt_mul_r in H₃.
    rewrite Nbar.fin_inj_add, Nbar.add_comm.
    apply Nbar.lt_add_lt_sub_r.
    assumption.

   reflexivity.
Qed.

Section fld₁.

Variable α : Type.
Variable fld : field α.
Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≈ b" := (eq_ps fld a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).

Theorem eq_ps_refl : reflexive _ (eq_ps fld).
Proof.
intros ps.
destruct ps as [nz| ]; constructor; reflexivity.
Qed.

Theorem eq_ps_sym : symmetric _ (eq_ps fld).
Proof.
intros ps₁ ps₂ H.
induction H; constructor; try assumption; symmetry; assumption.
Qed.

Lemma stretch_stretch_series : ∀ a b s,
  stretch_series fld (a * b) s ≃
  stretch_series fld a (stretch_series fld b s).
Proof.
intros ap bp s.
unfold stretch_series; simpl.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
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

Lemma stretch_series_series_0 : ∀ k,
  stretch_series fld k (series_0 fld) ≃ series_0 fld.
Proof.
intros k.
constructor; intros i.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin i) 0); [ idtac | reflexivity ].
destruct (zerop (i mod Pos.to_nat k)); [ idtac | reflexivity ].
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin (i / Pos.to_nat k)) 0); reflexivity.
Qed.

Lemma stretch_series_0_if : ∀ k s,
  stretch_series fld k s ≃ series_0 fld
  → s ≃ series_0 fld.
Proof.
intros k s Hs.
constructor.
intros i.
inversion Hs; subst.
pose proof (H (i * Pos.to_nat k)%nat) as Hi.
unfold series_nth_fld in Hi; simpl in Hi.
rewrite Nat.mod_mul in Hi; [ simpl in Hi | apply Pos2Nat_ne_0 ].
rewrite Nat.div_mul in Hi; [ simpl in Hi | apply Pos2Nat_ne_0 ].
remember (stop s * fin (Pos.to_nat k))%Nbar as ss.
destruct (Nbar.lt_dec (fin (i * Pos.to_nat k)) ss).
 rewrite Hi.
 unfold series_nth_fld; simpl.
 destruct (Nbar.lt_dec (fin (i * Pos.to_nat k)) 0).
  destruct (Nbar.lt_dec (fin i) 0); reflexivity.

  destruct (Nbar.lt_dec (fin i) 0); reflexivity.

 unfold series_nth_fld; simpl.
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

Lemma stretch_pad_series_distr : ∀ kp n s,
  stretch_series fld kp (series_pad_left fld n s) ≃
  series_pad_left fld (n * Pos.to_nat kp) (stretch_series fld kp s).
Proof.
intros kp n s.
constructor; intros i.
unfold stretch_series, series_nth_fld; simpl.
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

Lemma series_pad_pad : ∀ x y ps,
  series_pad_left fld x (series_pad_left fld y ps) ≃
  series_pad_left fld (x + y) ps.
Proof.
intros x y ps.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
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

Theorem eq_ps_trans : transitive _ (eq_ps fld).
Proof.
intros ps₁ ps₂ ps₃ H₁ H₂.
induction H₁.
 inversion H₂; subst.
  constructor; etransitivity; eassumption.

  constructor.
  unfold normalise_nz in H.
  remember (first_nonzero fld (nz_terms nz₁)) as n₁ eqn:Hn₁ .
  remember (first_nonzero fld (nz_terms nz₂)) as n₂ eqn:Hn₂ .
  symmetry in Hn₁, Hn₂.
  destruct n₁ as [n₁| ].
   destruct n₂ as [n₂| ]; [ idtac | inversion H ].
   apply first_nonzero_iff in Hn₂.
   destruct Hn₂ as (_, Hn₂).
   exfalso; apply Hn₂; rewrite H1.
   unfold series_nth_fld; simpl.
   destruct (Nbar.lt_dec (fin n₂) 0); reflexivity.

   destruct n₂ as [n₂| ]; [ inversion H | idtac ].
   apply first_nonzero_iff in Hn₁.
   constructor; intros i.
   unfold series_nth_fld at 2; simpl.
   destruct (Nbar.lt_dec (fin i) 0); apply Hn₁.

 inversion H₂; subst.
  rename nz0 into nz₃.
  constructor.
  unfold normalise_nz.
  rewrite H, H0.
  remember (first_nonzero fld (series_0 fld)) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ]; [ idtac | reflexivity ].
  apply first_nonzero_iff in Hn.
  destruct Hn as (_, Hn).
  exfalso; apply Hn.
  unfold series_nth_fld; simpl.
  destruct (Nbar.lt_dec (fin n) 0); reflexivity.

  constructor; assumption.

 inversion H₂; constructor; subst.
 unfold normalise_nz in H1.
 rename nz into nz₁.
 remember (first_nonzero fld (nz_terms nz₁)) as n₁ eqn:Hn₁ .
 remember (first_nonzero fld (nz_terms nz₂)) as n₂ eqn:Hn₂ .
 symmetry in Hn₁, Hn₂.
 destruct n₁ as [n₁| ].
  rewrite H in Hn₁.
  apply first_nonzero_iff in Hn₁.
  destruct Hn₁ as (_, Hn₁).
  exfalso; apply Hn₁.
  unfold series_nth_fld; simpl.
  destruct (Nbar.lt_dec (fin n₁) 0); reflexivity.

  destruct n₂ as [n₂| ]; [ inversion H1 | idtac ].
  apply first_nonzero_iff in Hn₂.
  constructor; intros i.
  unfold series_nth_fld at 2; simpl.
  destruct (Nbar.lt_dec (fin i) 0); apply Hn₂.

 assumption.
Qed.

End fld₁.

Add Parametric Relation α (fld : field α) : (puiseux_series α) (eq_ps fld)
 reflexivity proved by (eq_ps_refl fld)
 symmetry proved by (eq_ps_sym (fld := fld))
 transitivity proved by (eq_ps_trans (fld := fld))
 as eq_ps_rel.

(*
Definition mk_nonzero (s : series α) v c := NonZero (mknz s v c).

Lemma fold_mk_nonzero : ∀ (s : series α) v c,
  NonZero (mknz s v c) = mk_nonzero s v c.
Proof. reflexivity. Qed.

Add Parametric Morphism : mk_nonzero
with signature eq_series fld ==> eq ==> eq ==> eq_ps fld as NonZero_morph.
Proof.
bbb.
*)

Section fld₂.

Variable α : Type.
Variable fld : field α.
Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).
Notation "a ≈ b" := (eq_ps fld a b) (at level 70).
Notation "a ≐ b" := (eq_norm_ps fld a b) (at level 70).

Definition valuation (ps : puiseux_series α) :=
  match ps with
  | NonZero nz => Some (nz_valnum nz # nz_comden nz)
  | Zero => None
  end.

Definition valuation_coeff (ps : puiseux_series α) :=
  match ps with
  | NonZero nz => series_nth_fld fld 0 (nz_terms nz)
  | Zero => zero fld
  end.

Theorem lt_first_nonzero : ∀ s n,
  (fin n < first_nonzero fld s)%Nbar → series_nth_fld fld n s ≍ zero fld.
Proof.
intros s n Hn.
remember (first_nonzero fld s) as v eqn:Hv .
symmetry in Hv.
apply first_nonzero_iff in Hv.
destruct v as [v| ]; [ idtac | apply Hv ].
destruct Hv as (Hvz, Hvnz).
apply Hvz, Nbar.fin_lt_mono; assumption.
Qed.

Theorem eq_first_nonzero : ∀ s n,
  first_nonzero fld s = fin n → ¬ (series_nth_fld fld n s ≍ zero fld).
Proof.
intros s n Hn.
apply first_nonzero_iff in Hn.
destruct Hn; assumption.
Qed.

Lemma series_pad_left_0 : ∀ s, series_pad_left fld 0 s ≃ s.
Proof.
intros s.
constructor; intros i.
unfold series_pad_left, series_nth_fld; simpl.
rewrite Nbar.add_0_r, Nat.sub_0_r; reflexivity.
Qed.

Lemma series_nth_pad_S : ∀ s n i,
  series_nth_fld fld i (series_pad_left fld n s) =
  series_nth_fld fld (S i) (series_pad_left fld (S n) s).
Proof.
intros s n i.
unfold series_nth_fld; simpl.
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

Lemma first_nonzero_pad_S : ∀ s n,
  first_nonzero fld (series_pad_left fld (S n) s) =
  NS (first_nonzero fld (series_pad_left fld n s)).
Proof.
intros s n.
remember (first_nonzero fld (series_pad_left fld n s)) as u eqn:Hu .
remember (first_nonzero fld (series_pad_left fld (S n) s)) as v eqn:Hv .
symmetry in Hu, Hv.
apply first_nonzero_iff in Hu.
apply first_nonzero_iff in Hv.
destruct u as [u| ].
 destruct Hu as (Hiu, Hu).
 destruct v as [v| ].
  destruct Hv as (Hiv, Hv).
  apply Nbar.fin_inj_wd.
  rewrite series_nth_pad_S in Hu.
  destruct (lt_dec (S u) v) as [Hlt₁| Hge₁].
   rewrite Hiv in Hu; [ negation Hu | assumption ].

   apply Nat.nlt_ge in Hge₁.
   destruct v.
    unfold series_nth_fld in Hv; simpl in Hv.
    exfalso.
    destruct (Nbar.lt_dec 0 (stop s + fin (S n))); apply Hv; reflexivity.

    destruct (lt_dec v u) as [Hlt₂| Hge₂].
     apply Hiu in Hlt₂.
     rewrite <- series_nth_pad_S in Hv; contradiction.

     apply Nat.nlt_ge in Hge₂.
     apply le_antisym; [ assumption | idtac ].
     apply Nat.succ_le_mono in Hge₂; assumption.

  rewrite series_nth_pad_S in Hu.
  exfalso; apply Hu, Hv.

 destruct v as [v| ]; [ idtac | reflexivity ].
 destruct Hv as (Hiv, Hv).
 destruct v.
  unfold series_nth_fld in Hv; simpl in Hv.
  exfalso.
  destruct (Nbar.lt_dec 0 (stop s + fin (S n))); apply Hv; reflexivity.

  rewrite <- series_nth_pad_S in Hv.
  exfalso; apply Hv, Hu.
Qed.

Theorem first_nonzero_pad : ∀ s n,
  first_nonzero fld (series_pad_left fld n s) =
    (fin n + first_nonzero fld s)%Nbar.
Proof.
intros s n.
induction n.
 rewrite series_pad_left_0, Nbar.add_0_l; reflexivity.

 rewrite first_nonzero_pad_S.
 rewrite IHn.
 simpl.
 destruct (first_nonzero fld s); reflexivity.
Qed.

Lemma padded_in_stretched : ∀ s k i,
  (0 < i mod Pos.to_nat k)%nat
  → series_nth_fld fld i (stretch_series fld k s) = zero fld.
Proof.
intros s k i Hi.
unfold series_nth_fld; simpl.
unfold series_nth_fld; simpl.
destruct (zerop (i mod Pos.to_nat k)) as [Hz| Hnz].
 exfalso; revert Hi; rewrite Hz; apply Nat.lt_irrefl.

 destruct (Nbar.lt_dec (fin i) (stop s * fin (Pos.to_nat k))); reflexivity.
Qed.

Lemma series_nth_fld_mul_stretch : ∀ s k i,
  series_nth_fld fld (Pos.to_nat k * i) (stretch_series fld k s) =
  series_nth_fld fld i s.
Proof.
intros s k i.
unfold series_nth_fld; simpl.
rewrite Nat.mul_comm.
rewrite Nat.mod_mul; [ simpl | apply Pos2Nat_ne_0 ].
rewrite Nat.div_mul; [ simpl | apply Pos2Nat_ne_0 ].
unfold series_nth_fld.
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

Lemma zero_series_stretched : ∀ s,
  (∀ i : nat, series_nth_fld fld i s ≍ zero fld)
  → ∀ n k, series_nth_fld fld n (stretch_series fld k s) ≍ zero fld.
Proof.
intros s H n k.
unfold series_nth_fld; simpl.
remember (stop s * fin (Pos.to_nat k))%Nbar as x.
destruct (Nbar.lt_dec (fin n) x) as [Hlt₁| ]; [ subst x | reflexivity ].
destruct (zerop (n mod Pos.to_nat k)) as [Hz| ]; [ idtac | reflexivity ].
rewrite Nat.mod_divides in Hz; [ idtac | apply Pos2Nat_ne_0 ].
destruct Hz as (c, Hn); subst n.
rewrite Nat.mul_comm.
rewrite Nat.div_mul; [ apply H | apply Pos2Nat_ne_0 ].
Qed.

Lemma zero_stretched_series : ∀ s k,
  (∀ i : nat, series_nth_fld fld i (stretch_series fld k s) ≍ zero fld)
  → ∀ n, series_nth_fld fld n s ≍ zero fld.
Proof.
intros s k H n.
pose proof (H (Pos.to_nat k * n)%nat) as Hn.
rewrite series_nth_fld_mul_stretch in Hn.
assumption.
Qed.

Theorem first_nonzero_stretch : ∀ k s,
  first_nonzero fld (stretch_series fld k s) =
    (fin (Pos.to_nat k) * first_nonzero fld s)%Nbar.
Proof.
intros k s.
remember (first_nonzero fld (stretch_series fld k s)) as n₁ eqn:Hn₁ .
remember (first_nonzero fld s) as n₂ eqn:Hn₂ .
symmetry in Hn₁, Hn₂.
apply first_nonzero_iff in Hn₁.
apply first_nonzero_iff in Hn₂.
destruct n₁ as [n₁| ].
 destruct Hn₁ as (Hiz₁, Hnz₁).
 destruct n₂ as [n₂| ].
  destruct Hn₂ as (Hiz₂, Hnz₂).
  simpl.
  apply Nbar.fin_inj_wd.
  destruct (lt_eq_lt_dec n₁ (Pos.to_nat k * n₂)) as [[Hlt| Hneq]| Hgt].
   exfalso; apply Hnz₁; clear Hnz₁.
   destruct (lt_dec 0 (n₁ mod Pos.to_nat k)) as [Hlt₁| Hge₁].
    rewrite padded_in_stretched; [ reflexivity | assumption ].

    apply Nat.nlt_ge in Hge₁.
    apply Nat.le_0_r in Hge₁.
    apply Nat.mod_divides in Hge₁; [ idtac | apply Pos2Nat_ne_0 ].
    destruct Hge₁ as (c, Hn).
    rewrite Hn.
    rewrite series_nth_fld_mul_stretch.
    apply Hiz₂; subst n₁.
    apply Nat.mul_lt_mono_pos_l in Hlt; [ assumption | apply Pos2Nat.is_pos ].

   assumption.

   exfalso; apply Hnz₂.
   erewrite <- series_nth_fld_mul_stretch.
   apply Hiz₁; assumption.

  exfalso; apply Hnz₁; clear Hnz₁.
  apply zero_series_stretched; assumption.

 destruct n₂ as [n₂| ]; [ idtac | reflexivity ].
 destruct Hn₂ as (Hiz₂, Hnz₂).
 exfalso; apply Hnz₂; clear Hnz₂.
 apply zero_stretched_series with (k := k).
 assumption.
Qed.

Lemma series_nth_add_pad : ∀ s i n,
  series_nth_fld fld (i + n) (series_pad_left fld n s) ≍
  series_nth_fld fld i s.
Proof.
intros s i n.
unfold series_nth_fld; simpl.
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

Lemma stretching_factor_pad : ∀ n s,
  stretching_factor fld (series_pad_left fld n s) = stretching_factor fld s.
Proof.
intros n s.
remember (stretching_factor fld s) as k₁ eqn:Hk₁ .
remember (stretching_factor fld (series_pad_left fld n s)) as k₂ eqn:Hk₂ .
symmetry in Hk₁, Hk₂.
apply stretching_factor_iff in Hk₁.
apply stretching_factor_iff in Hk₂.
rewrite first_nonzero_pad in Hk₂.
rewrite Nbar.add_comm in Hk₂.
remember (first_nonzero fld s) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; simpl in Hk₂; [ idtac | subst; reflexivity ].
destruct Hk₁ as [Hk₁| Hk₁].
 destruct Hk₂ as [Hk₂| Hk₂].
  unfold is_stretching_factor in Hk₁.
  unfold is_stretching_factor in Hk₂.
  destruct Hk₁ as (Hk₁, (Hik₁, Hlt₁)).
  destruct Hk₂ as (Hk₂, (Hik₂, Hlt₂)).
  destruct (lt_eq_lt_dec k₁ k₂) as [[H₁| H₁]| H₁].
   assert (1 < k₁ < k₂)%nat as H₂.
    split; assumption.

    apply Hlt₂ in H₂.
    destruct H₂ as (j, (Hjn, Hnj)).
    exfalso; apply Hnj.
    rewrite Nat.add_shuffle0.
    rewrite series_nth_add_pad.
    apply Hik₁; assumption.

   symmetry; assumption.

   assert (1 < k₂ < k₁)%nat as H₂.
    split; assumption.

    apply Hlt₁ in H₂.
    destruct H₂ as (j, (Hjn, Hnj)).
    exfalso; apply Hnj.
    erewrite <- series_nth_add_pad.
    rewrite Nat.add_shuffle0.
    apply Hik₂; assumption.

  destruct Hk₂ as (Hk₂, Hk').
  subst k₂.
  unfold is_stretching_factor in Hk₁.
  pose proof (Hk' k₁) as Hk'₁.
  exfalso; apply Hk'₁.
  unfold is_stretching_factor.
  destruct Hk₁ as (Hk₁, (Hik₁, Hlt₁)).
  split; [ assumption | idtac ].
  split.
   intros i Him.
   rewrite Nat.add_shuffle0.
   rewrite series_nth_add_pad.
   apply Hik₁; assumption.

   intros k₂ Hkk.
   apply Hlt₁ in Hkk.
   destruct Hkk as (i, (Hkk, Hss)).
   exists i.
   split; [ assumption | idtac ].
   rewrite Nat.add_shuffle0.
   rewrite series_nth_add_pad.
   assumption.

 destruct Hk₂ as [Hk₂| Hk₂].
  destruct Hk₁ as (Hk₁, Hk').
  subst k₁.
  unfold is_stretching_factor in Hk₂.
  pose proof (Hk' k₂) as Hk'₂.
  exfalso; apply Hk'₂.
  unfold is_stretching_factor.
  destruct Hk₂ as (Hk₂, (Hik₂, Hlt₂)).
  split; [ assumption | idtac ].
  split.
   intros i Him.
   rewrite <- series_nth_add_pad.
   rewrite Nat.add_shuffle0.
   apply Hik₂; assumption.

   intros k₁ Hkk.
   apply Hlt₂ in Hkk.
   destruct Hkk as (i, (Hkk, Hss)).
   exists i.
   split; [ assumption | idtac ].
   rewrite <- series_nth_add_pad.
   rewrite Nat.add_shuffle0.
   eassumption.

  destruct Hk₁, Hk₂; subst; reflexivity.
Qed.

Lemma stretching_factor_stretch : ∀ k s,
  stretching_factor fld (stretch_series fld k s) =
  (stretching_factor fld s * Pos.to_nat k)%nat.
Proof.
intros k s.
remember (stretching_factor fld s) as k₁ eqn:Hk₁ .
symmetry in Hk₁.
apply stretching_factor_iff in Hk₁.
apply stretching_factor_iff.
rewrite first_nonzero_stretch.
rewrite Nbar.mul_comm.
remember (first_nonzero fld s) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ simpl | subst; reflexivity ].
destruct Hk₁ as [Hk₁| Hk₁].
 left.
 unfold is_stretching_factor.
 unfold is_stretching_factor in Hk₁.
 destruct Hk₁ as (Hk₁, (Hik₁, Hlt₁)).
 split.
  destruct k₁ as [| k₁].
   apply Nat.lt_asymm in Hk₁.
   exfalso; apply Hk₁, Nat.lt_0_1.

   remember (Pos.to_nat k) as kn.
   symmetry in Heqkn.
   destruct kn.
    exfalso; revert Heqkn; apply Pos2Nat_ne_0.

    destruct k₁ as [| k₁].
     exfalso; revert Hk₁; apply Nat.lt_irrefl.

     simpl.
     rewrite Nat.add_comm; simpl.
     apply -> Nat.succ_lt_mono.
     apply Nat.lt_0_succ.

  split.
   intros i Him.
bbb.

destruct Hk₁ as (Hk₁, (Hik₁, Hlt₁)).
split.
 apply Nat.neq_mul_0; split; [ assumption | apply Pos2Nat_ne_0 ].

 split.
  intros i Him.
  destruct (zerop (i mod Pos.to_nat k)) as [H₁| H₁].
   apply Nat.mod_divides in H₁.
    destruct H₁ as (c, H₁).
    rewrite H₁.
    rewrite Nat.mul_comm, <- Nat.mul_add_distr_l.
    rewrite series_nth_fld_mul_stretch.
    apply Hik₁.
    intros H; apply Him; clear Him.
    apply Nat.mod_divides in H.
     destruct H as (d, H).
     subst i c.
     rewrite Nat.mul_assoc, Nat.mul_shuffle0.
     rewrite Nat.mul_comm, Nat.mul_assoc.
     rewrite Nat.mul_comm.
     apply Nat.mod_mul.
     apply Nat.neq_mul_0.
     split; [ assumption | apply Pos2Nat_ne_0 ].

     assumption.

    apply Pos2Nat_ne_0.

   rewrite padded_in_stretched; [ reflexivity | idtac ].
   rewrite Nat.add_comm.
   rewrite Nat.mod_add; [ assumption | idtac ].
   apply Pos2Nat_ne_0.

  intros k₂ Hlt.
  destruct (zerop (k₂ mod Pos.to_nat k)) as [H₁| H₁].
   apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
   destruct H₁ as (c, H₁).
   rewrite H₁ in Hlt.
   rewrite Nat.mul_comm in Hlt.
   destruct Hlt as (Hck, Hlt).
   apply Nat.mul_lt_mono_pos_r in Hlt; [ idtac | apply Pos2Nat.is_pos ].
   apply Nat.mul_pos_cancel_r in Hck; [ idtac | apply Pos2Nat.is_pos ].
   apply conj with (A := (0 < c)%nat) in Hlt; [ idtac | assumption ].
   apply Hlt₁ in Hlt.
   destruct Hlt as (i, (Him, Hin)).
   exists (i * Pos.to_nat k)%nat.
   split.
    intros H; apply Him; clear Him.
    rewrite H₁ in H.
    rewrite Nat.mul_comm in H.
    destruct c; [ reflexivity | idtac ].
    rewrite Nat.mul_mod_distr_l in H.
     apply Nat.eq_mul_0_r in H; [ assumption | apply Pos2Nat_ne_0 ].

     intros HH; discriminate HH.

     apply Pos2Nat_ne_0.

    rewrite <- Nat.mul_add_distr_r.
    rewrite Nat.mul_comm.
    rewrite series_nth_fld_mul_stretch.
    assumption.
bbb.
*)

(* ps_add *)

(*
Definition cm ps₁ ps₂ := Plcm (nz_comden ps₁) (nz_comden ps₂).
Definition cm_factor α (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (nz_comden ps₁) (nz_comden ps₂) in
  Pos.of_nat (Pos.to_nat l / Pos.to_nat (nz_comden ps₁))%nat.
*)
Definition cm (nz₁ nz₂ : nz_ps α) :=
  (nz_comden nz₁ * nz_comden nz₂)%positive.
Definition cm_factor α (nz₁ nz₂ : nz_ps α) :=
  nz_comden nz₂.
(**)

Definition adjust_nz n k nz :=
  {| nz_terms := series_pad_left fld n (stretch_series fld k (nz_terms nz));
     nz_valnum := nz_valnum nz * Zpos k - Z.of_nat n;
     nz_comden := nz_comden nz * k |}.

Theorem glop : ∀ nz n k, NonZero nz ≈ NonZero (adjust_nz n k nz).
Proof.
intros nz n k.
constructor.
unfold normalise_nz; simpl.
rewrite first_nonzero_pad.
rewrite first_nonzero_stretch.
rewrite Nbar.add_comm, Nbar.mul_comm.
remember (first_nonzero fld (nz_terms nz)) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; simpl; [ idtac | reflexivity ].
constructor; simpl.
 rewrite stretching_factor_pad.
 rewrite stretching_factor_stretch.
 simpl.
 rewrite Nat2Z.inj_add.
 rewrite Nat2Z.inj_mul.
 rewrite Nat2Z.inj_mul.
 rewrite positive_nat_Z.
bbb.
*)

Definition nz_terms_add nz₁ nz₂ :=
  let s₁ := stretch_series fld (cm_factor nz₁ nz₂) (nz_terms nz₁) in
  let s₂ := stretch_series fld (cm_factor nz₂ nz₁) (nz_terms nz₂) in
  let v₁ := (nz_valnum nz₁ * 'cm_factor nz₁ nz₂)%Z in
  let v₂ := (nz_valnum nz₂ * 'cm_factor nz₂ nz₁)%Z in
  series_add fld
    (series_pad_left fld (Z.to_nat (v₁ - v₂)) s₁)
    (series_pad_left fld (Z.to_nat (v₂ - v₁)) s₂).

Definition build_nz_add (nz₁ nz₂ : nz_ps α) :=
  let v₁ := (nz_valnum nz₁ * 'cm_factor nz₁ nz₂)%Z in
  let v₂ := (nz_valnum nz₂ * 'cm_factor nz₂ nz₁)%Z in
  {| nz_terms := nz_terms_add nz₁ nz₂;
     nz_valnum := Z.min v₁ v₂;
     nz_comden := cm nz₁ nz₂ |}.

Definition ps_add (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => NonZero (build_nz_add nz₁ nz₂)
      | Zero => ps₁
      end
  | Zero => ps₂
  end.

(* ps_mul *)

Fixpoint sum_mul_coeff i ni₁ s₁ s₂ :=
  match ni₁ with
  | O => None
  | S ni =>
      match sum_mul_coeff (S i) ni s₁ s₂ with
      | Some c =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (add fld (mul fld c₁ c₂) c)
              | None => Some c
              end
          | None => Some c
          end
      | None =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (mul fld c₁ c₂)
              | None => None
              end
          | None => None
          end
      end
  end.

Definition series_mul_term (s₁ s₂ : series α) :=
  {| terms i :=
       match sum_mul_coeff 0 (S i) s₁ s₂ with
       | Some c => c
       | None => zero fld
       end;
     stop := Nbar.max (stop s₁) (stop s₂) |}.

(*
Definition ps_mul (ps₁ ps₂ : puiseux_series α) :=
  match nz_valnum ps₁ with
  | zfin _ =>
      match nz_valnum ps₂ with
      | zfin _ =>
          let aps₁ := adjust (cm_factor ps₁ ps₂) ps₁ in
          let aps₂ := adjust (cm_factor ps₂ ps₁) ps₂ in
          {| nz_terms := series_mul_term (nz_terms aps₁) (nz_terms aps₂);
             nz_valnum := nz_valnum aps₁ + nz_valnum aps₂;
             nz_comden := nz_comden aps₁ |}
      | ∞ => ps_zero fld
      end
  | ∞ => ps_zero fld
  end.
*)

Lemma stretch_series_add_distr : ∀ k s₁ s₂,
  stretch_series fld k (series_add fld s₁ s₂) ≃
  series_add fld (stretch_series fld k s₁) (stretch_series fld k s₂).
Proof.
intros kp s₁ s₂.
unfold stretch_series; simpl.
unfold series_add; simpl.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
remember (Pos.to_nat kp) as k.
assert (k ≠ O) as Hk by (subst k; apply Pos2Nat_ne_0).
destruct (zerop (i mod k)) as [Hz| Hnz].
 apply Nat.mod_divides in Hz; [ idtac | assumption ].
 destruct Hz as (c, Hi).
 subst i.
 rewrite Nat.mul_comm.
 rewrite Nat.div_mul; [ idtac | assumption ].
 rewrite Nbar.mul_max_distr_r.
 remember (Nbar.max (stop s₁) (stop s₂) * fin k)%Nbar as m.
 remember (Nbar.lt_dec (fin (c * k)) m) as n; subst m.
 clear Heqn.
 destruct n as [Hlt| ]; [ idtac | reflexivity ].
 remember (Nbar.max (stop s₁) (stop s₂)) as m.
 remember (Nbar.lt_dec (fin c) m) as lt₁; subst m.
 remember (Nbar.lt_dec (fin c) (stop s₁)) as lt₂.
 remember (Nbar.lt_dec (fin c) (stop s₂)) as lt₃.
 remember (Nbar.lt_dec (fin (c * k)) (stop s₁ * fin k)) as lt₄.
 remember (Nbar.lt_dec (fin (c * k)) (stop s₂ * fin k)) as lt₅.
 clear Heqlt₁ Heqlt₂ Heqlt₃ Heqlt₄ Heqlt₅.
 destruct lt₁ as [Hlt₁| Hge₁].
  destruct lt₄ as [Hlt₄| Hge₄].
   destruct lt₅ as [Hlt₅| Hge₅]; [ reflexivity | idtac ].
   destruct lt₃ as [Hlt₃| ]; [ idtac | reflexivity ].
   exfalso; apply Hge₅; subst k.
   apply mul_lt_mono_positive_r; assumption.

   destruct lt₅ as [Hlt₅| Hge₅].
    destruct lt₂ as [Hlt₂| Hge₂]; [ idtac | reflexivity ].
    exfalso; apply Hge₄; subst k.
    apply mul_lt_mono_positive_r; assumption.

    destruct lt₂ as [Hlt₂| Hge₂].
     exfalso; apply Hge₄; subst k.
     apply mul_lt_mono_positive_r; assumption.

     destruct lt₃ as [Hlt₃| Hge₃]; [ idtac | reflexivity ].
     exfalso; apply Hge₅; subst k.
     apply mul_lt_mono_positive_r; assumption.

  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₁; clear Hge₁.
   apply Nbar.max_lt_iff; left; assumption.

   destruct lt₃ as [Hlt₃| Hge₃].
    exfalso; apply Hge₁; clear Hge₁.
    apply Nbar.max_lt_iff; right; assumption.

    destruct lt₄, lt₅; rewrite fld_add_0_l; reflexivity.

 remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂) * fin k)) as a.
 remember (Nbar.max (stop s₁ * fin k) (stop s₂ * fin k)) as n.
 remember (Nbar.lt_dec (fin i) n) as b.
 remember (Nbar.lt_dec (fin i) (stop s₁ * fin k)) as c.
 remember (Nbar.lt_dec (fin i) (stop s₂ * fin k)) as d.
 destruct a, b, c, d; try rewrite fld_add_0_l; reflexivity.
Qed.

Lemma stretch_pad_1_series_distr : ∀ kp s,
  stretch_series fld kp (series_pad_left fld 1 s) ≃
  series_pad_left fld (Pos.to_nat kp) (stretch_series fld kp s).
Proof.
intros kp s.
remember (Pos.to_nat kp) as x.
rewrite <- Nat.mul_1_l in Heqx; subst x.
apply stretch_pad_series_distr.
Qed.

(* *)

Lemma Pcm_factor_mul : ∀ x y,
  (x * Pos.of_nat (Pos.to_nat (Plcm x y) / Pos.to_nat x))%positive = Plcm x y.
Proof.
intros x y.
pose proof (Pos_divides_lcm_l x y) as H.
destruct H as (k, H).
rewrite H.
rewrite Pos2Nat.inj_mul.
rewrite Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
rewrite Pos2Nat.id.
apply Pos.mul_comm.
Qed.

Lemma nz_terms_add_comm : ∀ ps₁ ps₂,
  nz_terms_add ps₁ ps₂ ≃ nz_terms_add ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold nz_terms_add.
rewrite series_add_comm; reflexivity.
Qed.

Lemma nz_norm_add_comm : ∀ nz₁ nz₂,
  eq_norm_ps fld
    (normalise_nz fld (build_nz_add nz₁ nz₂))
    (normalise_nz fld (build_nz_add nz₂ nz₁)).
Proof.
intros nz₁ nz₂.
unfold normalise_nz; simpl.
rewrite nz_terms_add_comm.
remember (first_nonzero fld (nz_terms_add nz₂ nz₁)) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; simpl.
 rewrite Z.min_comm.
 rewrite nz_terms_add_comm; reflexivity.

 unfold cm.
 rewrite Pos.mul_comm.
 rewrite nz_terms_add_comm; reflexivity.

 rewrite nz_terms_add_comm; reflexivity.
Qed.

Theorem ps_add_comm : ∀ ps₁ ps₂, ps_add ps₁ ps₂ ≈ ps_add ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_add; simpl.
destruct ps₁ as [nz₁| ]; [ idtac | destruct ps₂; reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
constructor; apply nz_norm_add_comm.
Qed.

Lemma series_pad_add_distr : ∀ s₁ s₂ n,
  series_pad_left fld n (series_add fld s₁ s₂)
  ≃ series_add fld (series_pad_left fld n s₁) (series_pad_left fld n s₂).
Proof.
intros s₁ s₂ n.
constructor.
intros i.
unfold series_add, series_nth_fld; simpl.
rewrite Nbar.add_max_distr_r.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂) + fin n)) as c₁.
remember (Nbar.lt_dec (fin i) (stop s₁ + fin n)) as c₂.
remember (Nbar.lt_dec (fin i) (stop s₂ + fin n)) as c₃.
remember (Nbar.lt_dec (fin (i - n)) (stop s₁)) as c₄.
remember (Nbar.lt_dec (fin (i - n)) (stop s₂)) as c₅.
clear Heqc₁ Heqc₂ Heqc₃ Heqc₄ Heqc₅.
destruct (lt_dec i n) as [Hlt| Hge].
 destruct c₁, c₂, c₃; try rewrite fld_add_0_l; reflexivity.

 apply not_gt in Hge.
 remember (i - n)%nat as m.
 assert (m + n = i)%nat by (subst m; apply Nat.sub_add; assumption).
 subst i; clear Heqm Hge.
 destruct c₁ as [H₁| ]; [ idtac | reflexivity ].
 destruct c₂ as [H₂| H₂].
  destruct c₄ as [H₄| H₄].
   destruct c₃ as [H₃| H₃].
    destruct c₅ as [H₅| H₅]; [ reflexivity | idtac ].
    rewrite Nbar.fin_inj_add in H₃.
    apply Nbar.add_lt_mono_r in H₃; [ idtac | intros H; discriminate H ].
    contradiction.

    destruct c₅ as [c₅| c₅]; [ idtac | reflexivity ].
    rewrite Nbar.fin_inj_add in H₃.
    exfalso; apply H₃.
    apply Nbar.add_lt_mono_r; [ intros H; discriminate H | idtac ].
    assumption.

   rewrite Nbar.fin_inj_add in H₂.
   apply Nbar.add_lt_mono_r in H₂; [ idtac | intros H; discriminate H ].
   contradiction.

  destruct c₄ as [H₄| H₄].
   exfalso; apply H₂.
   rewrite Nbar.fin_inj_add.
   apply Nbar.add_lt_mono_r; [ intros H; discriminate H | idtac ].
   assumption.

   destruct c₃ as [H₃| H₃].
    destruct c₅ as [H₅| H₅]; [ reflexivity | idtac ].
    rewrite Nbar.fin_inj_add in H₃.
    apply Nbar.add_lt_mono_r in H₃; [ idtac | intros H; discriminate H ].
    contradiction.

    destruct c₅ as [c₅| c₅]; [ idtac | reflexivity ].
    exfalso; apply H₃.
    rewrite Nbar.fin_inj_add.
    apply Nbar.add_lt_mono_r; [ intros H; discriminate H | idtac ].
    assumption.
Qed.

Lemma first_nonzero_nonzero_fin : ∀ s n,
  first_nonzero fld s = fin (S n)
  → series_nth_fld fld 0 s ≍ zero fld.
Proof.
intros s n Hn.
apply lt_first_nonzero.
rewrite Hn.
constructor; apply lt_0_Sn.
Qed.

Definition Qmin x y :=
  match x ?= y with
  | Eq => x
  | Lt => x
  | Gt => y
  end.

Definition Qmin₃ x y z := Qmin (Qmin x y) z.

Lemma nz_terms_add_assoc : ∀ nz₁ nz₂ nz₃,
  nz_terms_add (build_nz_add nz₁ nz₂) nz₃ ≃
  nz_terms_add nz₁ (build_nz_add nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃.
constructor; intros i.
unfold build_nz_add; simpl.
unfold cm_factor, cm.
unfold nz_terms_add; simpl.
unfold cm_factor, cm.
remember (nz_valnum nz₁) as v₁ eqn:Hv₁ .
remember (nz_valnum nz₂) as v₂ eqn:Hv₂ .
remember (nz_valnum nz₃) as v₃ eqn:Hv₃ .
remember (nz_comden nz₁) as c₁.
remember (nz_comden nz₂) as c₂.
remember (nz_comden nz₃) as c₃.
do 2 rewrite stretch_series_add_distr.
do 2 rewrite series_pad_add_distr.
rewrite series_add_assoc.
do 4 rewrite stretch_pad_series_distr.
do 4 rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
do 4 rewrite series_pad_pad.
do 4 rewrite <- Z2Nat_inj_mul_pos_r.
do 4 rewrite Z.mul_sub_distr_r.
do 2 rewrite Pos2Z.inj_mul, Z.mul_assoc.
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
remember (v₁ * ' c₂ * ' c₃)%Z as vcc eqn:Hvcc .
remember (v₂ * ' c₁ * ' c₃)%Z as cvc eqn:Hcvc .
remember (v₃ * ' c₂ * ' c₁)%Z as ccv eqn:Hccv .
rewrite Z.mul_shuffle0, <- Hccv.
rewrite Z.mul_shuffle0, <- Hcvc.
do 2 rewrite Z2Nat_sub_min2.
do 2 rewrite Z2Nat_sub_min1.
rewrite Pos.mul_comm.
replace (c₃ * c₁)%positive with (c₁ * c₃)%positive by apply Pos.mul_comm.
reflexivity.
Qed.

Definition terms_add ps₁ ps₂ :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => nz_terms_add nz₁ nz₂
      | Zero => nz_terms nz₁
      end
  | Zero =>
      match ps₂ with
      | NonZero nz₂ => nz_terms nz₂
      | Zero => series_0 fld
      end
  end.

Lemma nz_norm_add_assoc : ∀ nz₁ nz₂ nz₃,
  eq_norm_ps fld
    (normalise_nz fld (build_nz_add (build_nz_add nz₁ nz₂) nz₃))
    (normalise_nz fld (build_nz_add nz₁ (build_nz_add nz₂ nz₃))).
Proof.
intros nz₁ nz₂ nz₃.
unfold normalise_nz; simpl.
rewrite nz_terms_add_assoc.
remember (first_nonzero fld (nz_terms_add nz₁ (build_nz_add nz₂ nz₃))) as n
 eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; constructor; simpl.
 unfold cm_factor, cm; simpl.
 f_equal.
 do 2 rewrite Pos2Z.inj_mul.
 do 2 rewrite Z.mul_assoc.
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Z.min_assoc.
 f_equal.
  f_equal.
   f_equal; apply Z.mul_shuffle0.

   apply Z.mul_shuffle0.

  rewrite nz_terms_add_assoc; reflexivity.

 unfold cm; simpl.
 unfold cm; simpl.
 rewrite Pos.mul_assoc.
 rewrite nz_terms_add_assoc; reflexivity.

 rewrite nz_terms_add_assoc; reflexivity.
Qed.

(*
Lemma nz_add_assoc_base : ∀ nz₁ nz₂ nz₃,
  nz_add (build_nz_add nz₁ nz₂) nz₃ ≈
  nz_add nz₁ (build_nz_add nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃.
unfold nz_add.
rewrite nz_terms_add_assoc.
remember (nz_terms_add nz₁ (build_nz_add nz₂ nz₃)) as nz.
remember (first_nonzero fld nz) as n eqn:Hn ; subst nz.
destruct n as [n| ]; [ constructor | reflexivity ].
apply nz_norm_add_assoc.
Qed.
*)

Delimit Scope ps_scope with ps.
Bind Scope ps_scope with puiseux_series.
Notation "a + b" := (ps_add a b) : ps_scope.
Notation "a ∔ b" := (build_nz_add a b) (at level 70).

Lemma ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  ps_add (ps_add ps₁ ps₂) ps₃ ≈ ps_add ps₁ (ps_add ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃.
destruct ps₁ as [nz₁| ]; [ idtac | reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
destruct ps₃ as [nz₃| ]; [ idtac | rewrite ps_add_comm; reflexivity ].
remember (ps_add (NonZero nz₁) (NonZero nz₂)) as x.
remember (ps_add (NonZero nz₂) (NonZero nz₃)) as y.
simpl in Heqx, Heqy; subst x y.
simpl; constructor.
apply nz_norm_add_assoc.
Qed.

Lemma Z2Nat_sub_mul_succ_l : ∀ a b,
  (Z.to_nat (a * ' b) - Z.to_nat ((a + 1) * ' b))%nat = O.
Proof.
intros a b.
destruct a as [| a| a]; [ reflexivity | simpl | reflexivity ].
do 2 rewrite Pos2Nat.inj_mul.
rewrite <- Nat.mul_sub_distr_r.
rewrite Pos2Nat.inj_add.
rewrite Nat.sub_add_distr, Nat.sub_diag; reflexivity.
Qed.

Lemma stop_head_tail : ∀ nz,
  stop (nz_terms nz) ≠ fin 0
  → stop (nz_terms_add (nz_head nz) (nz_tail nz)) =
    stop (stretch_series fld (nz_comden nz) (nz_terms nz)).
Proof.
intros nz Hst.
unfold nz_terms_add; simpl.
unfold nz_head, nz_tail.
remember (stop (nz_terms nz)) as st.
destruct st as [st| ]; [ simpl | simpl; rewrite <- Heqst; reflexivity ].
destruct st as [| st]; [ negation Hst | simpl ].
rewrite Nat.add_0_r.
rewrite <- Heqst; simpl.
rewrite Nat.sub_0_r.
rewrite Z.mul_add_distr_r, Z.mul_1_l.
rewrite Z.sub_add_distr, Z.sub_diag; simpl.
rewrite Nat.add_0_r.
rewrite Z.add_simpl_l.
rewrite Nat.max_r; [ rewrite Nat.add_comm; reflexivity | idtac ].
apply Nat.le_sub_le_add_r; rewrite Nat.sub_diag; apply Nat.le_0_l.
Qed.

Lemma stop_0_series_nth_0 : ∀ s i,
  stop s = 0%Nbar
  → series_nth_fld fld i s = zero fld.
Proof.
intros s i Hs.
unfold series_nth_fld; simpl.
rewrite Hs; simpl.
destruct (Nbar.lt_dec (fin i) 0) as [Hlt₁| Hge₁]; [ idtac | reflexivity ].
apply Nbar.nlt_ge in Hlt₁.
 exfalso; apply Hlt₁; constructor; apply lt_0_Sn.

 constructor; apply Nat.le_0_l.
Qed.

Lemma stop_0_series_nth_stretch_0 : ∀ s n i,
  stop s = 0%Nbar
  → series_nth_fld fld i (stretch_series fld n s) = zero fld.
Proof.
intros s n i Hs.
unfold series_nth_fld; simpl.
rewrite Hs; simpl.
destruct (Nbar.lt_dec (fin i) 0) as [Hlt₁| Hge₁]; [ idtac | reflexivity ].
apply Nbar.nlt_ge in Hlt₁.
 exfalso; apply Hlt₁; constructor; apply lt_0_Sn.

 constructor; apply Nat.le_0_l.
Qed.

Lemma stop_0_series_nth_pad_stretch_0 : ∀ s i n k,
  stop s = 0%Nbar
  → series_nth_fld fld i (series_pad_left fld n (stretch_series fld k s))
    = zero fld.
Proof.
intros s i n k Hs.
unfold series_nth_fld; simpl.
rewrite Hs; simpl.
destruct (Nbar.lt_dec (fin i) (fin n)) as [H₁| H₁]; [ idtac | reflexivity ].
destruct (lt_dec i n) as [H₂| H₂]; [ reflexivity | idtac ].
exfalso; apply H₂.
apply Nbar.fin_lt_mono; assumption.
Qed.

(* à voir...
Lemma ps_cons : ∀ nz,
  series_nth_fld fld 0 (nz_terms_add (nz_head nz) (nz_tail nz)) ≭ zero fld
  → nz_add (nz_head nz) (nz_tail nz) ≈ NonZero nz.
Proof.
intros nz Hzz.
remember (nz_terms_add (nz_head nz) (nz_tail nz)) as s.
remember (first_nonzero fld s) as n eqn:Hn ; subst s.
symmetry in Hn.
destruct n as [[| n]| ].
 destruct (Nbar.eq_dec (stop (nz_terms nz)) (fin 0)) as [Hst| Hst].
  unfold nz_add.
  rewrite Hn.
  constructor 1 with (k₁ := xH) (k₂ := nz_comden nz); simpl.
   rewrite stretch_series_1.
   constructor; intros i.
   rewrite stop_0_series_nth_stretch_0; [ idtac | assumption ].
   unfold series_nth_fld; simpl.
   unfold nz_head, nz_tail; simpl.
   rewrite Hst; simpl.
   rewrite Hst; simpl.
   rewrite Z.sub_diag; simpl.
   destruct (Nbar.lt_dec (fin i) 0) as [H₁| H₁]; [ idtac | reflexivity ].
   apply Nbar.nle_gt in H₁.
   exfalso; apply H₁, Nbar.le_0_l.

   unfold nz_head, nz_tail; simpl.
   rewrite Hst.
   rewrite Z.mul_1_r.
   rewrite Z.min_id; reflexivity.

   unfold nz_head, nz_tail; simpl.
   rewrite Hst.
   rewrite Pos.mul_1_r; reflexivity.

  unfold nz_add.
  rewrite Hn.
  constructor 1 with (k₁ := xH) (k₂ := nz_comden nz); simpl.
   rewrite stretch_series_1.
   constructor; intros i.
   remember (nz_terms_add fld (nz_head nz) (nz_tail nz)) as s₁ eqn:Hs₁ .
   remember (stretch_series fld (nz_comden nz) (nz_terms nz)) as s₂ eqn:Hs₂ .
   unfold series_nth_fld; simpl.
   destruct (Nbar.lt_dec (fin i) (stop s₁)) as [H₁| H₁].
    destruct (Nbar.lt_dec (fin i) (stop s₂)) as [H₂| H₂].
     subst s₁ s₂; simpl.
     unfold nz_head, nz_tail; simpl.
     remember (stop (nz_terms nz)) as st.
     symmetry in Heqst.
     destruct st as [st| ]; simpl in H₁, H₂ |- *.
      destruct st as [| st]; [ negation Hst | simpl in H₁ |- * ].
      rewrite Z.mul_add_distr_r, Z.mul_1_l.
      rewrite Z.sub_add_distr, Z.sub_diag.
      rewrite Z.add_simpl_l; simpl.
      rewrite series_pad_left_0.
      destruct (zerop (i mod Pos.to_nat (nz_comden nz))) as [Hz| Hnz].
       apply Nat.mod_divides in Hz; [ idtac | apply Pos2Nat_ne_0 ].
       destruct Hz as (k, Hi); subst i.
       rewrite Nat.mul_comm, Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
       unfold series_head, series_tail; simpl.
       rewrite Heqst; simpl.
       rewrite Nat.sub_0_r.
       remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
       unfold series_nth_fld; simpl.
       rewrite Nat.add_0_r.
       rewrite <- Hc.
       rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
       rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
       rewrite Nat.mul_comm, <- Nat.mul_pred_r.
       destruct (Nbar.lt_dec (fin (c * k)) (fin c)) as [H₃| H₃].
        remember (c * k)%nat as x.
        rewrite Nat.mul_comm, <- Nat.mul_succ_r; subst x.
        destruct (Nbar.lt_dec (fin (c * k)) (fin (c * S st))) as [H₄| H₄].
         destruct (lt_dec (c * k) c) as [H₅| H₅].
          unfold series_nth_fld; simpl.
          rewrite Heqst.
          rewrite fld_add_comm, fld_add_0_l.
          destruct (Nbar.lt_dec (fin k) 1) as [H₆| H₆].
           destruct (Nbar.lt_dec (fin k) (fin (S st))) as [| H₇].
            reflexivity.

            exfalso; apply H₇; clear H₇.
            rewrite Heqst, Nbar.fin_inj_mul in H₂.
            apply <- Nbar.mul_lt_mono_pos_r.
             rewrite Nbar.mul_comm; eassumption.

             intros H; discriminate H.

             intros H; discriminate H.

             destruct k; [ rewrite Nat.mul_0_r in H₃; assumption | idtac ].
             apply Nbar.nle_gt in H₆.
             exfalso; apply H₆.
             constructor; apply le_n_S, le_0_n.

           apply Nbar.nlt_ge in H₆.
           destruct k.
            apply Nbar.nlt_ge in H₆.
            exfalso; apply H₆; constructor; apply Nat.lt_0_1.

            apply Nbar.nlt_ge in H₃.
             exfalso; apply H₃.

             constructor.
             rewrite Nat.mul_comm; simpl.
             apply le_plus_l.

          destruct k.
           exfalso; apply H₅; rewrite Nat.mul_0_r; subst c.
           apply Pos2Nat.is_pos.

           unfold series_nth_fld; simpl.
           rewrite Nat.mul_comm.
           rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
           rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
           destruct (Nbar.lt_dec (fin (S k)) 1) as [H₆| H₆].
            apply Nbar.nlt_ge in H₆.
             exfalso; apply H₆.

             constructor; apply le_n_S, le_0_n.

            rewrite fld_add_0_l.
            rewrite Heqst.
            destruct (Nbar.lt_dec (fin k) (fin st)) as [H₇| H₇].
             destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [H₈| H₈].
              reflexivity.

              exfalso; apply H₈.
              constructor; apply lt_n_S.
              inversion H₇; assumption.

             destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [H₈| H₈].
              exfalso; apply H₇.
              constructor; apply lt_S_n.
              inversion H₈; assumption.

              reflexivity.

         rewrite Heqst in H₂.
         replace (c * S st)%nat with (S st * c)%nat in H₄ .
          contradiction.

          apply Nat.mul_comm.

        rewrite fld_add_0_l.
        rewrite <- Nat.mul_succ_l.
        destruct (Nbar.lt_dec (fin (c * k)) (fin (S st * c))) as [H₄| H₄].
         destruct (lt_dec (c * k) c) as [H₅| H₅].
          exfalso; apply H₃.
          constructor; assumption.

          rewrite Nat.mul_comm.
          rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
          rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
          unfold series_nth_fld; simpl.
          rewrite Heqst.
          destruct k.
           rewrite Nat.mul_0_r in H₅.
           exfalso; apply H₅; subst c; apply Pos2Nat.is_pos.

           simpl.
           destruct (Nbar.lt_dec (fin k) (fin st)) as [H₆| H₆].
            destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [H₇| H₇].
             reflexivity.

             exfalso; apply H₇; constructor; apply lt_n_S.
             inversion H₆; assumption.

            destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [H₇| H₇].
             exfalso; apply H₆; constructor; apply lt_S_n.
             inversion H₇; assumption.

             reflexivity.

         rewrite Heqst in H₂.
         contradiction.

       rewrite <- stretch_pad_1_series_distr.
       rewrite padded_in_stretched; [ rewrite fld_add_0_l | assumption ].
       rewrite padded_in_stretched; [ reflexivity | assumption ].

      rewrite Z.mul_add_distr_r, Z.mul_1_l.
      rewrite Z.sub_add_distr, Z.sub_diag.
      rewrite Z.add_simpl_l; simpl.
      rewrite series_pad_left_0.
      destruct (zerop (i mod Pos.to_nat (nz_comden nz))) as [Hz| Hnz].
       apply Nat.mod_divides in Hz; [ idtac | apply Pos2Nat_ne_0 ].
       destruct Hz as (k, Hi).
       subst i.
       rewrite Nat.mul_comm, Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
       unfold series_head, series_tail; simpl.
       rewrite Heqst; simpl.
       remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
       unfold series_nth_fld; simpl.
       rewrite Nat.add_0_r.
       rewrite <- Hc.
       rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
       rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
       rewrite Nat.mul_comm, <- Nat.mul_pred_r.
       destruct (Nbar.lt_dec (fin (c * k)) (fin c)) as [H₃| H₃].
        remember (c * k)%nat as x.
        rewrite Heqst.
        destruct (Nbar.lt_dec (fin x) inf) as [H₄| H₄].
         subst x.
         destruct (lt_dec (c * k) c) as [H₅| H₅].
          rewrite fld_add_comm, fld_add_0_l.
          destruct (Nbar.lt_dec (fin k) inf) as [H₆| H₆].
           unfold series_nth_fld; simpl.
           destruct (Nbar.lt_dec (fin k) 1) as [H₇| H₇].
            reflexivity.

            exfalso; apply H₇.
            destruct k; [ apply Nbar.lt_0_1 | idtac ].
            apply Nat.nle_gt in H₅.
            exfalso; apply H₅.
            rewrite Nat.mul_comm; simpl.
            apply Nat.le_add_r.

           exfalso; apply H₆; constructor.

          rewrite Nat.mul_comm.
          rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
          rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
          destruct (Nbar.lt_dec (fin k) ∞) as [H₆| H₆].
           destruct k.
            exfalso; apply H₅; rewrite Nat.mul_0_r.
            subst c; apply Pos2Nat.is_pos.

            apply Nbar.nle_gt in H₃.
            exfalso; apply H₃.
            constructor.
            rewrite Nat.mul_comm; simpl.
            apply Nat.le_add_r.

           exfalso; apply H₆.
           constructor.

         exfalso; apply H₄; constructor.

        rewrite fld_add_0_l.
        destruct k.
         exfalso; apply H₃; rewrite Nat.mul_0_r.
         constructor.
         subst c; apply Pos2Nat.is_pos.

         destruct (Nbar.lt_dec (fin (c * S k)) ∞) as [H₄| H₄].
          destruct (lt_dec (c * S k) c) as [H₅| H₅].
           apply Nat.nle_gt in H₅.
           exfalso; apply H₅.
           rewrite Nat.mul_comm; simpl.
           apply Nat.le_add_r.

           rewrite Nat.mul_comm.
           rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
           rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
           rewrite Heqst.
           destruct (Nbar.lt_dec (fin (S k)) ∞) as [H₆| H₆].
            unfold series_nth_fld; simpl.
            destruct (Nbar.lt_dec (fin k) ∞) as [H₇| H₇].
             reflexivity.

             exfalso; apply H₇; constructor.

            exfalso; apply H₆; constructor.

          exfalso; apply H₄; constructor.

       unfold series_head, series_tail; simpl.
       unfold series_nth_fld; simpl.
       unfold series_nth_fld; simpl.
       rewrite Heqst; simpl.
       rewrite Nat.add_0_r.
       remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
       destruct (Nbar.lt_dec (fin i) (fin c)) as [H₃| H₃].
        destruct (zerop (i mod c)) as [Hz| Hnz₂].
         rewrite Hz in Hnz.
         exfalso; revert Hnz; apply Nat.lt_irrefl.

         rewrite fld_add_0_l.
         destruct (Nbar.lt_dec (fin i) ∞) as [H₄| H₄].
          destruct (lt_dec i c) as [H₅| H₅].
           reflexivity.

           apply Nbar.fin_lt_mono in H₃.
           contradiction.

          reflexivity.

        rewrite fld_add_0_l.
        destruct (Nbar.lt_dec (fin i) ∞) as [H₄| H₄].
         destruct (lt_dec i c) as [H₅| H₅].
          reflexivity.

          destruct (zerop ((i - c) mod c)) as [H₆| H₆].
           apply Nat.mod_divides in H₆.
            destruct H₆ as (k, Hic).
            rewrite Hic.
            rewrite Nat.mul_comm.
            rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
            apply Nat.nlt_ge in H₅.
            destruct k.
             rewrite Nat.mul_0_r in Hic.
             apply Nat.sub_0_le in Hic.
             apply Nat.le_antisymm in Hic; [ idtac | assumption ].
             rewrite Hic in Hnz.
             destruct i.
              simpl in Hnz.
              exfalso; revert Hnz; apply Nat.lt_irrefl.

              rewrite Nat.mod_same in Hnz.
               exfalso; revert Hnz; apply Nat.lt_irrefl.

               intros H; discriminate H.

             apply Nat.add_sub_eq_nz in Hic.
              rewrite Nat.add_comm in Hic.
              rewrite <- Nat.mul_succ_r in Hic.
              rewrite <- Hic in Hnz.
              rewrite Nat.mul_comm in Hnz.
              rewrite Nat.mod_mul in Hnz.
               exfalso; revert Hnz; apply Nat.lt_irrefl.

               subst c; apply Pos2Nat_ne_0.

              apply Nat.neq_mul_0.
              split; [ idtac | intros H; discriminate H ].
              subst c; apply Pos2Nat_ne_0.

            subst c; apply Pos2Nat_ne_0.

           reflexivity.

         reflexivity.

     clear Hn.
     rewrite Hs₂ in H₂.
     simpl in H₂.
     apply Nbar.nlt_ge in H₂.
     rewrite Hs₁ in H₁.
     simpl in H₁.
     unfold nz_head, nz_tail in H₁.
     remember (stop (nz_terms nz)) as st.
     symmetry in Heqst.
     destruct st as [st| ].
      destruct st as [| st]; [ exfalso; apply Hst; reflexivity | idtac ].
      simpl in H₁.
      rewrite Heqst in H₁.
      simpl in H₁.
      rewrite Nat.add_0_r in H₁.
      rewrite Nat.sub_0_r in H₁.
      rewrite Z.mul_add_distr_r, Z.mul_1_l in H₁.
      rewrite Z.sub_add_distr, Z.sub_diag in H₁.
      rewrite Z.add_simpl_l in H₁; simpl in H₁.
      rewrite Nat.add_0_r in H₁.
      rewrite Nat.max_r in H₁.
       rewrite <- Nat.mul_succ_l in H₁.
       rewrite Nbar.fin_inj_mul in H₁.
       apply Nbar.nlt_ge in H₂.
       contradiction.

       rewrite Nat.add_comm; apply Nat.le_add_r.

      apply Nbar.nlt_ge in H₂.
      exfalso; apply H₂; constructor.

    destruct (Nbar.lt_dec (fin i) (stop s₂)) as [H₂| H₂].
     subst s₁ s₂.
     simpl in H₁, H₂.
     unfold nz_head, nz_tail in H₁; simpl in H₁.
     remember (stop (nz_terms nz)) as st.
     symmetry in Heqst.
     destruct st as [st| ].
      destruct st as [| st]; [ exfalso; apply Hst; reflexivity | idtac ].
      simpl in H₁.
      rewrite Heqst in H₁; simpl in H₁.
      rewrite Nat.add_0_r, Nat.sub_0_r in H₁.
      rewrite Z.mul_add_distr_r, Z.mul_1_l in H₁.
      rewrite Z.sub_add_distr, Z.sub_diag in H₁.
      rewrite Z.add_simpl_l in H₁; simpl in H₁.
      rewrite Nat.add_0_r in H₁.
      rewrite Nat.max_r in H₁.
       rewrite <- Nat.mul_succ_l in H₁.
       rewrite Nbar.fin_inj_mul in H₁.
       contradiction.

       rewrite Nat.add_comm; apply Nat.le_add_r.

      simpl in H₁.
      rewrite Heqst in H₁; simpl in H₁.
      exfalso; apply H₁; constructor.

     reflexivity.

   rewrite Z.mul_1_r.
   unfold nz_head, nz_tail; simpl.
   remember (stop (nz_terms nz)) as st.
   symmetry in Heqst.
   destruct st as [st| ]; simpl.
    destruct st as [| st]; [ exfalso; apply Hst; reflexivity | simpl ].
    rewrite Z.min_l; [ reflexivity | idtac ].
    rewrite Z.add_1_r.
    rewrite Z.mul_succ_l.
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    apply Pos2Z.is_nonneg.

    rewrite Z.min_l; [ reflexivity | idtac ].
    rewrite Z.add_1_r.
    rewrite Z.mul_succ_l.
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    apply Pos2Z.is_nonneg.

   rewrite Pos.mul_1_r.
   unfold nz_head, nz_tail; simpl.
   remember (stop (nz_terms nz)) as st.
   symmetry in Heqst.
   destruct st as [st| ].
    destruct st as [| st]; [ exfalso; apply Hst; reflexivity | idtac ].
    reflexivity.

    reflexivity.

 apply first_nonzero_iff in Hn.
 destruct Hn as (Hn, _).
 rewrite Hn in Hzz; [ idtac | apply Nat.lt_0_succ ].
 negation Hzz.

 apply first_nonzero_iff in Hn.
 rewrite Hn in Hzz.
 negation Hzz.
Qed.
*)

Lemma stop_head_tail₂ : ∀ nz,
  stop (nz_terms nz) ≠ 0%Nbar
  → stop (nz_terms_add (nz_head nz) (nz_tail nz))
    = (fin (Pos.to_nat (nz_comden nz)) * stop (nz_terms nz))%Nbar.
Proof.
intros nz Hst.
unfold nz_terms_add; simpl.
unfold nz_head, nz_tail.
remember (stop (nz_terms nz)) as st.
destruct st as [st| ]; [ simpl | simpl; rewrite <- Heqst; reflexivity ].
destruct st as [| st]; [ negation Hst | simpl ].
rewrite <- Heqst; simpl.
rewrite Nat.add_0_r.
rewrite Nat.sub_0_r.
rewrite Z.mul_add_distr_r, Z.mul_1_l.
rewrite Z.sub_add_distr, Z.sub_diag; simpl.
rewrite Z.add_simpl_l; simpl.
rewrite Nat.add_0_r.
rewrite max_r.
 rewrite <- Nat.mul_succ_l, Nat.mul_comm; reflexivity.

 rewrite Nat.add_comm.
 apply Nat.le_add_r.
Qed.

Lemma stop_nz_add_pos_pos : ∀ nz,
  (0 < stop (nz_terms_add (nz_head nz) (nz_tail nz)))%Nbar
  → (0 < stop (nz_terms nz))%Nbar.
Proof.
intros nz H.
unfold nz_terms_add in H; simpl in H.
unfold nz_head, nz_tail in H; simpl in H.
remember (stop (nz_terms nz)) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ]; [ idtac | constructor ].
destruct st as [| st]; [ idtac | constructor; apply Nat.lt_0_succ ].
rewrite Hst in H; simpl in H.
rewrite Z.sub_diag in H; assumption.
Qed.

Lemma stop_nz_pos_add_pos : ∀ nz,
  (0 < stop (nz_terms nz))%Nbar
  → (0 < stop (nz_terms_add (nz_head nz) (nz_tail nz)))%Nbar.
Proof.
intros nz H.
unfold nz_terms_add; simpl.
unfold nz_head, nz_tail; simpl.
remember (stop (nz_terms nz)) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ]; [ simpl | simpl; rewrite Hst; constructor ].
destruct st as [| st]; simpl.
 exfalso; revert H; apply Nbar.lt_irrefl.

 rewrite Hst; simpl.
 rewrite Nat.add_0_r, Nat.sub_0_r.
 rewrite Z.mul_add_distr_r, Z.mul_1_l.
 rewrite Z.sub_add_distr, Z.sub_diag.
 rewrite Z.add_simpl_l; simpl.
 rewrite Nat.add_0_r.
 rewrite Nat.max_r.
  rewrite <- Nat.mul_succ_l.
  rewrite Nbar.fin_inj_mul.
  constructor.
  apply Nat.mul_pos_pos; [ apply Nat.lt_0_succ | apply Pos2Nat.is_pos ].

  rewrite Nat.add_comm; apply Nat.le_add_r.
Qed.

Lemma series_nth_add_head_tail : ∀ nz,
  series_nth_fld fld 0 (nz_terms nz)
  ≍ series_nth_fld fld 0 (nz_terms_add (nz_head nz) (nz_tail nz)).
Proof.
intros nz.
unfold series_nth_fld.
remember (nz_terms_add (nz_head nz) (nz_tail nz)) as s eqn:Hs .
destruct (Nbar.lt_dec 0 (stop (nz_terms nz))) as [H₁| H₁].
 destruct (Nbar.lt_dec 0 (stop s)) as [H₂| H₂].
  subst s; simpl.
  unfold nz_head, nz_tail; simpl.
  remember (stop (nz_terms nz)) as st.
  symmetry in Heqst.
  destruct st as [st| ]; simpl.
   destruct st as [st| ]; simpl.
    exfalso; revert H₁; apply Nbar.lt_irrefl.

    rewrite Z.mul_add_distr_r, Z.mul_1_l.
    rewrite Z.sub_add_distr, Z.sub_diag; simpl.
    rewrite Z.add_simpl_l; simpl.
    rewrite series_pad_left_0.
    unfold series_head, series_tail; simpl.
    rewrite Heqst; simpl.
    rewrite Nat.sub_0_r.
    unfold series_nth_fld; simpl.
    rewrite Nat.add_0_r.
    rewrite Nat.mod_0_l; [ simpl | apply Pos2Nat_ne_0 ].
    rewrite Nat.div_0_l; [ simpl | apply Pos2Nat_ne_0 ].
    remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
    destruct (Nbar.lt_dec 0 (fin c)) as [H₃| H₃].
     unfold series_nth_fld; simpl.
     destruct (Nbar.lt_dec 0 1) as [H₄| H₄].
      destruct (Nbar.lt_dec 0 (fin (st * c + c))) as [H₅| H₅].
       destruct (lt_dec 0 c) as [H₆| H₆].
        rewrite fld_add_comm, fld_add_0_l; reflexivity.

        exfalso; apply H₆; subst c; apply Pos2Nat.is_pos.

       rewrite fld_add_comm, fld_add_0_l; reflexivity.

      exfalso; apply H₄; apply Nbar.lt_0_1.

     exfalso; apply H₃; constructor; subst c; apply Pos2Nat.is_pos.

   rewrite Z.mul_add_distr_r, Z.mul_1_l.
   rewrite Z.sub_add_distr, Z.sub_diag; simpl.
   rewrite Z.add_simpl_l; simpl.
   rewrite series_pad_left_0.
   unfold series_head, series_tail; simpl.
   rewrite Heqst; simpl.
   unfold series_nth_fld; simpl.
   rewrite Nat.add_0_r.
   rewrite Nat.mod_0_l; [ simpl | apply Pos2Nat_ne_0 ].
   rewrite Nat.div_0_l; [ simpl | apply Pos2Nat_ne_0 ].
   unfold series_nth_fld; simpl.
   remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
   destruct (Nbar.lt_dec 0 (fin c)) as [H₃| H₃].
    destruct (Nbar.lt_dec 0 1) as [H₄| H₄].
     destruct (Nbar.lt_dec 0 inf) as [H₅| H₅].
      destruct (lt_dec 0 c) as [H₆| H₆].
       rewrite fld_add_comm, fld_add_0_l; reflexivity.

       exfalso; apply H₆; subst c; apply Pos2Nat.is_pos.

      exfalso; apply H₅; constructor.

     exfalso; apply H₄, Nbar.lt_0_1.

    exfalso; apply H₃; subst c; constructor; apply Pos2Nat.is_pos.

  exfalso; apply H₂; subst s.
  apply stop_nz_pos_add_pos; assumption.

 destruct (Nbar.lt_dec 0 (stop s)) as [H₂| H₂]; [ idtac | reflexivity ].
 exfalso; apply H₁; subst s.
 apply stop_nz_add_pos_pos; assumption.
Qed.

(* à voir...
Lemma ps_cons2 : ∀ nz,
  series_nth_fld fld 0 (nz_terms nz) ≭ zero fld
  → nz_add (nz_head nz) (nz_tail nz) ≈ NonZero nz.
Proof.
intros nz Hznz.
apply ps_cons.
rewrite <- series_nth_add_head_tail; assumption.
Qed.
*)

(* à voir...
Lemma ps_add_cancel_0_0_l : ∀ nz₁ nz₂ nz₃,
  first_nonzero fld (nz_terms_add nz₁ nz₂) = 0%Nbar
  → first_nonzero fld (nz_terms_add nz₁ nz₃) = 0%Nbar
    → NonZero nz₂ ≈ NonZero nz₃
      → nz_add nz₁ nz₂ ≈ nz_add nz₁ nz₃.
Proof.
intros nz₁ nz₂ nz₃ Hn₂ Hn₃ H₂₃.
unfold nz_add; simpl.
rewrite Hn₂, Hn₃.
inversion H₂₃; subst.
constructor 1 with (k₁ := k₁) (k₂ := k₂); simpl.
 inversion H1; subst.
 constructor; intros i.
 unfold nz_terms_add.
 unfold cm_factor, cm; simpl.
 do 2 rewrite stretch_series_add_distr.
 do 4 rewrite stretch_pad_series_distr.
 do 4 rewrite <- stretch_stretch_series.
 do 4 rewrite Pos.mul_comm, stretch_stretch_series.
 rewrite H1.
 do 3 rewrite <- stretch_stretch_series.
 rewrite H3.
 do 4 rewrite <- Z2Nat_inj_mul_pos_r.
 do 4 rewrite Z.mul_sub_distr_r.
 rewrite <- Z.mul_assoc.
 rewrite <- Pos2Z.inj_mul.
 rewrite H3.
 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_assoc.
 replace (nz_valnum nz₂ * ' nz_comden nz₁ * ' k₁)%Z with
  (nz_valnum nz₃ * ' nz_comden nz₁ * ' k₂)%Z .
  reflexivity.

  rewrite Z.mul_shuffle0, <- H2.
  rewrite Z.mul_shuffle0; reflexivity.

 unfold cm_factor; simpl.
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul, H3.
 rewrite Pos2Z.inj_mul, Z.mul_assoc.
 replace (nz_valnum nz₂ * ' nz_comden nz₁ * ' k₁)%Z with
  (nz_valnum nz₃ * ' nz_comden nz₁ * ' k₂)%Z .
  reflexivity.

  rewrite <- Z.mul_assoc, Z.mul_comm.
  rewrite Z.mul_shuffle0.
  rewrite <- Z.mul_assoc, <- H2.
  rewrite <- Z.mul_assoc, Z.mul_comm.
  rewrite <- Z.mul_shuffle0, Z.mul_assoc.
  reflexivity.

 unfold cm.
 rewrite <- Pos.mul_assoc, H3, Pos.mul_assoc.
 reflexivity.
Qed.
*)

(* à voir...
Lemma stop_tail : ∀ s, (0 < stop s)%Nbar → stop s = NS (stop (series_tail s)).
Proof.
intros s Hs.
unfold series_tail; simpl.
destruct (stop s) as [| st]; [ simpl | reflexivity ].
rewrite <- Nat.sub_succ_l.
 simpl; rewrite Nat.sub_0_r; reflexivity.

 destruct x.
  exfalso; revert Hs; apply Nbar.lt_irrefl.

  apply -> Nat.succ_le_mono; apply Nat.le_0_l.
Qed.

Lemma stop_tail_0 : ∀ s, stop s = fin 0 → stop (series_tail s) = fin 0.
Proof.
intros s H; simpl.
rewrite H; reflexivity.
Qed.

Lemma terms_S_tail : ∀ s n, terms s (S n) = terms (series_tail s) n.
Proof.
intros s n.
unfold series_tail; reflexivity.
Qed.

Lemma first_nonzero_S_tail : ∀ s n,
  first_nonzero fld s = fin (S n)
  → first_nonzero fld (series_tail s) = fin n.
Proof.
intros s n Hn₃.
apply first_nonzero_iff in Hn₃.
apply first_nonzero_iff.
destruct Hn₃ as (Hisn, Hsn).
split; [ intros i Hin | idtac ].
 remember (stop s) as st eqn:Hst .
 symmetry in Hst.
 destruct st as [st| ].
  destruct st as [| st].
   destruct (Nbar.lt_dec (fin i) 0) as [H₁| ].
    apply Nbar.nle_gt in H₁.
    exfalso; apply H₁; constructor; apply Nat.le_0_l.

    assert (i < S n)%nat as H by omega.
    apply Hisn in H.
    unfold series_nth_fld in H.
    remember Hst as Hst₂; clear HeqHst₂.
    apply stop_0_series_nth_stretch_0 with (i := S i) (n := xH) in Hst.
    rewrite <- Hst.
    rewrite stretch_series_1.
    unfold series_nth_fld.
    rewrite <- terms_S_tail.
    rewrite Hst₂.
    rewrite stop_tail_0; [ idtac | assumption ].
    destruct (Nbar.lt_dec (fin i) 0) as [H₁| H₁].
     contradiction.

     destruct (Nbar.lt_dec (fin (S i)) 0) as [H₂| H₂].
      apply Nbar.nle_gt in H₂.
      exfalso; apply H₂; constructor; apply Nat.le_0_l.

      reflexivity.

   apply Nat.succ_lt_mono in Hin.
   apply Hisn in Hin.
   unfold series_nth_fld.
   rename Hin into H.
   unfold series_nth_fld in H.
   remember Hst as Hst₂; clear HeqHst₂.
   rewrite stop_tail in H.
    remember (series_tail s) as s₁.
    destruct (Nbar.lt_dec (fin i) (stop s₁)) as [H₁| H₁].
     destruct (Nbar.lt_dec (fin (S i)) (NS (stop s₁))) as [H₂| H₂].
      rewrite Heqs₁.
      rewrite <- terms_S_tail.
      assumption.

      exfalso; apply H₂.
      destruct (stop s₁) as [st₁| ].
       destruct st₁ as [| st₁].
        apply Nbar.nle_gt in H₁.
        exfalso; apply H₁, Nbar.le_0_l.

        simpl.
        constructor.
        apply Nbar.fin_lt_mono in H₁.
        apply Nat.succ_lt_mono in H₁; assumption.

       constructor.

     reflexivity.

    rewrite Hst.
    constructor; apply Nat.lt_0_succ.

  apply Nat.succ_lt_mono in Hin.
  apply Hisn in Hin.
  unfold series_nth_fld.
  rename Hin into H.
  unfold series_nth_fld in H.
  remember Hst as Hst₂; clear HeqHst₂.
  rewrite stop_tail in H.
   remember (series_tail s) as s₁.
   destruct (Nbar.lt_dec (fin i) (stop s₁)) as [H₁| H₁].
    destruct (Nbar.lt_dec (fin (S i)) (NS (stop s₁))) as [H₂| H₂].
     rewrite Heqs₁.
     rewrite <- terms_S_tail.
     assumption.

     exfalso; apply H₂.
     destruct (stop s₁) as [st₁| ].
      destruct st₁ as [| st₁].
       apply Nbar.nle_gt in H₁.
       exfalso; apply H₁, Nbar.le_0_l.

       simpl.
       constructor.
       apply Nbar.fin_lt_mono in H₁.
       apply Nat.succ_lt_mono in H₁; assumption.

      constructor.

    reflexivity.

   rewrite Hst; constructor.

 unfold series_nth_fld.
 unfold series_nth_fld in Hsn.
 remember (stop s) as st eqn:Hst .
 symmetry in Hst.
 destruct st as [st| ].
  destruct st as [| st].
   destruct (Nbar.lt_dec (fin (S n)) 0) as [H₁| ]; [ idtac | negation Hsn ].
   apply Nbar.nle_gt in H₁.
   exfalso; apply H₁; constructor; apply Nat.le_0_l.

   rewrite <- Hst in Hsn.
   rewrite stop_tail in Hsn.
    remember (stop (series_tail s)) as st₁.
    destruct (Nbar.lt_dec (fin n) st₁) as [H₁| H₁].
     destruct (Nbar.lt_dec (fin (S n)) (NS st₁)) as [H₂| H₂].
      rewrite <- terms_S_tail; assumption.

      negation Hsn.

     destruct (Nbar.lt_dec (fin (S n)) (NS st₁)) as [H₂| H₂].
      exfalso; apply H₁.
      destruct st₁ as [st₁| ]; [ idtac | constructor ].
      constructor.
      apply Nat.succ_lt_mono.
      inversion H₂; assumption.

      negation Hsn.

    rewrite Hst.
    constructor.
    apply Nat.lt_0_succ.

  rewrite <- Hst in Hsn.
  rewrite stop_tail in Hsn.
   remember (stop (series_tail s)) as st₁.
   destruct (Nbar.lt_dec (fin n) st₁) as [H₁| H₁].
    destruct (Nbar.lt_dec (fin (S n)) (NS st₁)) as [H₂| H₂].
     rewrite <- terms_S_tail; assumption.

     negation Hsn.

    destruct (Nbar.lt_dec (fin (S n)) (NS st₁)) as [H₂| H₂].
     exfalso; apply H₁.
     destruct st₁ as [st₁| ]; [ idtac | constructor ].
     constructor.
     apply Nat.succ_lt_mono.
     inversion H₂; assumption.

     negation Hsn.

   rewrite Hst; constructor.
Qed.
*)

Definition series_tail_n n (s : series α) :=
  {| terms i := terms s (i + n); stop := stop s - fin n |}.

Definition stretch_series_nat n s :=
  {| terms i :=
       if zerop (i mod n) then
         series_nth_fld fld (i / n) s
       else zero fld;
     stop :=
       stop s * fin n |}.

Lemma stretch_series_to_nat : ∀ k s,
  stretch_series fld k s = stretch_series_nat (Pos.to_nat k) s.
Proof. reflexivity. Qed.

Lemma series_tail_n_tail_comm : ∀ n s,
  series_tail (series_tail_n n s) = series_tail_n n (series_tail s).
Proof.
intros n s.
unfold series_tail_n, series_tail.
simpl; f_equal.
destruct (stop s) as [st| ]; [ idtac | reflexivity ].
rewrite <- Nat.sub_add_distr, Nat.add_comm, Nat.sub_add_distr.
reflexivity.
Qed.

Lemma series_nth_tail : ∀ i s,
  series_nth_fld fld i (series_tail s) = series_nth_fld fld (S i) s.
Proof.
intros i s.
unfold series_nth_fld, series_tail; simpl.
remember (stop s) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ].
 destruct (Nbar.lt_dec (fin i) (fin (st - 1))) as [H₁| H₁].
  destruct (Nbar.lt_dec (fin (S i)) (fin st)) as [H₂| H₂].
   reflexivity.

   destruct st as [| st].
    apply Nbar.nle_gt in H₁.
    exfalso; apply H₁, Nbar.le_0_l.

    simpl in H₁; rewrite Nat.sub_0_r in H₁.
    apply Nbar.succ_lt_mono in H₁.
    exfalso; apply H₂; assumption.

  destruct (Nbar.lt_dec (fin (S i)) (fin st)) as [H₂| H₂].
   destruct st as [| st].
    apply Nbar.nle_gt in H₂.
    exfalso; apply H₂, Nbar.le_0_l.

    simpl in H₁; rewrite Nat.sub_0_r in H₁.
    exfalso; apply H₁, Nbar.succ_lt_mono.
    assumption.

   reflexivity.

 destruct (Nbar.lt_dec (fin i) ∞) as [H₁| H₁].
  destruct (Nbar.lt_dec (fin (S i)) ∞) as [H₂| H₂]; [ reflexivity | idtac ].
  exfalso; apply H₂; constructor.

  exfalso; apply H₁; constructor.
Qed.

Lemma stretch_series_tail : ∀ k s,
  stretch_series fld k (series_tail s)
  ≃ series_tail_n (Pos.to_nat k) (stretch_series fld k s).
Proof.
intros k s.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite Nat.add_mod; [ idtac | apply Pos2Nat_ne_0 ].
rewrite Nat.mod_same; [ idtac | apply Pos2Nat_ne_0 ].
rewrite Nat.add_0_r.
rewrite Nat.mod_mod; [ idtac | apply Pos2Nat_ne_0 ].
remember (stop s) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ]; simpl.
 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
 rewrite series_nth_tail.
 remember (Pos.to_nat k) as x.
 replace (i + x)%nat with (i + 1 * x)%nat .
  rewrite Nat.div_add; [ idtac | subst x; apply Pos2Nat_ne_0 ].
  rewrite Nat.add_comm; reflexivity.

  rewrite Nat.mul_1_l; reflexivity.

 rewrite series_nth_tail.
 remember (Pos.to_nat k) as x.
 replace (i + x)%nat with (i + 1 * x)%nat .
  rewrite Nat.div_add; [ idtac | subst x; apply Pos2Nat_ne_0 ].
  rewrite Nat.add_comm; reflexivity.

  rewrite Nat.mul_1_l; reflexivity.
Qed.

(*
Definition norm_nz nz₁ nz₂ :=
  let v₁ := (nz_valnum nz₁ * 'cm_factor nz₁ nz₂)%Z in
  let v₂ := (nz_valnum nz₂ * 'cm_factor nz₂ nz₁)%Z in
  let s₁ := stretch_series fld (cm_factor nz₁ nz₂) (nz_terms nz₁) in
  {| nz_terms := series_pad_left fld (Z.to_nat (v₁ - v₂)) s₁;
     nz_valnum := Z.min v₁ v₂;
     nz_comden := cm nz₁ nz₂ |}.

Lemma nz_add_norm : ∀ nz₁ nz₂ v,
  NonZero (build_nz_add fld v nz₁ nz₂)
  ≈ NonZero
      (build_nz_add fld (v * Pos.to_nat (nz_comden nz₁ * nz_comden nz₂))%nat
         (norm_nz nz₁ nz₂) (norm_nz nz₂ nz₁)).
Proof.
intros nz₁ nz₂ v.
remember (nz_comden nz₁ * nz_comden nz₂)%positive as c.
constructor 1 with (k₁ := c) (k₂ := xH); subst c; simpl.
 constructor; intros i.
 unfold series_nth_fld; simpl.
 unfold cm_factor, cm; simpl.
 remember (nz_valnum nz₁) as v₁ eqn:Hv₁ .
 remember (nz_valnum nz₂) as v₂ eqn:Hv₂ .
 remember (nz_comden nz₁) as c₁ eqn:Hc₁ .
 remember (nz_comden nz₂) as c₂ eqn:Hc₂ .
 symmetry in Hv₁, Hv₂, Hc₁, Hc₂.
 rewrite divmod_div.
 rewrite Nat.div_1_r.
 rewrite Z.min_comm.
 replace (c₂ * c₁)%positive with (c₁ * c₂)%positive by apply Pos.mul_comm.
 rewrite Z.sub_diag; simpl.
 do 2 rewrite Nbar.add_0_r.
 remember (Z.to_nat (v₁ * ' c₂ - v₂ * ' c₁))%Z as vc₁ eqn:Hvc₁ .
 remember (Z.to_nat (v₂ * ' c₁ - v₁ * ' c₂))%Z as vc₂ eqn:Hvc₂ .
 symmetry in Hvc₁, Hvc₂.
 rewrite Nbar.mul_1_r.
 rewrite Nbar.mul_max_distr_r.
 remember
  (Nbar.max (stop (nz_terms nz₁) * fin (Pos.to_nat c₂) + fin vc₁)
     (stop (nz_terms nz₂) * fin (Pos.to_nat c₁) + fin vc₂) *
   fin (Pos.to_nat (c₁ * c₂)))%Nbar as x.
 destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁]; [ idtac | reflexivity ].
 destruct (zerop (i mod Pos.to_nat (c₁ * c₂))) as [H₂| H₂].
  apply Nat.mod_divides in H₂; [ idtac | apply Pos2Nat_ne_0 ].
  destruct H₂ as (k, Hi).
  rewrite Hi.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
  unfold nz_terms_add; simpl.
  unfold cm_factor, cm; simpl.
  rewrite Hv₁, Hv₂, Hc₁, Hc₂.
  rewrite Hvc₁, Hvc₂.
  rewrite Z.min_comm.
  replace (c₂ * c₁)%positive with (c₁ * c₂)%positive by apply Pos.mul_comm.
  rewrite Z.sub_diag; simpl.
  do 2 rewrite series_pad_left_0.
  rewrite <- stretch_series_add_distr.
  rewrite Nat.mul_comm.
  rewrite series_nth_fld_mul_stretch.
  reflexivity.

  remember (norm_nz nz₁ nz₂) as nz'₁.
  remember (norm_nz nz₂ nz₁) as nz'₂.
  unfold nz_terms_add.
  subst nz'₁ nz'₂; simpl.
  unfold cm_factor, cm; simpl.
  rewrite Hv₁, Hv₂, Hc₁, Hc₂.
  rewrite Hvc₁, Hvc₂.
  rewrite Z.min_comm.
  replace (c₂ * c₁)%positive with (c₁ * c₂)%positive by apply Pos.mul_comm.
  rewrite Z.sub_diag; simpl.
  do 2 rewrite series_pad_left_0.
  rewrite <- stretch_series_add_distr.
  symmetry.
  rewrite padded_in_stretched; [ reflexivity | assumption ].

 unfold cm_factor, cm; simpl.
 rewrite Z.mul_1_r.
 symmetry.
 rewrite Z.min_l.
  rewrite Nat2Z.inj_mul.
  rewrite positive_nat_Z.
  rewrite Z.mul_add_distr_r.
  rewrite Pos.mul_comm.
  reflexivity.

  rewrite Z.min_comm, Pos.mul_comm; reflexivity.

 rewrite Pos.mul_1_r.
 unfold cm; simpl.
 unfold cm; simpl.
 f_equal.
 apply Pos.mul_comm.
Qed.

Definition norm₂_nz (nz₁ nz₂ nz₃ : nz_ps α) :=
  let c₁ := nz_comden nz₁ in
  let c₂ := nz_comden nz₂ in
  let c₃ := nz_comden nz₃ in
  let v₁ := (nz_valnum nz₁ * 'c₂ * 'c₃)%Z in
  let v₂ := (nz_valnum nz₂ * 'c₃ * 'c₁)%Z in
  let v₃ := (nz_valnum nz₃ * 'c₁ * 'c₂)%Z in
  let vm := Z.min v₁ (Z.min v₂ v₃) in
  let s₁ := stretch_series fld (c₂ * c₃) (nz_terms nz₁) in
  {| nz_terms := series_pad_left fld (Z.to_nat (v₁ - vm)) s₁;
     nz_valnum := vm;
     nz_comden := c₁ * c₂ * c₃ |}.

Lemma nz_add_norm₂ : ∀ nz₁ nz₂ nz₃ v,
  NonZero (build_nz_add fld v nz₁ nz₂)
  ≈ NonZero
      (build_nz_add fld
         (v *
          Pos.to_nat
            (nz_comden nz₁ * nz_comden nz₂ * nz_comden nz₃ * nz_comden nz₃))
         (norm₂_nz nz₁ nz₂ nz₃) (norm₂_nz nz₂ nz₁ nz₃)).
Proof.
intros nz₁ nz₂ nz₃ v.
remember (nz_comden nz₁) as c₁ eqn:Hc₁ .
remember (nz_comden nz₂) as c₂ eqn:Hc₂ .
remember (nz_comden nz₃) as c₃ eqn:Hc₃ .
symmetry in Hc₁, Hc₂, Hc₃.
remember (c₁ * c₂ * c₃ * c₃)%positive as c.
constructor 1 with (k₁ := c) (k₂ := xH); subst c; simpl.
 3: unfold cm; simpl.
 3: rewrite Hc₁, Hc₂, Hc₃.
 Focus 2.
 unfold cm_factor.
 rewrite Hc₁, Hc₂, Hc₃.
 remember (nz_valnum nz₁) as v₁ eqn:Hv₁ .
 remember (nz_valnum nz₂) as v₂ eqn:Hv₂ .
 remember (nz_valnum nz₃) as v₃ eqn:Hv₃ .
 rewrite Z.mul_add_distr_r.
 rewrite Z.mul_1_r.
 f_equal.
  symmetry.
  rewrite Z.min_l.
   rewrite Z.min_assoc.
bbb.
mmm.... pas sûr que ce soit bon.
*)

(*
Lemma zzz : ∀ nz₁ nz₂ nz₃ n,
  NonZero nz₂ ≈ NonZero nz₃
  → NonZero (build_nz_add fld 0 nz₁ nz₂)
    ≈ NonZero (build_nz_add fld n nz₁ nz₃).
Proof.
intros nz₁ nz₂ nz₃ n H₂₃.
rewrite nz_add_norm₂ with (nz₃ := nz₃); symmetry.
rewrite nz_add_norm₂ with (nz₃ := nz₂); symmetry; simpl.
bbb.
intros nz₁ nz₂ nz₃ n H₂₃.
rewrite nz_add_norm; symmetry.
rewrite nz_add_norm; symmetry.
rewrite Nat.mul_0_l.
revert nz₁ nz₂ nz₃ H₂₃.
induction n; intros.
 inversion H₂₃; subst; simpl.
 constructor 1 with (k₁ := k₁) (k₂ := k₂); simpl.
  inversion H1; subst.
  constructor; intros i.
  remember norm_nz as f.
  unfold nz_terms_add.
  unfold cm_factor, cm; simpl.
  do 2 rewrite stretch_series_add_distr.
  do 4 rewrite stretch_pad_series_distr.
  do 4 rewrite <- stretch_stretch_series.
  do 4 rewrite Pos.mul_comm, stretch_stretch_series.
  subst f; simpl.
  unfold cm_factor, cm; simpl.
  remember (nz_valnum nz₁) as v₁ eqn:Hv₁ .
  remember (nz_valnum nz₂) as v₂ eqn:Hv₂ .
  remember (nz_valnum nz₃) as v₃ eqn:Hv₃ .
  remember (nz_comden nz₁) as c₁ eqn:Hc₁ .
  remember (nz_comden nz₂) as c₂ eqn:Hc₂ .
  remember (nz_comden nz₃) as c₃ eqn:Hc₃ .
  rewrite Z.min_comm, Pos.mul_comm, Z.sub_diag; symmetry.
  rewrite Z.min_comm, Pos.mul_comm, Z.sub_diag; symmetry.
  simpl.
  do 4 rewrite series_pad_left_0.
  do 8 rewrite stretch_pad_series_distr.
  do 8 rewrite <- stretch_stretch_series.
  move H1 at bottom.
  move H2 at bottom.
  move H3 at bottom.
  remember (Z.to_nat (v₁ * ' c₃ - v₃ * ' c₁) * Pos.to_nat k₂)%nat as x.
  assert (Z.to_nat (v₁ * ' c₂ - v₂ * ' c₁) * Pos.to_nat k₁ = x)%nat as H₁.
   subst x.
   do 2 rewrite <- Z2Nat_inj_mul_pos_r.
   do 2 rewrite Z.mul_sub_distr_r.
   assert (v₂ * ' c₁ * ' k₁ = v₃ * ' c₁ * ' k₂)%Z as H₁.
    rewrite Z.mul_shuffle0, H2, Z.mul_shuffle0; reflexivity.

    rewrite H₁; clear H₁; rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
    rewrite H3, Pos2Z.inj_mul, Z.mul_assoc; reflexivity.

   rewrite H₁; clear H₁.
   rewrite Pos2Nat.inj_mul, Nat.mul_assoc.
   rewrite Pos.mul_comm.
   rewrite stretch_stretch_series.
   rewrite <- stretch_pad_series_distr.
   rewrite <- Pos.mul_assoc, H3, Pos.mul_assoc.
   symmetry.
   rewrite Pos2Nat.inj_mul, Nat.mul_assoc.
   rewrite Pos.mul_comm.
   rewrite stretch_stretch_series.
   rewrite <- stretch_pad_series_distr.
   symmetry.
   rewrite series_add_comm.
   remember (Z.to_nat (v₃ * ' c₁ - v₁ * ' c₃) * Pos.to_nat k₂)%nat as y.
   assert (Z.to_nat (v₂ * ' c₁ - v₁ * ' c₂) * Pos.to_nat k₁ = y)%nat as H₁.
    subst y.
    do 2 rewrite <- Z2Nat_inj_mul_pos_r.
    do 2 rewrite Z.mul_sub_distr_r.
    assert (v₁ * ' c₂ * ' k₁ = v₁ * ' c₃ * ' k₂)%Z as H₁.
     rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
     rewrite H3.
     rewrite Pos2Z.inj_mul, Z.mul_assoc.
     reflexivity.

     rewrite H₁; clear H₁.
     rewrite Z.mul_shuffle0, H2, Z.mul_shuffle0.
     reflexivity.

    rewrite H₁; clear H₁.
    assert
     (stretch_series fld (c₁ * c₃ * k₂ * c₁) (nz_terms nz₂)
      ≃ stretch_series fld (c₁ * c₂ * k₂ * c₁) (nz_terms nz₃)) 
     as H₁.
     assert (c₁ * c₃ * k₂ * c₁ = c₁ * c₂ * k₁ * c₁)%positive as H₁.
      f_equal.
      rewrite <- Pos.mul_assoc, <- H3, Pos.mul_assoc.
      reflexivity.

      rewrite H₁; clear H₁.
      rewrite Pos_mul_shuffle0.
      rewrite stretch_stretch_series, H1, <- stretch_stretch_series.
      rewrite Pos_mul_shuffle0; reflexivity.

     rewrite H₁; clear H₁.
     rewrite Nat.mul_assoc.
     assert (c₁ * c₂ * k₂ * c₁ = c₂ * (c₁ * k₂ * c₁))%positive as H₁.
      rewrite Pos.mul_assoc; f_equal.
      rewrite Pos.mul_assoc; f_equal.
      apply Pos.mul_comm.

      rewrite H₁; clear H₁.
      rewrite stretch_stretch_series.
      rewrite <- stretch_pad_series_distr.
      rewrite <- stretch_series_add_distr.
      rewrite series_add_comm.
      symmetry.
      rewrite series_add_comm.
      rewrite Nat.mul_assoc.
      assert (c₁ * c₃ * k₂ * c₁ = c₃ * (c₁ * k₂ * c₁))%positive as H₁.
       rewrite Pos.mul_assoc; f_equal.
       rewrite Pos.mul_assoc; f_equal.
       apply Pos.mul_comm.

       rewrite H₁; clear H₁.
       rewrite stretch_stretch_series.
       rewrite <- stretch_pad_series_distr.
       rewrite <- stretch_series_add_distr.
       rewrite series_add_comm.
       remember
        (series_add fld
           (series_pad_left fld (x * Pos.to_nat c₁)
              (stretch_series fld (c₁ * c₃ * k₂) (nz_terms nz₁)))
           (series_pad_left fld (y * Pos.to_nat c₁)
              (stretch_series fld (c₁ * k₂ * c₁) (nz_terms nz₃)))) as z.
       do 2 rewrite <- Pos.mul_assoc in Heqz.
       subst z.
       rewrite stretch_stretch_series.
       rewrite <- stretch_pad_series_distr.
       rewrite series_add_comm.
       rewrite stretch_stretch_series.
       rewrite <- stretch_pad_series_distr.
       rewrite <- stretch_series_add_distr.
       remember
        (stretch_series fld c₁
           (series_add fld
              (series_pad_left fld y
                 (stretch_series fld (k₂ * c₁) (nz_terms nz₃)))
              (series_pad_left fld x
                 (stretch_series fld (c₃ * k₂) (nz_terms nz₁))))) as z.
Focus 1.
bbb.
*)

(*
Lemma ps_add_cancel_l : ∀ ps₁ ps₂ ps₃,
  ps₂ ≈ ps₃
  → ps_add fld ps₁ ps₂ ≈ ps_add fld ps₁ ps₃.
Proof.
intros ps₁ ps₂ ps₃ H₂₃.
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ].
  destruct ps₃ as [nz₃| ]; simpl.
   remember (first_nonzero fld (nz_terms_add fld nz₁ nz₂)) as n₂ eqn:Hn₂ .
   symmetry in Hn₂.
   destruct n₂ as [n₂| ].
    revert nz₁ nz₂ nz₃ H₂₃ Hn₂.
    induction n₂; intros.
     remember (first_nonzero fld (nz_terms_add fld nz₁ nz₃)) as n₃ eqn:Hn₃ .
     symmetry in Hn₃.
     destruct n₃ as [n₃| ].
      unfold nz_add.
      rewrite Hn₂, Hn₃.
bbb.
      revert nz₁ nz₂ nz₃ H₂₃ Hn₂ Hn₃.
      induction n₃; intros.
       apply ps_add_cancel_0_0_l; assumption.
bbb.
*)

(*
Theorem ps_add_compat : ∀ ps₁ ps₂ ps₃ ps₄,
  ps₁ ≈ ps₂
  → ps₃ ≈ ps₄
    → ps_add fld ps₁ ps₃ ≈ ps_add fld ps₂ ps₄.
Proof.
intros ps₁ ps₃ ps₂ ps₄ H₁ H₂.
transitivity (ps_add fld ps₁ ps₄).
bbb.
 apply ps_add_cancel_l; assumption.

 rewrite ps_add_comm; symmetry.
 rewrite ps_add_comm; symmetry.
 apply ps_add_cancel_l; assumption.
Qed.
*)

(*
  NonZero (build_nz_add fld n nz₁ nz₂)
  = ps_add fld (nz_add fld (nz_head nz₁) (nz_tail nz₁)) (Nonzero nz₂).
*)

(*
Add Parametric Morphism : (ps_add fld) with 
signature (eq_ps fld) ==> (eq_ps fld) ==> (eq_ps fld) as ps_add_morph.
Proof.
intros ps₁ ps₃ H₁ ps₂ ps₄ H₂.
bbb.
*)

Theorem ps_add_0_l : ∀ ps, ps_add (ps_zero _) ps ≈ ps.
Proof. reflexivity. Qed.

Definition nz_neg nz :=
  {| nz_terms := series_neg fld (nz_terms nz);
     nz_valnum := nz_valnum nz;
     nz_comden := nz_comden nz |}.

Definition ps_neg ps :=
  match ps with
  | NonZero nz => NonZero (nz_neg nz)
  | Zero => Zero _
  end.

Lemma add_neg_nth : ∀ s i,
  add fld (series_nth_fld fld i s) (series_nth_fld fld i (series_neg fld s)) ≍
  zero fld.
Proof.
intros s i.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin i) (stop s)).
 apply fld_add_neg.

 apply fld_add_0_l.
Qed.

(*
Definition eq_nz nz₁ nz₂ :=
  nz_valnum nz₁ = nz_valnum nz₂ ∧
  nz_comden nz₁ = nz_comden nz₂ ∧
  nz_terms nz₁ ≃ nz_terms nz₂.

Add Parametric Morphism : (@mknz α)
with signature eq_series fld ==> eq ==> eq ==> eq_nz as mknz_morph.
Proof.
bbb.
*)

(*
Definition eq_nz nz₁ nz₂ :=
  nz_valnum nz₁ = nz_valnum nz₂ ∧
  nz_comden nz₁ = nz_comden nz₂ ∧
  nz_terms nz₁ ≃ nz_terms nz₂.

Axiom eq_nz_refl : reflexive _ eq_nz.
Axiom eq_nz_sym : symmetric _ eq_nz.
Axiom eq_nz_trans : transitive _ eq_nz.

Add Parametric Relation : (nz_ps α) eq_nz
 reflexivity proved by eq_nz_refl
 symmetry proved by eq_nz_sym
 transitivity proved by eq_nz_trans
 as eq_nz_rel.

Add Parametric Morphism : (@NonZero α)
with signature eq_nz ==> eq_ps fld as NonZero_morph.
Proof.
bbb.
*)

(*
Add Parametric Morphism :
  (λ s v c, NonZero {| nz_terms := s; nz_valnum := v; nz_comden := c |})
with signature eq_series fld ==> eq ==> eq ==> eq_ps fld as NonZero_morph₁.
Proof.
bbb.
*)

Definition mk_nonzero (s : series α) v c := NonZero (mknz s v c).

Lemma fold_mk_nonzero : ∀ (s : series α) v c,
  NonZero (mknz s v c) = mk_nonzero s v c.
Proof. reflexivity. Qed.

Add Parametric Morphism : mk_nonzero
with signature eq_series fld ==> eq ==> eq ==> eq_ps fld as NonZero_morph.
Proof.
intros s₁ s₂ Heq v c.
constructor.
unfold normalise_nz; simpl.
rewrite <- Heq.
remember (first_nonzero fld s₁) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor; simpl; rewrite Heq; reflexivity.
Qed.

Theorem ps_add_neg : ∀ ps, ps_add ps (ps_neg ps) ≈ ps_zero _.
Proof.
intros ps.
unfold ps_zero.
unfold ps_add; simpl.
destruct ps as [nz| ]; [ simpl | reflexivity ].
unfold build_nz_add.
unfold nz_neg; simpl.
unfold cm_factor; simpl.
rewrite Z.min_id.
unfold cm; simpl.
unfold nz_terms_add; simpl.
unfold cm_factor; simpl.
rewrite Z.sub_diag; simpl.
rewrite fold_mk_nonzero.
do 2 rewrite series_pad_left_0.
rewrite <- stretch_series_add_distr.
rewrite series_add_neg.
rewrite stretch_series_series_0.
unfold mk_nonzero.
constructor; reflexivity.
Qed.

(* just to test... *)
Definition nz_zero :=
  {| nz_terms := series_0 fld;
     nz_valnum := 0;
     nz_comden := 1 |}.

Lemma series_pad_series_0 : ∀ n,
  series_pad_left fld n (series_0 fld) ≃ series_0 fld.
Proof.
intros n.
constructor; intros i.
unfold series_nth_fld; simpl.
remember (Nbar.lt_dec (fin i) (fin n)) as d₁.
remember (lt_dec i n) as d₂.
remember (Nbar.lt_dec (fin i) 0) as d₃.
destruct d₁, d₂, d₃; reflexivity.
Qed.

Lemma nz_add_0_r : ∀ nz,
  nz_terms_add nz nz_zero ≃
  series_pad_left fld (Z.to_nat (nz_valnum nz)) (nz_terms nz).
Proof.
intros nz.
unfold nz_terms_add; simpl.
rewrite Z.mul_1_r, Z.sub_0_r.
rewrite stretch_series_1.
rewrite stretch_series_series_0.
rewrite series_pad_series_0.
rewrite series_add_comm.
rewrite series_add_0_l.
reflexivity.
Qed.

Lemma series_nth_0_series_nth_pad_0 : ∀ s n,
  (∀ i : nat, series_nth_fld fld i s ≍ zero fld)
  → ∀ i, series_nth_fld fld i (series_pad_left fld n s) ≍ zero fld.
Proof.
intros s n H i.
revert i.
induction n as [| n]; intros.
 rewrite series_pad_left_0; apply H.

 destruct i.
  unfold series_nth_fld; simpl.
  destruct (Nbar.lt_dec 0 (stop s + fin (S n))); reflexivity.

  rewrite <- series_nth_pad_S; apply IHn.
Qed.

Lemma series_nth_pad_0_series_nth_0 : ∀ s n,
  (∀ i : nat, series_nth_fld fld i (series_pad_left fld n s) ≍ zero fld)
  → ∀ i, series_nth_fld fld i s ≍ zero fld.
Proof.
intros s n H i.
revert i.
induction n as [| n]; intros.
 rewrite <- series_pad_left_0; apply H.

 apply IHn; intros j.
 rewrite series_nth_pad_S; apply H.
Qed.

(*
Lemma series_nth_pad_0_P_series_nth_0 : ∀ s n P,
  (∀ i, P i → series_nth_fld fld i (series_pad_left fld n s) ≍ zero fld)
  → ∀ i, P i
    → series_nth_fld fld i s ≍ zero fld.
Proof.
intros s n P H i Pi.
revert i Pi.
induction n; intros.
 rewrite <- series_pad_left_0.
 apply H; assumption.

 apply IHn; [ intros j Pj | assumption ].
 rewrite series_nth_pad_S.
bbb.
*)

Lemma normalise_series_add_pad : ∀ s n m k,
  normalise_series fld (n + m) k (series_pad_left fld m s)
  ≃ normalise_series fld n k s.
Proof.
intros s n m k.
unfold normalise_series.
destruct k; [ reflexivity | idtac ].
constructor; intros i.
unfold series_nth_fld.
remember Nbar_div_sup as f; simpl; subst f.
do 2 rewrite Nbar.fold_sub.
replace (stop s + fin m - fin (n + m))%Nbar with (stop s - fin n)%Nbar .
 remember (Nbar_div_sup (stop s - fin n) (fin (S k))) as x eqn:Hx .
 destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁]; [ idtac | reflexivity ].
 subst x.
 remember (i * S k)%nat as x.
 replace (n + m + x - m)%nat with (n + x)%nat by omega.
 subst x.
 destruct (lt_dec (n + m + i * S k) m) as [H₂| H₂]; [ idtac | reflexivity ].
 rewrite Nat.add_shuffle0, Nat.add_comm in H₂.
 apply Nat.nle_gt in H₂.
 exfalso; apply H₂.
 apply Nat.le_add_r.

 simpl.
 destruct (stop s) as [st| ]; [ simpl | reflexivity ].
 apply Nbar.fin_inj_wd.
 omega.
Qed.

Lemma normalise_nz_add_0_r : ∀ nz,
  eq_norm_ps fld
    (normalise_nz fld (build_nz_add nz nz_zero))
    (normalise_nz fld nz).
Proof.
intros nz.
unfold normalise_nz; simpl.
rewrite nz_add_0_r.
rewrite first_nonzero_pad.
remember (first_nonzero fld (nz_terms nz)) as n₁ eqn:Hn₁ .
symmetry in Hn₁.
rewrite Nbar.add_comm.
destruct n₁ as [n₁| ]; [ simpl | reflexivity ].
constructor; simpl.
 rewrite Z.mul_1_r.
 rewrite nz_add_0_r.
 rewrite Nat2Z.inj_add.
 rewrite Z.add_assoc, Z.add_shuffle0.
 rewrite stretching_factor_pad.
 do 2 f_equal.
 rewrite Z2Nat_id_max, Z.min_comm.
 destruct (Z_le_dec (nz_valnum nz) 0) as [H₁| H₁].
  rewrite Z.min_r; [ idtac | assumption ].
  rewrite Z.max_l; [ idtac | assumption ].
  rewrite Z.add_0_r; reflexivity.

  apply Z.nle_gt, Z.lt_le_incl in H₁.
  rewrite Z.min_l; [ idtac | assumption ].
  rewrite Z.max_r; [ idtac | assumption ].
  reflexivity.

 unfold cm; simpl.
 rewrite Pos.mul_1_r.
 rewrite nz_add_0_r.
 rewrite stretching_factor_pad.
 reflexivity.

 rewrite nz_add_0_r.
 rewrite stretching_factor_pad.
 rewrite normalise_series_add_pad.
 reflexivity.
Qed.

(*
Lemma yyy : ∀ nz₁ nz₂ n₁ n₂,
  first_nonzero fld (nz_terms nz₁) = n₁
  → first_nonzero fld (nz_terms nz₂) = n₂
    → first_nonzero fld (nz_terms_add nz₁ nz₂) = Nbar.min n₁ n₂.
Proof.
intros nz₁ nz₂ n₁ n₂ Hn₁ Hn₂.
apply first_nonzero_iff in Hn₁.
apply first_nonzero_iff in Hn₂.
apply first_nonzero_iff.
destruct n₁ as [n₁| ].
 destruct Hn₁ as (Hin₁, Hnn₁).
 destruct n₂ as [n₂| ].
  destruct Hn₂ as (Hin₂, Hnn₂).
  simpl; split.
   intros i Hlt.
   destruct (lt_dec n₁ n₂) as [H₁| H₁].
    rewrite Nat.min_l in Hlt; [ idtac | apply Nat.lt_le_incl; assumption ].
    remember Hlt as H₂; clear HeqH₂.
    apply Hin₁ in H₂.
    apply Nat.lt_trans with (n := i) in H₁; [ idtac | assumption ].
    apply Hin₂ in H₁.
    unfold series_nth_fld.
    unfold series_nth_fld in H₁.
    unfold series_nth_fld in H₂.
    destruct (Nbar.lt_dec (fin i) (stop (nz_terms nz₂))) as [H₃| H₃].
     destruct (Nbar.lt_dec (fin i) (stop (nz_terms nz₁))) as [H₄| H₄].
      destruct (Nbar.lt_dec (fin i) (stop (nz_terms_add nz₁ nz₂)))
       as [H₅| H₅].
       simpl.
       unfold cm_factor.
       Focus 1.
bbb.
*)

Lemma nz_norm_add_compat_r : ∀ nz₁ nz₂ nz₃,
  eq_norm_ps fld (normalise_nz fld nz₁) (normalise_nz fld nz₂)
  → eq_norm_ps fld
      (normalise_nz fld (build_nz_add nz₁ nz₃))
      (normalise_nz fld (build_nz_add nz₂ nz₃)).
Proof.
intros nz₁ nz₂ nz₃ Heq.
unfold normalise_nz in Heq; simpl in Heq.
remember (first_nonzero fld (nz_terms nz₁)) as n₁ eqn:Hn₁ .
remember (first_nonzero fld (nz_terms nz₂)) as n₂ eqn:Hn₂ .
symmetry in Hn₁, Hn₂.
destruct n₁ as [n₁| ].
 destruct n₂ as [n₂| ].
  inversion_clear Heq; simpl in *.
  remember (stretching_factor fld (nz_terms nz₁)) as k₁ eqn:Hk₁ .
  remember (stretching_factor fld (nz_terms nz₂)) as k₂ eqn:Hk₂ .
  symmetry in Hk₁, Hk₂.
  apply stretching_factor_iff in Hk₁.
  apply stretching_factor_iff in Hk₂.
  rewrite Hn₁ in Hk₁.
  rewrite Hn₂ in Hk₂.
  destruct Hk₁ as (Hk₁, (Hik₁, Hlt₁)).
  destruct Hk₂ as (Hk₂, (Hik₂, Hlt₂)).
  unfold normalise_nz.
  remember (first_nonzero fld (nz_terms (nz₁ ∔ nz₃))) as n₁₃ eqn:Hn₁₃ .
  remember (first_nonzero fld (nz_terms (nz₂ ∔ nz₃))) as n₂₃ eqn:Hn₂₃ .
  symmetry in Hn₁₃, Hn₂₃.
  simpl in Hn₁₃, Hn₂₃.
  simpl.
  remember (stretching_factor fld (nz_terms_add nz₁ nz₃)) as k₁₃ eqn:Hk₁₃ .
  remember (stretching_factor fld (nz_terms_add nz₂ nz₃)) as k₂₃ eqn:Hk₂₃ .
  symmetry in Hk₁₃, Hk₂₃.
  destruct n₁₃ as [n₁₃| ].
   destruct n₂₃ as [n₂₃| ].
    destruct k₁₃ as [k₁₃| ].
     apply stretching_factor_iff in Hk₁₃.
     rewrite Hn₁₃ in Hk₁₃.
     destruct Hk₁₃ as (Hk, _).
     exfalso; apply Hk; reflexivity.

     destruct k₂₃ as [k₂₃| ].
      apply stretching_factor_iff in Hk₂₃.
      rewrite Hn₂₃ in Hk₂₃.
      destruct Hk₂₃ as (Hk, _).
      exfalso; apply Hk; reflexivity.

      constructor; [ simpl | simpl | idtac ].
       unfold cm_factor.
    Focus 1.
bbb.
  destruct k₁ as [| k₁]; [ discriminate Hk₁ | idtac ].
  destruct k₂ as [| k₂]; [ discriminate Hk₂ | idtac ].
  unfold normalise_nz; simpl.
  remember (first_nonzero fld (nz_terms_add nz₁ nz₃)) as n₁₃ eqn:Hn₁₃ .
  remember (first_nonzero fld (nz_terms_add nz₂ nz₃)) as n₂₃ eqn:Hn₂₃ .
  symmetry in Hn₁₃, Hn₂₃.
  destruct n₁₃ as [n₁₃| ].
    destruct n₂₃ as [n₂₃| ].
    constructor; simpl.
     Focus 1.
     unfold cm_factor; simpl.
     remember (stretching_factor fld (nz_terms_add nz₁ nz₃)) as k₁₃.
     remember (stretching_factor fld (nz_terms_add nz₂ nz₃)) as k₂₃.
     rename Heqk₁₃ into Hk₁₃.
     rename Heqk₂₃ into Hk₂₃.
     symmetry in Hk₁₃, Hk₂₃.
     apply stretching_factor_iff in Hk₁₃.
     apply stretching_factor_iff in Hk₂₃.
     rewrite Hn₁₃ in Hk₁₃.
     rewrite Hn₂₃ in Hk₂₃.
     destruct k₁₃ as [| k₁₃]; [ discriminate Hk₁₃ | idtac ].
     destruct k₂₃ as [| k₂₃]; [ discriminate Hk₂₃ | idtac ].
bbb.
*)
(*
     assert (nz₃ = nz_zero).
      Focus 2.
      subst nz₃; simpl.
      rewrite nz_add_0_r in Hn₁₃.
      rewrite nz_add_0_r in Hn₂₃.
      rewrite first_nonzero_pad in Hn₁₃.
      rewrite first_nonzero_pad in Hn₂₃.
      do 2 rewrite Z.mul_1_r.
      rewrite Hn₁ in Hn₁₃.
      rewrite Hn₂ in Hn₂₃.
      simpl in Hn₁₃, Hn₂₃.
      injection Hn₁₃; clear Hn₁₃; intros Hn₁₃.
      injection Hn₂₃; clear Hn₂₃; intros Hn₂₃.
      rewrite <- Hn₁₃, <- Hn₂₃.
      do 2 rewrite Nat2Z.inj_add.
      do 2 rewrite Z2Nat_id_max.
*)

Lemma ps_add_compat_r : ∀ ps₁ ps₂ ps₃,
  ps₁ ≈ ps₂
  → ps_add ps₁ ps₃ ≈ ps_add ps₂ ps₃.
Proof.
intros ps₁ ps₂ ps₃ H₁₂.
unfold ps_add.
destruct ps₁ as [nz₁| ].
 destruct ps₂ as [nz₂| ].
  destruct ps₃ as [nz₃| ].
   constructor.
   inversion_clear H₁₂.
bbb.

intros ps₁ ps₂ ps₃ H₂₃.
unfold ps_add.
inversion H₂₃ as [k₂₁ k₂₂ nz₂₁ nz₂₂ Hss₂ Hvv₂ Hck₂| a b H₂ H₃]; subst.
 remember (nz_valnum ps₁) as v₁.
 remember (nz_valnum ps₂) as v₂.
 remember (nz_valnum ps₃) as v₃.
 symmetry in Heqv₁, Heqv₂, Heqv₃.
 destruct v₁ as [v₁| ]; [ idtac | assumption ].
 destruct v₂ as [v₂| ].
  destruct v₃ as [v₃| ]; [ idtac | discriminate Hvv₂ ].
  unfold ps_add_nz, cm_factor; simpl.
  rewrite Heqv₁, Heqv₂, Heqv₃; simpl.
  constructor 1 with (k₁ := k₂₁) (k₂ := k₂₂); unfold cm_factor; simpl.
   do 2 rewrite stretch_series_add_distr.
   do 4 rewrite stretch_pad_series_distr.
   do 4 rewrite <- stretch_stretch_series.
   do 4 rewrite Nat.mul_sub_distr_r.
   do 4 rewrite <- Z2Nat_inj_mul_pos_r.
   do 4 rewrite <- Z.mul_assoc; simpl.
   rewrite Hck₂.
   rewrite Pos.mul_comm in Hck₂; symmetry in Hck₂.
   rewrite Pos.mul_comm in Hck₂; symmetry in Hck₂.
   rewrite Hck₂.
   replace (k₂₁ * nz_comden ps₁)%positive with
    (nz_comden ps₁ * k₂₁)%positive by apply Pos.mul_comm.
   do 2 rewrite stretch_stretch_series.
   rewrite Hss₂.
   do 2 rewrite <- stretch_stretch_series.
   replace (nz_comden ps₁ * k₂₂)%positive with
    (k₂₂ * nz_comden ps₁)%positive by apply Pos.mul_comm.
   replace (v₂ * ' (nz_comden ps₁ * k₂₁))%Z with
    (v₃ * ' (k₂₂ * nz_comden ps₁))%Z .
    reflexivity.

    do 2 rewrite Pos2Z.inj_mul.
    do 2 rewrite Z.mul_assoc.
    symmetry; rewrite Z.mul_shuffle0.
    apply Z.mul_cancel_r; [ apply Zpos_ne_0 | idtac ].
    inversion Hvv₂; subst.
    reflexivity.

   rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
   rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
   simpl in Hvv₂.
   do 2 f_equal.
    do 2 rewrite <- Z.mul_assoc; simpl.
    rewrite Hck₂; reflexivity.

    rewrite Z.mul_shuffle0.
    injection Hvv₂; clear Hvv₂; intros Hvv₂; rewrite Hvv₂.
    rewrite Z.mul_shuffle0; reflexivity.

   rewrite <- Pos.mul_assoc, Hck₂, Pos.mul_assoc.
   reflexivity.

  destruct v₃ as [v₃| ]; [ discriminate Hvv₂ | reflexivity ].

 remember (nz_valnum ps₁) as v₁.
 remember (nz_valnum ps₂) as v₂.
 remember (nz_valnum ps₃) as v₃.
 symmetry in Heqv₁, Heqv₂, Heqv₃.
 destruct v₁ as [v₁| ]; [ idtac | assumption ].
 destruct v₂ as [v₂| ]; simpl.
  destruct H₂ as [H₂| H₂]; [ idtac | discriminate H₂ ].
  destruct v₃ as [v₃| ]; simpl.
   destruct H₃ as [H₃| H₃]; [ idtac | discriminate H₃ ].
   unfold build_ps; simpl.
   rewrite Heqv₁, Heqv₂, Heqv₃; simpl.
   Focus 1.
bbb.

intros ps₁ ps₃ ps₄ H.
inversion H as [k₂₁ k₂₂ nz₂₁ nz₂₂ Hss₂ Hvv₂ Hck₂| ]; subst.
 constructor 1 with (k₁ := k₂₁) (k₂ := k₂₂); unfold cm_factor; simpl.
  do 4 rewrite Z2Nat_inj_mul_pos_r.
  remember (nz_valnum nz₁) as v₁.
  remember (nz_comden nz₁) as c₁.
  remember (nz_comden nz₂₁) as c₂₁.
  remember (nz_comden nz₂₂) as c₂₂.
  remember (nz_valnum nz₂₁) as v₂₁.
  remember (nz_valnum nz₂₂) as v₂₂.
  do 2 rewrite stretch_series_add_distr.
  rewrite stretch_pad_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite stretch_pad_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite stretch_pad_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite stretch_pad_series_distr; [ idtac | apply Pos2Nat_ne_0 ].
  rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
  rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
  rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
  rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
-- à nettoyer
  rewrite Nat.mul_sub_distr_r.
  rewrite <- Nat.mul_assoc.
  rewrite <- Pos2Nat.inj_mul.
  rewrite Hck₂.
  rewrite Nat.mul_shuffle0.
  rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite Hvv₂.
  rewrite Pos2Z.inj_mul.
  rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite Z.mul_assoc.
  remember (v₁ * ' c₂₂ * ' k₂₂)%Z as vck eqn:Hvck .
  remember (v₂₂ * ' k₂₂ * ' c₁)%Z as vkc eqn:Hvkc .
  rewrite Nat.mul_sub_distr_r.
  do 4 rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite Z.mul_shuffle0.
  rewrite Hvv₂.
  rewrite <- Hvkc.
  rewrite <- Z.mul_assoc; simpl.
  rewrite Hck₂.
  rewrite Pos2Z.inj_mul.
  rewrite Z.mul_assoc.
  rewrite <- Hvck.
  do 2 rewrite Nat.mul_sub_distr_r.
  do 4 rewrite <- Z2Nat_inj_mul_pos_r.
  rewrite <- Hvck.
  rewrite Z.mul_shuffle0.
  rewrite <- Hvkc.
  do 4 rewrite <- Pos2Nat.inj_mul.
  rewrite Pos.mul_comm.
  rewrite Hck₂.
  rewrite Pos.mul_comm.
  rewrite series_add_comm.
  rewrite Pos2Nat.inj_mul.
  rewrite Nat.mul_comm.
  rewrite stretch_stretch_series; try apply Pos2Nat_ne_0.
  rewrite Hss₂.
  rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
  rewrite Nat.mul_comm.
  rewrite <- Pos2Nat.inj_mul.
  rewrite series_add_comm.
  reflexivity.

  rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
  rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
  rewrite <- Z.mul_assoc; simpl.
  rewrite Hck₂.
  rewrite Z.mul_shuffle0, Hvv₂.
  rewrite Pos2Z.inj_mul, Z.mul_assoc.
  rewrite Z.min_comm, Z.mul_shuffle0, Z.min_comm.
  reflexivity.

  do 2 rewrite <- Pos.mul_assoc.
  apply Pos.mul_cancel_l.
  assumption.

 reflexivity.
Qed.
*)

Theorem ps_mul_ident : ∀ ps, ps_mul fld ps_one ps ≈ ps.
Proof.
intros ps.
unfold ps_mul; simpl.
destruct ps as [nz| ]; [ idtac | reflexivity ].
unfold cm_factor; simpl.
rewrite Z.mul_1_r.
apply eq_non_zero_ps with (k₁ := xH) (k₂ := xH); try reflexivity; simpl.
rewrite stretch_series_1.
rewrite stretch_series_1 in |- * at 2.
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
rewrite stretch_series_1.
rewrite stretch_series_1 in |- * at 2.
constructor; simpl.
 intros i.
 remember
  (sum_mul_coeff fld 1 i
     (stretch_series fld (Pos.to_nat (nz_comden nz))
        {| terms := λ _ : nat, one fld; stop := 1 |})
     (stretch_series fld (Pos.to_nat 1) (nz_terms nz))) as x.
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
