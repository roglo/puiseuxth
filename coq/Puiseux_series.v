(* $Id: Puiseux_series.v,v 1.856 2013-10-16 15:19:32 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Misc.
Require Import Series.
Require Import Nbar.

Set Implicit Arguments.

Section Axioms.

Variable α : Type.
Variable fld : field α.
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).

(* [first_nonzero fld s n] returns the position of the first non null
   coefficient in the series [s], starting from the [n]th one (first
   one being 0). *)
Definition first_nonzero : ∀ α, field α → series α → nat → Nbar.
Admitted.

Axiom first_nonzero_iff : ∀ s c n,
  first_nonzero fld s c = n
  ↔ match n with
    | fin k =>
        (∀ i, (i < k)%nat → series_nth_fld fld (c + i) s ≍ zero fld) ∧
        series_nth_fld fld (c + k) s ≭ zero fld
    | ∞ =>
        (∀ i, series_nth_fld fld (c + i) s ≍ zero fld)
    end.

(* [shrink_factor fld s n] returns the maximal shrink factor [k] of the
   series [s] starting at position [n], i.e. there is a series [s'] which
   can be stretched by [stretch_series] (below) with a factor of [k] to
   give [s] back. *)
Definition shrink_factor : ∀ α, field α → series α → nat → positive.
Admitted.

Axiom shrink_factor_iff : ∀ s n k,
  shrink_factor fld s n = k
  ↔ match first_nonzero fld s (S n) with
    | fin _ =>
        (∀ i, i mod (Pos.to_nat k) ≠ O →
         series_nth_fld fld (n + i) s ≍ zero fld) ∧
        (∀ k', (Pos.to_nat k < k')%nat →
         ∃ i, i mod k' ≠ O ∧ series_nth_fld fld (n + i) s ≭ zero fld)
    | ∞ =>
        k = 1%positive
    end.

End Axioms.

Section fld.

Variable α : Type.
Variable fld : field α.
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).
Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "x ≤ y < z" :=
  (x <= y ∧ y < z)%nat (at level 70, y at next level) : nat_scope.

Definition stretch_series k s :=
  {| terms i :=
       if zerop (i mod Pos.to_nat k) then
         series_nth_fld fld (i / Pos.to_nat k) s
       else zero fld;
     stop :=
       stop s * fin (Pos.to_nat k) |}.

Definition series_shift n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n);
     stop := stop s + fin n |}.

Record nz_ps α := mknz
  { nz_terms : series α;
    nz_valnum : Z;
    nz_comden : positive }.

Inductive puiseux_series α :=
  | NonZero : nz_ps α → puiseux_series α
  | Zero : puiseux_series α.

Definition normalise_series n k (s : series α) :=
  {| terms i := terms s (n + i * Pos.to_nat k);
     stop := Nbar.div_sup (stop s - fin n) (fin (Pos.to_nat k)) |}.

Definition gcd_nz n k (nz : nz_ps α) :=
  Z.gcd (Z.gcd (nz_valnum nz + Z.of_nat n) (' nz_comden nz)) (' k).

Definition normalise_nz nz :=
  match first_nonzero fld (nz_terms nz) 0 with
  | fin n =>
      let k := shrink_factor fld (nz_terms nz) n in
      let g := gcd_nz n k nz in
      NonZero
        {| nz_terms := normalise_series n (Z.to_pos g) (nz_terms nz);
           nz_valnum := (nz_valnum nz + Z.of_nat n) / g;
           nz_comden := Z.to_pos (' nz_comden nz / g) |}
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

Definition nz_monom (c : α) pow :=
  {| nz_terms := {| terms i := c; stop := 1 |};
     nz_valnum := Qnum pow;
     nz_comden := Qden pow |}.

Definition ps_monom c pow := NonZero (nz_monom c pow).
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
with signature (eq_series fld) ==> eq ==> eq as first_nonzero_morph.
Proof.
intros s₁ s₂ Heq n.
remember (first_nonzero fld s₁ n) as n₁ eqn:Hn₁ .
remember (first_nonzero fld s₂ n) as n₂ eqn:Hn₂ .
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

Add Parametric Morphism α (fld : field α) : (shrink_factor fld)
with signature (eq_series fld) ==> eq ==> eq as shrink_morph.
Proof.
intros s₁ s₂ Heq n.
remember (shrink_factor fld s₂ n) as k eqn:Hk .
symmetry in Hk.
apply shrink_factor_iff in Hk.
apply shrink_factor_iff.
remember (first_nonzero fld s₁ (S n)) as m eqn:Hm .
symmetry in Hm.
rewrite Heq in Hm.
rewrite Hm in Hk.
destruct m as [m| ]; [ idtac | assumption ].
destruct Hk as (Hz, Hnz).
split.
 intros i Him.
 rewrite Heq.
 apply Hz; assumption.

 intros k₁ Hk₁.
 apply Hnz in Hk₁.
 destruct Hk₁ as (i, Hk₁).
 rewrite <- Heq in Hk₁.
 exists i; assumption.
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

Add Parametric Morphism α (fld : field α) : (series_shift fld) with 
signature eq ==> eq_series fld ==> eq_series fld as series_shift_morph.
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

Add Parametric Morphism α (fld : field α) : (@normalise_series α) with 
signature eq ==> eq ==> (eq_series fld) ==> (eq_series fld) as normalise_morph.
Proof.
intros n k ps₁ ps₂ Heq.
constructor; intros i.
inversion Heq; subst.
unfold normalise_series.
remember Nbar.div_sup as f; simpl; subst f.
do 2 rewrite Nbar.fold_sub.
pose proof (H (n + i * Pos.to_nat k)%nat) as Hi.
remember Nbar.div_sup as f.
unfold series_nth_fld in Hi |- *; simpl.
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

Lemma stretch_shift_series_distr : ∀ kp n s,
  stretch_series fld kp (series_shift fld n s) ≃
  series_shift fld (n * Pos.to_nat kp) (stretch_series fld kp s).
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

Lemma series_shift_shift : ∀ x y ps,
  series_shift fld x (series_shift fld y ps) ≃
  series_shift fld (x + y) ps.
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
  remember (first_nonzero fld (nz_terms nz₁) 0) as n₁ eqn:Hn₁ .
  remember (first_nonzero fld (nz_terms nz₂) 0) as n₂ eqn:Hn₂ .
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
  remember (first_nonzero fld (series_0 fld) 0) as n eqn:Hn .
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
 remember (first_nonzero fld (nz_terms nz₁) 0) as n₁ eqn:Hn₁ .
 remember (first_nonzero fld (nz_terms nz₂) 0) as n₂ eqn:Hn₂ .
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
aaa.
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

Theorem lt_first_nonzero : ∀ s c n,
  (fin n < first_nonzero fld s c)%Nbar
  → series_nth_fld fld (c + n) s ≍ zero fld.
Proof.
intros s c n Hn.
remember (first_nonzero fld s c) as v eqn:Hv .
symmetry in Hv.
apply first_nonzero_iff in Hv.
destruct v as [v| ]; [ idtac | apply Hv ].
destruct Hv as (Hvz, Hvnz).
apply Hvz, Nbar.fin_lt_mono; assumption.
Qed.

Theorem eq_first_nonzero : ∀ s c n,
  first_nonzero fld s c = fin n
  → series_nth_fld fld (c + n) s ≭ zero fld.
Proof.
intros s c n Hn.
apply first_nonzero_iff in Hn.
destruct Hn; assumption.
Qed.

Lemma series_shift_0 : ∀ s, series_shift fld 0 s ≃ s.
Proof.
intros s.
constructor; intros i.
unfold series_shift, series_nth_fld; simpl.
rewrite Nbar.add_0_r, Nat.sub_0_r; reflexivity.
Qed.

Lemma series_nth_shift_S : ∀ s n i,
  series_nth_fld fld i (series_shift fld n s) =
  series_nth_fld fld (S i) (series_shift fld (S n) s).
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

Lemma first_nonzero_shift_S : ∀ s c n,
  (c ≤ n)%nat
  → first_nonzero fld (series_shift fld (S n) s) c =
    NS (first_nonzero fld (series_shift fld n s) c).
Proof.
intros s c n Hcn.
remember (first_nonzero fld (series_shift fld n s) c) as u eqn:Hu .
remember (first_nonzero fld (series_shift fld (S n) s) c) as v eqn:Hv .
symmetry in Hu, Hv.
apply first_nonzero_iff in Hu.
apply first_nonzero_iff in Hv.
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
    unfold series_nth_fld in Hv; simpl in Hv.
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
  unfold series_nth_fld in Hv; simpl in Hv.
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

Theorem first_nonzero_shift : ∀ s n,
  first_nonzero fld (series_shift fld n s) 0 =
    (fin n + first_nonzero fld s 0)%Nbar.
Proof.
intros s n.
induction n.
 rewrite series_shift_0, Nbar.add_0_l; reflexivity.

 rewrite first_nonzero_shift_S; [ idtac | apply Nat.le_0_l ].
 rewrite IHn; simpl.
 destruct (first_nonzero fld s); reflexivity.
Qed.

(* à voir...
Lemma xxx : ∀ s,
  series_nth_fld fld 0 s ≍ zero fld
  → NS (first_nonzero fld s 1) = first_nonzero fld s 0.
Proof.
intros s Hz.
remember (first_nonzero fld s 1) as n eqn:Hn .
remember (first_nonzero fld s 0) as p eqn:Hp .
symmetry in Hn, Hp.
apply first_nonzero_iff in Hn.
apply first_nonzero_iff in Hp.
destruct n as [n| ].
 destruct Hn as (Hin, Hn).
 destruct p as [p| ]; simpl.
  destruct Hp as (Hip, Hp).
  apply Nbar.fin_inj_wd.
  simpl in Hin, Hn, Hp, Hip.
  destruct (lt_eq_lt_dec (S n) p) as [[H₁| H₁]| H₁].
   rewrite Hip in Hn; [ exfalso; apply Hn; reflexivity | assumption ].

   assumption.

   destruct (eq_nat_dec n p) as [H₂| H₂].
    subst p.
    destruct n as [| n].
     rewrite Hz in Hp; exfalso; apply Hp; reflexivity.

     rewrite Hin in Hp; [ idtac | apply Nat.lt_succ_diag_r ].
     exfalso; apply Hp; reflexivity.

    assert (p < n)%nat as H₃ by omega.
    destruct p as [| p].
     rewrite Hz in Hp; exfalso; apply Hp; reflexivity.
aaa.
*)

(* à voir...
Theorem first_nonzero_1_shift : ∀ s n,
  series_nth_fld fld 0 s ≍ zero fld
  → first_nonzero fld (series_shift fld n s) 1 =
      (fin n + first_nonzero fld s 1)%Nbar.
Proof.
intros s n Hz.
induction n.
 rewrite series_shift_0, Nbar.add_0_l; reflexivity.

 destruct (le_dec 1 n) as [H₁| H₁].
  rewrite first_nonzero_shift_S; [ idtac | assumption ].
  rewrite IHn; simpl.
  destruct (first_nonzero fld s); reflexivity.

  apply Nat.nle_gt in H₁.
  apply Nat.lt_1_r in H₁; subst n.
  simpl in IHn |- *.
  remember (first_nonzero fld s 1) as m eqn:Hm .
  symmetry in Hm.
  destruct m as [m| ].
aaa.
*)

Lemma shifted_in_stretched : ∀ s k i,
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

Lemma stretch_finite_series : ∀ s b k,
  (∀ i : nat, series_nth_fld fld (b + i) s ≍ zero fld)
  → ∀ i,
    series_nth_fld fld (b * Pos.to_nat k + i) (stretch_series fld k s)
    ≍ zero fld.
Proof.
intros s b k Hz i.
destruct (zerop (i mod Pos.to_nat k)) as [H₁| H₁].
 apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
 destruct H₁ as (c, H₁).
 subst i.
 rewrite Nat.mul_comm, <- Nat.mul_add_distr_l.
 rewrite series_nth_fld_mul_stretch.
 apply Hz.

 rewrite shifted_in_stretched; [ reflexivity | idtac ].
 rewrite Nat.add_comm.
 rewrite Nat.mod_add; [ assumption | apply Pos2Nat_ne_0 ].
Qed.

Lemma first_nonzero_stretch : ∀ s b k,
  first_nonzero fld (stretch_series fld k s) (b * Pos.to_nat k) =
    (fin (Pos.to_nat k) * first_nonzero fld s b)%Nbar.
Proof.
intros s b k.
remember (first_nonzero fld s b) as n eqn:Hn .
symmetry in Hn.
apply first_nonzero_iff in Hn.
apply first_nonzero_iff.
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
   rewrite series_nth_fld_mul_stretch.
   apply Hz.
   rewrite H₁ in Hin.
   rewrite Nat.mul_comm in Hin.
   apply Nat.mul_lt_mono_pos_r in Hin; [ assumption | apply Pos2Nat.is_pos ].

   rewrite shifted_in_stretched; [ reflexivity | idtac ].
   rewrite Nat.add_comm.
   rewrite Nat.mod_add; [ assumption | apply Pos2Nat_ne_0 ].

  rewrite <- Nat.mul_add_distr_r.
  rewrite Nat.mul_comm.
  rewrite series_nth_fld_mul_stretch.
  assumption.

 intros i.
 apply stretch_finite_series; assumption.
Qed.

Lemma first_nonzero_stretch_0 : ∀ s k,
  first_nonzero fld (stretch_series fld k s) 0 =
    (fin (Pos.to_nat k) * first_nonzero fld s 0)%Nbar.
Proof.
intros s k.
rewrite <- first_nonzero_stretch.
rewrite Nat.mul_0_l; reflexivity.
Qed.

(*
Lemma stretch_succ : ∀ s b k,
  first_nonzero fld (stretch_series fld k s) (S b * Pos.to_nat k) =
  first_nonzero fld (stretch_series fld k s) (S (b * Pos.to_nat k)).
Proof.
intros s b k.
remember (stretch_series fld k s) as t.
remember (first_nonzero fld t (S b * Pos.to_nat k)) as n eqn:Hn .
subst t.
symmetry in Hn |- *.
apply first_nonzero_iff in Hn.
apply first_nonzero_iff.
destruct n as [n| ].
 destruct Hn as (Hz, Hnz).
 split.
  intros i Hin.
  remember (Pos.to_nat k) as kn eqn:Hkn .
  symmetry in Hkn.
  destruct kn as [| kn]; [ exfalso; revert Hkn; apply Pos2Nat_ne_0 | idtac ].
  destruct kn as [| kn].
   rewrite Nat.mul_1_r in Hz |- *.
   apply Hz; assumption.

   rewrite <- Hkn in Hz, Hnz |- *.
   destruct (zerop i) as [H₁| H₁].
    subst i.
    rewrite Nat.add_0_r.
    rewrite shifted_in_stretched; [ reflexivity | idtac ].
    rewrite <- Nat.add_1_r, Nat.add_comm.
    rewrite Nat.mod_add; [ idtac | apply Pos2Nat_ne_0 ].
    rewrite Hkn.
    rewrite Nat.mod_1_l; [ apply Nat.lt_0_1 | idtac ].
    apply -> Nat.succ_lt_mono.
    apply Nat.lt_0_succ.

    destruct (lt_dec (S i) (Pos.to_nat k)) as [H₂| H₂].
     rewrite shifted_in_stretched; [ reflexivity | idtac ].
     rewrite Nat.add_succ_l, <- Nat.add_succ_r.
     rewrite Nat.add_comm.
     rewrite Nat.mod_add; [ idtac | apply Pos2Nat_ne_0 ].
     rewrite Nat.mod_small; [ idtac | assumption ].
     apply Nat.lt_0_succ.

     apply Nat.nlt_ge in H₂.
     rewrite Nat.add_succ_l, <- Nat.add_succ_r.
     remember (S i - Pos.to_nat k)%nat as j.
     assert (S i = Pos.to_nat k + j)%nat by fast_omega H₂ Heqj.
     replace (Pos.to_nat k) with (1 * Pos.to_nat k)%nat in H
      by apply Nat.mul_1_l.
     rewrite H.
     rewrite Nat.add_assoc.
     rewrite <- Nat.mul_add_distr_r.
     rewrite Nat.add_1_r.
     apply Hz.
     eapply le_lt_trans; [ idtac | eassumption ].
     apply Nat.succ_le_mono.
     rewrite H.
     rewrite Nat.mul_1_l.
     rewrite Hkn.
     rewrite Nat.add_succ_l, <- Nat.add_succ_r.
     apply le_plus_r.
aaa.
*)

Lemma series_nth_add_shift : ∀ s i n,
  series_nth_fld fld (i + n) (series_shift fld n s) ≍
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

Lemma first_nonzero_shift_add : ∀ s m n,
  first_nonzero fld (series_shift fld m s) (m + n) = first_nonzero fld s n.
Proof.
intros s m n.
remember (first_nonzero fld s n) as v eqn:Hv .
symmetry in Hv.
apply first_nonzero_iff in Hv.
apply first_nonzero_iff.
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

Lemma shrink_factor_shift : ∀ n s b,
  shrink_factor fld (series_shift fld n s) (b + n) =
  shrink_factor fld s b.
Proof.
intros n s b.
remember (shrink_factor fld s b) as k eqn:Hk .
symmetry in Hk.
apply shrink_factor_iff in Hk.
apply shrink_factor_iff.
rewrite <- Nat.add_succ_l.
rewrite Nat.add_comm.
rewrite first_nonzero_shift_add.
remember (first_nonzero fld s (S b)) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; [ simpl | assumption ].
destruct Hk as (Hz, Hnz).
split.
 intros i Him.
 rewrite Nat.add_shuffle0.
 rewrite series_nth_add_shift.
 apply Hz; assumption.

 intros k₁ Hk₁.
 apply Hnz in Hk₁.
 destruct Hk₁ as (i, Hk₁).
 rewrite <- series_nth_add_shift with (n := n) in Hk₁.
 rewrite Nat.add_shuffle0 in Hk₁.
 exists i; assumption.
Qed.

(* mouais... faut voir...
Lemma shrink_factor_stretch : ∀ s b k,
  first_nonzero fld s 0 = fin b
  → first_nonzero fld s (S b) ≠ ∞
    → shrink_factor fld (stretch_series fld k s) (b * Pos.to_nat k) =
      (k * shrink_factor fld s b)%positive.
Proof.
intros s b k Hb Hsb.
remember (Pos.to_nat k) as kn eqn:Hkn .
symmetry in Hkn.
destruct kn as [| kn].
 exfalso; revert Hkn; apply Pos2Nat_ne_0.

 destruct kn as [| kn].
  rewrite Nat.mul_1_r.
  replace 1%nat with (Pos.to_nat xH) in Hkn ; [ idtac | reflexivity ].
  apply Pos2Nat.inj in Hkn.
  subst k.
  rewrite stretch_series_1, Pos.mul_1_l.
  reflexivity.

  rewrite <- Hkn.
  remember (shrink_factor fld s b) as k₁ eqn:Hk₁ .
  remember (stretch_series fld k s) as t.
  remember (shrink_factor fld t (b * Pos.to_nat k)) as k₂ eqn:Hk₂ .
  subst t.
  symmetry in Hk₁, Hk₂.
  apply shrink_factor_iff in Hk₁.
  apply shrink_factor_iff in Hk₂.
  remember (first_nonzero fld s (S b)) as n₁ eqn:Hn₁ .
  remember (stretch_series fld k s) as t.
  remember (first_nonzero fld t (S (b * Pos.to_nat k))) as n₂ eqn:Hn₂ .
  subst t.
  symmetry in Hn₁, Hn₂.
  destruct n₁ as [n₁| ]; [ idtac | exfalso; apply Hsb; reflexivity ].
  destruct n₂ as [n₂| ].
   Focus 2.
   subst k₂.
   apply first_nonzero_iff in Hn₁.
   apply first_nonzero_iff in Hn₂.
   destruct Hn₁ as (Hz₁, Hnz₁).
   rewrite <- series_nth_fld_mul_stretch with (k := k) in Hnz₁.
   rewrite Nat.mul_add_distr_l in Hnz₁.
   rewrite Nat.mul_comm in Hnz₁.
   simpl in Hnz₁.
   rewrite <- Nat.add_assoc, Nat.add_comm in Hnz₁.
   rewrite Hkn in Hnz₁.
   rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hnz₁.
   rewrite <- Nat.add_succ_l in Hnz₁.
   rewrite <- Nat.add_assoc in Hnz₁.
   rewrite <- Hkn in Hnz₁.
   rewrite Hn₂ in Hnz₁.
   exfalso; apply Hnz₁; reflexivity.

   destruct Hk₁ as (Hz₁, Hnz₁).
   destruct Hk₂ as (Hz₂, Hnz₂).
   destruct (Pos.eq_dec k₂ (k * k₁)) as [H₁| H₁]; [ assumption | exfalso ].
   destruct (lt_dec (Pos.to_nat k₂) (Pos.to_nat (k * k₁))) as [H₂| H₂].
    apply Hnz₂ in H₂.
    destruct H₂ as (i, (Him, Hin)).
    destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂].
     apply Nat.mod_divides in H₂; [ idtac | apply Pos2Nat_ne_0 ].
     destruct H₂ as (c, Hi); subst i.
     rewrite Nat.mul_comm, <- Nat.mul_add_distr_l in Hin.
     rewrite series_nth_fld_mul_stretch in Hin.
     rewrite Pos2Nat.inj_mul in Him.
     rewrite Nat.mul_mod_distr_l in Him; try apply Pos2Nat_ne_0.
     apply Nat.neq_mul_0 in Him.
     destruct Him as (_, Him).
     apply Hin, Hz₁; assumption.

     apply Hin.
     rewrite shifted_in_stretched; [ reflexivity | idtac ].
     rewrite Nat.add_comm.
     rewrite Nat.mod_add; [ assumption | apply Pos2Nat_ne_0 ].

    apply Nat.nlt_ge in H₂.
    rewrite Pos2Nat.inj_mul in H₂.
    apply le_neq_lt in H₂.
     assert (Pos.to_nat k₁ < Pos.to_nat k₂)%nat as H₃.
      eapply Nat.le_lt_trans; [ idtac | eassumption ].
      rewrite <- Pos2Nat.inj_mul.
      apply Pos2Nat.inj_le.
      rewrite <- Pos.mul_1_l in |- * at 1.
      apply Pos.mul_le_mono_r.
      apply Pos.le_1_l.

      assert (n₂ = Pos.to_nat k * n₁)%nat.
       destruct (lt_eq_lt_dec n₂ (Pos.to_nat k * n₁)) as [[H₄| H₄]| H₄].
        apply first_nonzero_iff in Hn₂.
        apply first_nonzero_iff in Hn₁.
        destruct (zerop (n₂ mod Pos.to_nat k)) as [H₅| H₅].
         apply Nat.mod_divides in H₅.
          destruct H₅ as (c, H₅).
          subst n₂.
          apply Nat.mul_lt_mono_pos_l in H₄.
           apply Hn₁ in H₄.
           destruct Hn₂ as (Hz, Hnz).
           rewrite shifted_in_stretched in Hnz.
            exfalso; apply Hnz; reflexivity.

            rewrite <- Nat.add_1_r.
            rewrite Nat.add_shuffle0.
            rewrite Nat.mul_comm, <- Nat.mul_add_distr_l.
            rewrite Nat.add_comm.
            rewrite Nat.mul_comm.
            rewrite Nat.mod_add.
             rewrite Hkn.
             rewrite Nat.mod_small.
              apply Nat.lt_0_1.

              apply Nat.lt_succ_r.
              apply -> Nat.succ_le_mono.
              apply Nat.le_0_l.

             apply Pos2Nat_ne_0.

           apply Pos2Nat.is_pos.

          apply Pos2Nat_ne_0.

         Focus 1.
aaa.
*)

End fld₂.
