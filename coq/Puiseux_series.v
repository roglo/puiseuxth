(* $Id: Puiseux_series.v,v 2.14 2013-11-04 12:25:28 deraugla Exp $ *)

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
Definition first_nonzero_prop s c n :=
  match n with
  | fin k =>
      (∀ i, (i < k)%nat → series_nth_fld fld (c + i) s ≍ zero fld) ∧
      series_nth_fld fld (c + k) s ≭ zero fld
  | ∞ =>
      (∀ i, series_nth_fld fld (c + i) s ≍ zero fld)
  end.

Definition first_nonzero : ∀ α, field α → series α → nat → Nbar.
Admitted.

Axiom first_nonzero_iff : ∀ s c n,
  first_nonzero fld s c = n ↔ first_nonzero_prop s c n.

(* [stretching_factor fld s n] returns the maximal stretching factor of
   the series [s] starting at position [n], i.e. there is a series [s']
   which can be stretched by [stretch_series] (below) with this factor
   to give [s] back. *)
Definition stretching_factor : ∀ α, field α → series α → nat → positive.
Admitted.

Fixpoint nth_nonzero_interval s n b :=
  match first_nonzero fld s (S b) with
  | fin p =>
      match n with
      | O => S p
      | S n₁ => nth_nonzero_interval s n₁ (S b + p)%nat
      end
  | ∞ => O
  end.

Definition stretching_factor_gcd_prop s n k :=
  (∀ cnt, nth_nonzero_interval s cnt n mod k = O) ∧
  (∀ k', (k < k')%nat → ∃ cnt, nth_nonzero_interval s cnt n mod k' ≠ O).

Axiom stretching_factor_iff : ∀ s n k,
  stretching_factor fld s n = k ↔
  stretching_factor_gcd_prop s n (Pos.to_nat k).

End Axioms.

Section fld.

Variable α : Type.
Variable fld : field α.
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).
Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "x ≤ y < z" :=
  (x <= y ∧ y < z)%nat (at level 70, y at next level) : nat_scope.

Definition series_stretch k s :=
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
  match first_nonzero fld (nz_terms nz) 0 with
  | fin n =>
      let k := stretching_factor fld (nz_terms nz) n in
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

Lemma series_stretch_1 : ∀ s, series_stretch 1 s ≃ s.
Proof.
intros s.
unfold series_stretch; simpl.
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

(*
Add Parametric Morphism α (fld : field α) : (stretching_factor_lim fld)
  with signature eq ==> (eq_series fld) ==> eq ==> eq
  as stretching_factor_lim_morph.
Proof.
intros cnt s₁ s₂ Heq n.
revert n.
induction cnt; intros; [ reflexivity | simpl ].
rewrite Heq.
remember (first_nonzero fld s₂ (S n)) as p eqn:Hp .
symmetry in Hp.
destruct p as [p| ]; [ idtac | reflexivity ].
rewrite IHcnt; reflexivity.
Qed.
*)

Add Parametric Morphism α (fld : field α) : (nth_nonzero_interval fld)
  with signature (eq_series fld) ==> eq ==> eq ==> eq
  as nth_nonzero_interval_morph.
Proof.
intros s₁ s₂ Heq c n.
revert n.
induction c; intros; simpl; rewrite Heq; [ reflexivity | idtac ].
destruct (first_nonzero fld s₂ (S n)); [ apply IHc | reflexivity ].
Qed.

Add Parametric Morphism α (fld : field α) : (stretching_factor fld)
with signature (eq_series fld) ==> eq ==> eq as stretching_factor_morph.
Proof.
intros s₁ s₂ Heq n.
remember (stretching_factor fld s₂ n) as k eqn:Hk .
symmetry in Hk.
apply stretching_factor_iff in Hk.
apply stretching_factor_iff.
unfold stretching_factor_gcd_prop in Hk |- *.
destruct Hk as (Hz, Hnz).
split.
 intros cnt.
 rewrite Heq; apply Hz.

 intros k₁ Hk₁.
 apply Hnz in Hk₁.
 destruct Hk₁ as (cnt, Hcnt).
 exists cnt; rewrite Heq; assumption.
Qed.

Add Parametric Morphism α (fld : field α) : (series_stretch fld) with 
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
unfold series_shrink, series_left_shift.
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

Lemma stretch_series_stretch : ∀ a b s,
  series_stretch fld (a * b) s ≃
  series_stretch fld a (series_stretch fld b s).
Proof.
intros ap bp s.
unfold series_stretch; simpl.
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

Lemma series_stretch_series_0 : ∀ k,
  series_stretch fld k (series_0 fld) ≃ series_0 fld.
Proof.
intros k.
constructor; intros i.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin i) 0); [ idtac | reflexivity ].
destruct (zerop (i mod Pos.to_nat k)); [ idtac | reflexivity ].
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin (i / Pos.to_nat k)) 0); reflexivity.
Qed.

Lemma series_stretch_0_if : ∀ k s,
  series_stretch fld k s ≃ series_0 fld
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
  series_stretch fld kp (series_shift fld n s) ≃
  series_shift fld (n * Pos.to_nat kp) (series_stretch fld kp s).
Proof.
intros kp n s.
constructor; intros i.
unfold series_stretch, series_nth_fld; simpl.
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
  → series_nth_fld fld i (series_stretch fld k s) = zero fld.
Proof.
intros s k i Hi.
unfold series_nth_fld; simpl.
unfold series_nth_fld; simpl.
destruct (zerop (i mod Pos.to_nat k)) as [Hz| Hnz].
 exfalso; revert Hi; rewrite Hz; apply Nat.lt_irrefl.

 destruct (Nbar.lt_dec (fin i) (stop s * fin (Pos.to_nat k))); reflexivity.
Qed.

Lemma series_nth_fld_mul_stretch : ∀ s k i,
  series_nth_fld fld (Pos.to_nat k * i) (series_stretch fld k s) =
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
  → ∀ n k, series_nth_fld fld n (series_stretch fld k s) ≍ zero fld.
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
  (∀ i : nat, series_nth_fld fld i (series_stretch fld k s) ≍ zero fld)
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
    series_nth_fld fld (b * Pos.to_nat k + i) (series_stretch fld k s)
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
  first_nonzero fld (series_stretch fld k s) (b * Pos.to_nat k) =
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
  first_nonzero fld (series_stretch fld k s) 0 =
    (fin (Pos.to_nat k) * first_nonzero fld s 0)%Nbar.
Proof.
intros s k.
rewrite <- first_nonzero_stretch.
rewrite Nat.mul_0_l; reflexivity.
Qed.

(*
Lemma stretch_succ : ∀ s b k,
  first_nonzero fld (series_stretch fld k s) (S b * Pos.to_nat k) =
  first_nonzero fld (series_stretch fld k s) (S (b * Pos.to_nat k)).
Proof.
intros s b k.
remember (series_stretch fld k s) as t.
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

(*
Lemma stretching_factor_lim_shift : ∀ cnt s n b,
  stretching_factor_lim fld cnt (series_shift fld n s) (b + n) =
  stretching_factor_lim fld cnt s b.
Proof.
intros cnt s n b.
revert s n b.
induction cnt; intros; [ reflexivity | simpl ].
rewrite <- Nat.add_succ_l, Nat.add_comm.
rewrite first_nonzero_shift_add.
remember (first_nonzero fld s (S b)) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ]; [ idtac | reflexivity ].
do 2 rewrite divmod_mod.
do 2 f_equal.
rewrite Nat.add_shuffle0.
rewrite <- Nat.add_succ_l.
apply IHcnt.
Qed.
*)

Lemma nth_nonzero_interval_shift : ∀ s cnt n b,
  nth_nonzero_interval fld (series_shift fld n s) cnt (b + n) =
  nth_nonzero_interval fld s cnt b.
Proof.
intros s cnt n b.
revert b.
induction cnt; intros; simpl.
 rewrite <- Nat.add_succ_l, Nat.add_comm.
 rewrite first_nonzero_shift_add.
 destruct (first_nonzero fld s (S b)); reflexivity.

 rewrite <- Nat.add_succ_l, Nat.add_comm.
 rewrite first_nonzero_shift_add.
 remember (first_nonzero fld s (S b)) as m eqn:Hm .
 symmetry in Hm.
 destruct m as [m| ]; [ idtac | reflexivity ].
 rewrite Nat.add_shuffle0.
 rewrite <- Nat.add_succ_l.
 apply IHcnt.
Qed.

Lemma stretching_factor_shift : ∀ n s b,
  stretching_factor fld (series_shift fld n s) (b + n) =
  stretching_factor fld s b.
Proof.
intros n s b.
remember (stretching_factor fld s b) as k eqn:Hk .
symmetry in Hk.
apply stretching_factor_iff in Hk.
apply stretching_factor_iff.
unfold stretching_factor_gcd_prop in Hk |- *.
destruct Hk as (Hz, Hnz).
split.
 intros cnt.
 rewrite nth_nonzero_interval_shift.
 apply Hz.

 intros k₁ Hk₁.
 apply Hnz in Hk₁.
 destruct Hk₁ as (cnt, H).
 exists cnt.
 rewrite nth_nonzero_interval_shift.
 assumption.
Qed.

Lemma first_nonzero_succ : ∀ s n,
  first_nonzero fld s (S n) =
  match first_nonzero fld s n with
  | fin O => first_nonzero fld s (S n)
  | fin (S m) => fin m
  | ∞ => ∞
  end.
Proof.
intros s n.
remember (first_nonzero fld s n) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ].
 destruct m as [| m]; [ reflexivity | idtac ].
 apply first_nonzero_iff in Hm.
 apply first_nonzero_iff.
 destruct Hm as (Hz, Hnz).
 split.
  intros i Him.
  rewrite Nat.add_succ_l, <- Nat.add_succ_r.
  apply Hz.
  apply -> Nat.succ_lt_mono; assumption.

  rewrite Nat.add_succ_l, <- Nat.add_succ_r.
  assumption.

 apply first_nonzero_iff in Hm.
 apply first_nonzero_iff.
 intros i.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hm.
Qed.

Lemma first_nonzero_stretch_succ : ∀ s n p k,
  first_nonzero fld s (S n) = fin p
  → first_nonzero fld (series_stretch fld k s) (S (n * Pos.to_nat k)) =
      fin (S p * Pos.to_nat k - 1).
Proof.
(* à nettoyer *)
intros s n p k Hp.
remember (series_stretch fld k s) as s₁ eqn:Hs₁ .
remember (first_nonzero fld s₁ (S (n * Pos.to_nat k))) as q eqn:Hq .
symmetry in Hq.
apply first_nonzero_iff in Hq.
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
  rewrite series_nth_fld_mul_stretch in Hnzq.
  apply first_nonzero_iff in Hp.
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
      rewrite series_nth_fld_mul_stretch in H.
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
 apply first_nonzero_iff in Hp.
 destruct Hp as (Hzp, Hnzp).
 rewrite <- series_nth_fld_mul_stretch with (k := k) in Hnzp.
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

Lemma first_nonzero_stretch_succ_inf : ∀ s n k,
  first_nonzero fld s (S n) = ∞
  → first_nonzero fld (series_stretch fld k s) (S (n * Pos.to_nat k)) = ∞.
Proof.
intros s n k Hp.
apply first_nonzero_iff in Hp.
apply first_nonzero_iff.
unfold first_nonzero_prop in Hp |- *.
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

Lemma series_shrink_stretch : ∀ s k,
  series_shrink k (series_stretch fld k s) ≃ s.
Proof.
intros s k.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.fold_sub.
rewrite Nbar.fold_div.
rewrite Nbar.fold_div_sup.
rewrite Nbar.div_sup_mul.
 rewrite Nat.mod_mul; simpl.
  rewrite Nat.div_mul; simpl.
   unfold series_nth_fld.
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
        match first_nonzero fld s (S b) with
        | fin m => S (rank_of_nonzero_after_from s n₁ i (S b + m)%nat)
        | ∞ => O
        end
      else O
  end.

Fixpoint index_of_nonzero_before_from s n i b last_b :=
  match n with
  | O => b
  | S n₁ =>
      if lt_dec b i then
        match first_nonzero fld s (S b) with
        | fin m => index_of_nonzero_before_from s n₁ i (S b + m)%nat b
        | ∞ => b
        end
      else last_b
  end.

Definition rank_of_nonzero_before s i :=
  pred (rank_of_nonzero_after_from s (S i) i 0).

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
 destruct (first_nonzero fld s (S b₁)) as [len₁| ]; [ idtac | assumption ].
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
 destruct (first_nonzero fld s (S b)) as [len₁| ]; [ idtac | assumption ].
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
       → first_nonzero fld s (S n) = fin len
         → first_nonzero fld s (S b) = fin len₁
           → index_of_nonzero_before_from s c i (S (b + len₁)) b = n
             → i ≤ S n + len)%nat.
Proof.
intros k c m s b i n len len₁ Hic Hb Hbi Hlen Hlen₁ Hn.
revert k m b len₁ Hic Hb Hbi Hlen₁ Hn.
induction c; intros; simpl in Hn; [ exfalso; omega | idtac ].
destruct (lt_dec (S (b + len₁)) i) as [H₁| H₁].
 remember (first_nonzero fld s (S (S (b + len₁)))) as len₂ eqn:Hlen₂ .
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
         → first_nonzero fld s (S n) = fin len
           → i ≤ S n + len)%nat.
Proof.
intros s c i b n last_b len Hbi Hli Hic Hn Hlen.
destruct c; simpl in Hn.
 apply Nat.nlt_0_r in Hic; contradiction.

 destruct (lt_dec b i) as [H₁| H₁]; [ idtac | exfalso; omega ].
 remember (first_nonzero fld s (S b)) as len₁ eqn:Hlen₁ .
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
     → first_nonzero fld s (S n) = fin len
       → i ≤ S n + len)%nat.
Proof.
intros s i n len Hi Hn Hlen.
eapply index_of_nonzero_before_from_right_bound; try eassumption.
apply Nat.lt_succ_r; reflexivity.
Qed.

(**)
Lemma vvv : ∀ s i c b k,
  (i < c)%nat
  → nth_nonzero_interval fld s
     (pred (rank_of_nonzero_after_from s c (b + i) b)) b
     mod Pos.to_nat k = O
    → i mod Pos.to_nat k ≠ O
      → series_nth_fld fld (b + i) s ≍ zero fld.
Proof.
intros s i c b k Hic Hs Hm.
remember (pred (rank_of_nonzero_after_from s c (b + i) b)) as n eqn:Hn .
symmetry in Hn.
destruct c; [ exfalso; omega | simpl in Hn ].
destruct i.
 rewrite Nat.mod_0_l in Hm; [ idtac | apply Pos2Nat_ne_0 ].
 exfalso; apply Hm; reflexivity.

 apply Nat.succ_lt_mono in Hic.
 destruct (lt_dec b (b + S i)) as [H₁| H₁]; [ idtac | exfalso; omega ].
 clear H₁.
 remember (first_nonzero fld s (S b)) as len eqn:Hlen .
 symmetry in Hlen.
 destruct len as [len| ].
  Focus 2.
  rewrite Nat.add_succ_r.
  apply first_nonzero_iff in Hlen; simpl in Hlen.
  apply Hlen.

  simpl in Hn.
  (* faire l'induction sur c à partir de là...
     faire un lemme plus général pour rank_of_nonzero_after_from *)
  (* mouais... *)
bbb.

intros s i c b k Hic Hs Hm.
remember (index_of_nonzero_before s (b + i)) as n eqn:Hn .
remember (first_nonzero fld s (S n)) as len eqn:Hlen .
symmetry in Hlen.
destruct len as [len| ].
 assert (n < b + i)%nat as Hnbi.
  rewrite Hn.
  apply index_of_nonzero_before_lt.
  destruct i; [ idtac | fast_omega  ].
  rewrite Nat.mod_0_l in Hm; [ idtac | apply Pos2Nat_ne_0 ].
  exfalso; apply Hm; reflexivity.

  assert (b + i ≤ S n + len)%nat as Hbin.
   symmetry in Hn.
   eapply index_of_nonzero_before_right_bound; try eassumption.
   destruct i.
    rewrite Nat.mod_0_l in Hm; [ idtac | apply Pos2Nat_ne_0 ].
    exfalso; apply Hm; reflexivity.

    rewrite Nat.add_succ_r; simpl.
    apply Nat.lt_0_succ.

   apply first_nonzero_iff in Hlen; simpl in Hlen.
   destruct Hlen as (Hz, Hnz).
   destruct (eq_nat_dec (b + i) (S n + len)) as [H₁| H₁].
    Focus 2.
    replace (b + i)%nat with (S (n + (b + i - S n)))%nat by omega.
    apply Hz.
    fast_omega Hnbi Hbin H₁.

    clear Hbin Hnz Hnbi.
    remember (pred (rank_of_nonzero_after_from s c (b + i) b)) as n₁ eqn:Hn₁ .
    assert (nth_nonzero_interval fld s n₁ b = len).
     clear Hz H₁.
     clear Hm.
     clear k Hs.
     revert i n n₁ Hic Hn₁ Hn.
     induction c; intros; [ exfalso; omega | idtac ].
     simpl in Hn₁.
     destruct (lt_dec b (b + i)) as [H₁| H₁].
      remember (first_nonzero fld s (S b)) as len₁ eqn:Hlen₁ .
      unfold index_of_nonzero_before in Hn.
      destruct len₁ as [len₁| ].
       destruct c.
        simpl in Hn₁.
        exfalso; fast_omega Hic H₁.

        simpl in Hn₁.
bbb.

J'avais essayé de trouver la règle d'induction, là, mais ça a l'air
de se compliquer...

    destruct c; [ exfalso; fast_omega Hic | idtac ].
    simpl in Hs.
    destruct (lt_dec b (b + i)) as [H₂| H₂].
     Focus 2.
     apply Nat.nlt_ge in H₂.
     apply Nat.le_add_le_sub_l in H₂.
     rewrite Nat.sub_diag in H₂.
     apply Nat.le_0_r in H₂; subst i.
     rewrite Nat.mod_0_l in Hm; [ idtac | apply Pos2Nat_ne_0 ].
     exfalso; apply Hm; reflexivity.

     remember (first_nonzero fld s (S b)) as len₁ eqn:Hlen₁ .
     symmetry in Hlen₁.
     destruct len₁ as [len₁| ].
      Focus 2.
      apply first_nonzero_iff in Hlen₁; simpl in Hlen₁.
      destruct i; [ exfalso; fast_omega H₂ | idtac ].
      rewrite Nat.add_succ_r.
      apply Hlen₁.

      destruct c; [ exfalso; fast_omega Hic H₂ | idtac ].
      simpl in Hs.
      destruct (lt_dec (S (b + len₁)) (b + i)) as [H₃| H₃].
       Focus 2.
       apply Nat.nlt_ge in H₃.
       simpl in Hs.
       rewrite Hlen₁ in Hs.
       rewrite <- Nat.add_succ_r in H₃.
       apply Nat.add_le_mono_l in H₃.
       apply first_nonzero_iff in Hlen₁; simpl in Hlen₁.
       destruct Hlen₁ as (Hz₁, Hnz₁).
       destruct i; [ exfalso; fast_omega H₂ | idtac ].
       destruct (eq_nat_dec i len₁) as [H₄| H₄].
        subst i.
        rewrite Hs in Hm; exfalso; apply Hm; reflexivity.

        assert (i < len₁)%nat as H₅ by fast_omega H₃ H₄.
        apply Hz₁ in H₅.
        rewrite Nat.add_succ_r; assumption.

       remember (first_nonzero fld s (S (S (b + len₁)))) as len₂ eqn:Hlen₂ .
       symmetry in Hlen₂.
       destruct len₂ as [len₂| ].
        Focus 2.
        apply first_nonzero_iff in Hlen₂; simpl in Hlen₂.
        simpl in Hs.
        rewrite Hlen₁ in Hs.
        rewrite <- Nat.add_succ_r in H₃.
        replace (b + i)%nat with (S (S (b + len₁ + (i - S (S len₁)))))%nat
         by omega.
        apply Hlen₂.

        destruct c; [ exfalso; fast_omega Hic H₃ | idtac ].
        simpl in Hs.
        rewrite Hlen₁ in Hs.
        destruct (lt_dec (S (S (b + len₁ + len₂))) (b + i)) as [H₄| H₄].
         Focus 2.
         apply Nat.nlt_ge in H₄.
         simpl in Hs.
         rewrite Hlen₂ in Hs.
         rewrite <- Nat.add_succ_r in H₄.
         rewrite <- Nat.add_succ_r in H₄.
         rewrite <- Nat.add_assoc in H₄.
         apply Nat.add_le_mono_l in H₄.
         apply first_nonzero_iff in Hlen₂; simpl in Hlen₂.
         destruct Hlen₂ as (Hz₁, Hnz₁).
         destruct i; [ exfalso; fast_omega H₂ | idtac ].
         destruct (eq_nat_dec i len₂) as [H₅| H₅].
          subst i.
          rewrite Hs in Hm; exfalso; apply Hm; reflexivity.

bbb.

intros s i c b k Hs Hm.
revert b c Hs Hm.
induction i; intros.
 rewrite Nat.add_0_r in Hm |- *.
 remember (pred (rank_of_nonzero_after_from s c 1 b)) as x eqn:Hx .
 symmetry in Hx.
 replace x with 0%nat in Hs .
  simpl in Hs.
  remember (first_nonzero fld s (S b)) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ].
   apply first_nonzero_iff in Hn.
   simpl in Hn.
   destruct n.
    remember (Pos.to_nat k) as kn eqn:Hkn .
    symmetry in Hkn.
    destruct kn as [| kn].
     exfalso; revert Hkn; apply Pos2Nat_ne_0.

     destruct kn as [| kn].
      rewrite Nat.mod_1_r in Hm.
      exfalso; apply Hm; reflexivity.

      rewrite Nat.mod_1_l in Hs; [ discriminate Hs | fast_omega  ].

    replace b with (b + 0)%nat by auto.
    apply Hn; apply Nat.lt_0_succ.

   apply first_nonzero_iff in Hn; simpl in Hn.
   replace b with (b + 0)%nat by auto.
   apply Hn.

  destruct c; [ assumption | simpl in Hx ].
  destruct (lt_dec b 1) as [H₁| H₁]; [ idtac | assumption ].
  apply Nat.lt_1_r in H₁; subst b.
  remember (first_nonzero fld s 1) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ]; [ idtac | assumption ].
  destruct c; assumption.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hm.

bbb.

 simpl in Hs.
 destruct (lt_dec b c) as [H₁| H₁]; simpl in Hs.
  remember (first_nonzero fld s (S b)) as n eqn:Hn .
  symmetry in Hn.
  destruct n as [n| ].
   apply first_nonzero_iff in Hn.
   simpl in Hn.
   simpl in Hs.
   destruct n.
    remember (Pos.to_nat k) as kn eqn:Hkn .
    symmetry in Hkn.
    destruct kn as [| kn].
     exfalso; revert Hkn; apply Pos2Nat_ne_0.

     destruct kn as [| kn].
      rewrite Nat.mod_1_r in Hm.
      exfalso; apply Hm; reflexivity.

      rewrite Nat.add_0_r in Hs.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l.
      rewrite Nat.add_succ_r in Hm.
      apply IHi with (c := c); [ idtac | assumption ].
      remember (S kn) as skn; simpl.
      rewrite divmod_mod; subst skn.
      remember (S kn) as skn; simpl.
      rewrite divmod_mod.
      destruct c; simpl.
       rewrite divmod_mod.
bbb.
*)

Fixpoint sigma_aux b len f :=
  match len with
  | O => f b
  | S len₁ => (f b + sigma_aux (S b) len₁ f)%nat
  end.

Definition sigma b e f := sigma_aux b (e - b) f.

(*
Notation "'Σ' ( i = b , e ) f" := (sigma b e (λ i, f))
  (at level 0, i at level 0, b at level 0, e at level 0, f at level 10,
   format "'Σ' ( i = b , e ) f").

Lemma nth_nonzero_interval_eq : ∀ s n b,
  nth_nonzero_interval fld s (S n) b =
  nth_nonzero_interval fld s 0
     (b + Σ (i = 0,n) (nth_nonzero_interval fld s i b)).
Proof.
bbb.
*)

Lemma sigma_aux_fin_succ : ∀ s b n l len,
  first_nonzero fld s (S b) = fin len
  → sigma_aux (S n) l (λ i : nat, nth_nonzero_interval fld s i b) =
    sigma_aux n l (λ i : nat, nth_nonzero_interval fld s i (S (b + len))).
Proof.
intros s b n l len H.
revert n.
induction l; intros.
 simpl; rewrite H; reflexivity.

 simpl; rewrite H; f_equal; apply IHl.
Qed.

Lemma sigma_aux_inf_succ : ∀ s b n l,
  first_nonzero fld s (S b) = ∞
  → sigma_aux (S n) l (λ i : nat, nth_nonzero_interval fld s i b) =
    sigma_aux n l (λ i : nat, nth_nonzero_interval fld s i b).
Proof.
intros s b n l H.
revert n.
induction l; intros.
 simpl; rewrite H.
 destruct n; simpl; rewrite H; reflexivity.

 simpl; rewrite H, IHl; f_equal.
 destruct n; simpl; rewrite H; reflexivity.
Qed.

Lemma nth_nonzero_interval_succ : ∀ s n b,
  nth_nonzero_interval fld s (S n) b =
  nth_nonzero_interval fld s n (b + nth_nonzero_interval fld s 0 b).
Proof.
intros s n b.
destruct n; simpl.
 remember (first_nonzero fld s (S b)) as len eqn:Hlen .
 symmetry in Hlen.
 destruct len as [len| ].
  rewrite Nat.add_succ_r; reflexivity.

  rewrite Nat.add_0_r, Hlen; reflexivity.

 remember (first_nonzero fld s (S b)) as len eqn:Hlen .
 symmetry in Hlen.
 destruct len as [len| ].
  rewrite Nat.add_succ_r; reflexivity.

  rewrite Nat.add_0_r, Hlen; reflexivity.
Qed.

Lemma nth_nonzero_interval_succ_sum : ∀ s n b,
  nth_nonzero_interval fld s (S n) b =
  nth_nonzero_interval fld s 0
    (b + sigma 0 n (λ i, nth_nonzero_interval fld s i b)).
Proof.
intros s n b.
revert b.
induction n; intros.
 rewrite nth_nonzero_interval_succ.
 reflexivity.

 rewrite nth_nonzero_interval_succ.
 rewrite IHn; f_equal.
 rewrite <- Nat.add_assoc; f_equal; simpl.
 unfold sigma; simpl.
 remember (first_nonzero fld s (S b)) as len eqn:Hlen .
 symmetry in Hlen.
 destruct len as [len| ].
  rewrite Nat.sub_0_r; f_equal.
  destruct n; simpl; rewrite Hlen, Nat.add_succ_r; [ reflexivity | f_equal ].
  symmetry.
  apply sigma_aux_fin_succ; assumption.

  rewrite Nat.sub_0_r, Nat.add_0_r; symmetry; simpl.
  apply sigma_aux_inf_succ; assumption.
Qed.

Lemma www : ∀ s k,
  (∀ n, nth_nonzero_interval fld s n 0 mod Pos.to_nat k = 0%nat)
  → ∀ i,
    (i mod Pos.to_nat k ≠ 0)%nat
    → series_nth_fld fld i s ≍ zero fld.
Proof.
intros s k Hs i Hi.
remember (rank_of_nonzero_before s i) as cnt.
pose proof (Hs cnt) as H.
subst cnt.
clear Hs.
unfold rank_of_nonzero_before in H.
destruct i.
 rewrite Nat.mod_0_l in Hi; [ idtac | apply Pos2Nat_ne_0 ].
 exfalso; apply Hi; reflexivity.

 replace (S i) with (0 + S i)%nat in H by reflexivity.
 apply vvv in H; auto.
qed.

(* essai d'induction sur i/k *)
intros s k Hs i Hi.
intros s k Hs i Hi.
remember (i / Pos.to_nat k)%nat as n eqn:Hn .
symmetry in Hn.
revert k i Hs Hi Hn.
induction n; intros.
 apply Nat.div_small_iff in Hn; [ idtac | apply Pos2Nat_ne_0 ].
 pose proof (Hs O) as H.
 simpl in H.
 remember (first_nonzero fld s 1) as len eqn:Hlen .
 symmetry in Hlen.
 destruct len as [len| ].
  apply first_nonzero_iff in Hlen; simpl in Hlen.
  destruct Hlen as (Hz, Hnz).
  destruct i.
   rewrite Nat.mod_0_l in Hi; [ idtac | apply Pos2Nat_ne_0 ].
   exfalso; apply Hi; reflexivity.

   apply Hz.
   apply Nat.mod_divides in H; [ idtac | apply Pos2Nat_ne_0 ].
   destruct H as (c, Hc).
   destruct c.
    rewrite Nat.mul_comm in Hc; discriminate Hc.

    rewrite Nat.mul_comm in Hc; simpl in Hc.
    remember (c * Pos.to_nat k)%nat as x.
    omega.

  apply first_nonzero_iff in Hlen; simpl in Hlen.
  destruct i.
   rewrite Nat.mod_0_l in Hi; [ idtac | apply Pos2Nat_ne_0 ].
   exfalso; apply Hi; reflexivity.

   apply Hlen.

 pose proof (Nat.div_mod i (Pos.to_nat k) (Pos2Nat_ne_0 k)) as Hdiv.
 rewrite Hn in Hdiv.
bbb.

(* démontré, non sans mal, que c'est vrai pour i=0 et i=1 mais la
   récurrence sur i me paraît mal barrée... *)
intros s k Hs i Hi.
destruct i.
 exfalso; apply Hi; rewrite Nat.mod_0_l; auto.

 revert k Hs Hi.
 induction i; intros.
  remember (Pos.to_nat k) as kn eqn:Hkn .
  symmetry in Hkn.
  destruct kn; [ exfalso; auto | idtac ].
  destruct kn; [ exfalso; auto | idtac ].
  pose proof (Hs 1%nat) as H.
  apply Nat.mod_divides in H.
   destruct H as (c, Hc).
   destruct c.
    rewrite Nat.mul_0_r in Hc.
    simpl in Hc.
    pose proof (Hs O) as H₀.
    apply Nat.mod_divides in H₀.
     destruct H₀ as (c₀, Hc₀).
     remember (S (S kn) * c₀)%nat as x.
     simpl in Hc₀; subst x.
     remember (first_nonzero fld s 1) as len₁ eqn:Hlen₁ .
     symmetry in Hlen₁.
     destruct len₁ as [len₁| ].
      destruct len₁.
       rewrite Nat.mul_comm in Hc₀.
       destruct c₀; discriminate Hc₀.

       apply first_nonzero_iff in Hlen₁; simpl in Hlen₁.
       destruct Hlen₁ as (Hz, Hnz).
       apply Hz.
       apply Nat.lt_0_succ.

      apply first_nonzero_iff in Hlen₁; simpl in Hlen₁.
      apply Hlen₁.

     intros H; discriminate H.

    simpl in Hc.
    remember (first_nonzero fld s 1) as len₁ eqn:Hlen₁ .
    symmetry in Hlen₁.
    destruct len₁ as [len₁| ]; [ idtac | discriminate Hc ].
    destruct len₁.
     pose proof (Hs O) as H₀.
     apply Nat.mod_divides in H₀.
      destruct H₀ as (c₀, Hc₀).
      remember (S (S kn) * c₀)%nat as x.
      simpl in Hc₀; subst x.
      rewrite Hlen₁ in Hc₀.
      rewrite Nat.mul_comm in Hc₀.
      destruct c₀; discriminate Hc₀.

      intros H; discriminate H.

     apply first_nonzero_iff in Hlen₁; simpl in Hlen₁.
     destruct Hlen₁ as (Hz, Hnz).
     apply Hz.
     apply Nat.lt_0_succ.

   clear H; intros H; discriminate H.
bbb.
*)

Lemma series_stretch_shrink : ∀ s k,
  (k | stretching_factor fld s 0)%positive
  → series_stretch fld k (series_shrink k s) ≃ s.
Proof.
intros s k Hk.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.fold_sub.
rewrite Nbar.fold_div.
rewrite Nbar.fold_div_sup.
remember (fin (Pos.to_nat k)) as kn eqn:Hkn .
destruct (Nbar.lt_dec (fin i) (Nbar.div_sup (stop s) kn * kn)) as [H₁| H₁].
 destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂].
  unfold series_nth_fld.
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
   apply stretching_factor_iff in Hk.
   unfold stretching_factor_gcd_prop in Hk.
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

    apply www with (s := s) in H; [ idtac | assumption ].
    unfold series_nth_fld in H.
    destruct (Nbar.lt_dec (fin i) (stop s)); [ assumption | contradiction ].

   reflexivity.
bbb.

   unfold stretching_factor_prop in Hk.
   remember (first_nonzero fld s 1) as n eqn:Hn .
   symmetry in Hn.
   destruct n as [n| ].
    simpl in Hk.
    destruct Hk as (Hz, Hnz).
    assert (i mod Pos.to_nat (c * k) ≠ 0)%nat as H.
     intros H.
     apply Nat.mod_divides in H.
      destruct H as (d, Hd).
      rewrite Pos2Nat.inj_mul, Nat.mul_shuffle0 in Hd.
      rewrite Hd in H₂.
      rewrite Nat.mod_mul in H₂; [ idtac | apply Pos2Nat_ne_0 ].
      revert H₂; apply Nat.lt_irrefl.

      apply Pos2Nat_ne_0.

     apply Hz in H.
     unfold series_nth_fld in H.
     destruct (Nbar.lt_dec (fin i) (stop s)) as [H₄| H₄].
      symmetry; assumption.

      contradiction.

    apply Pos.mul_eq_1_r in Hk.
    subst k.
    rewrite Nat.mod_1_r in H₂.
    exfalso; revert H₂; apply Nat.lt_irrefl.

   reflexivity.

 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₂| H₂].
  exfalso; apply H₁; clear H₁.
  eapply Nbar.lt_le_trans; [ eassumption | idtac ].
  unfold Nbar.div_sup.
  simpl.
  destruct (stop s) as [st| ]; simpl.
   Focus 2.
   unfold Nbar.div.
   destruct kn; constructor.

   destruct kn as [kn| ]; simpl.
    apply Nbar.le_fin.
    2: constructor.

    2: reflexivity.

  rewrite Nat_fold_div_sup.
  apply le_div_sup_mul.
  injection Hkn; intros; subst kn.
  apply Pos2Nat.is_pos.
Qed.

(*
Lemma www : ∀ s n k,
  stretching_factor_prop fld s n k ↔
  stretching_factor_gcd_prop fld s n (Pos.to_nat k).
Proof.
intros s n k.
split; intros H.
 unfold stretching_factor_gcd_prop.
 split.
  intros cnt.
  revert k cnt H.
  induction n; intros.
   destruct cnt; simpl.
    rewrite Nat.mod_0_l; [ reflexivity | apply Pos2Nat_ne_0 ].

    unfold stretching_factor_prop in H.
    remember (first_nonzero fld s 1) as m eqn:Hm .
    symmetry in Hm.
    destruct m as [m| ].
     simpl in H.
     rewrite divmod_mod.
bbb.
*)

Definition stretching_factor_prime_prop s n k :=
  match first_nonzero fld s (S n) with
  | fin _ =>
      (∀ i, i mod (Pos.to_nat k) ≠ O →
       series_nth_fld fld (n + i) s ≍ zero fld) ∧
      (∀ k', (Pos.to_nat k < k')%nat
       → prime (Z.of_nat k')
         → ∃ i, i mod k' ≠ O ∧ series_nth_fld fld (n + i) s ≭ zero fld)
  | ∞ =>
      k = 1%positive
  end.

Lemma stretching_factor_prop_1 : ∀ s n,
  stretching_factor_prop fld s n 1 ↔ stretching_factor_prime_prop s n 1.
Proof.
intros s n.
split; intros H.
 unfold stretching_factor_prop in H.
 unfold stretching_factor_prime_prop.
 remember (first_nonzero fld s (S n)) as m eqn:Hm .
 symmetry in Hm.
 destruct m as [m| ]; [ idtac | assumption ].
 destruct H as (Hz, Hnz).
 split.
  intros i Him.
  apply Hz; assumption.

  intros k' Hk' Hpk'.
  apply Hnz; assumption.

 unfold stretching_factor_prime_prop in H.
 unfold stretching_factor_prop.
 remember (first_nonzero fld s (S n)) as m eqn:Hm .
 symmetry in Hm.
 destruct m as [m| ]; [ idtac | assumption ].
 destruct H as (_, Hnz).
 split.
  intros i Him.
  exfalso; apply Him; apply Nat.mod_1_r.

  intros k' Hk'.
  assert (1 < Z.of_nat k')%Z as Hk.
   Focus 2.
   apply exists_prime_divisor in Hk.
   destruct Hk as (p, (Hp, Hpk')).
   remember (Z.to_nat p) as pn eqn:Hpn .
   assert (p = Z.of_nat pn) as Hpp.
    rewrite Hpn.
    rewrite Z2Nat.id; [ reflexivity | idtac ].
    apply prime_ge_2 in Hp.
    fast_omega Hp.

    remember Hp as Hpr; clear HeqHpr.
    rewrite Hpp in Hp.
    apply Hnz in Hp.
     destruct Hp as (j, (Hjm, Hjn)).
     exists j; split; [ idtac | assumption ].
     intros H; apply Hjm; clear Hjm.
     apply Nat.mod_divides in H; [ idtac | fast_omega Hk' ].
     destruct H as (c, Hc).
     destruct Hpk' as (d, Hd).
     rewrite Hc.
     apply Z2Nat.inj_iff in Hd.
      rewrite Nat2Z.id in Hd.
      destruct p as [| p| p].
       rewrite Z.mul_0_r in Hd; simpl in Hd.
       subst k'.
       fast_omega Hk'.

       rewrite Z2Nat_inj_mul_pos_r in Hd.
       rewrite <- positive_nat_Z in Hpp.
       apply Nat2Z.inj in Hpp.
       rewrite Hpp in Hd.
       rewrite Hd.
       rewrite Nat.mul_shuffle0.
       apply Nat.mod_mul.
       rewrite Hpn; simpl.
       apply Pos2Nat_ne_0.

       simpl in Hpn.
       subst pn; discriminate Hpp.

      apply Nat2Z.is_nonneg.

      rewrite <- Hd.
      apply Nat2Z.is_nonneg.

     apply prime_ge_2 in Hpr.
     rewrite Hpn.
     apply Nat2Z.inj_lt.
     rewrite positive_nat_Z.
     rewrite Z2Nat.id; fast_omega Hpr.

   apply Z2Nat_lt_lt.
   rewrite Nat2Z.id.
   assumption.
Qed.

Lemma stretching_factor_lim_stretch : ∀ s n k cnt,
  stretching_factor_lim fld cnt (series_stretch fld k s) (Pos.to_nat k * n) =
    (Pos.to_nat k * stretching_factor_lim fld cnt s n)%nat.
Proof.
(* à nettoyer *)
intros s n k cnt.
revert s n k.
induction cnt; intros.
 auto.

 simpl.
 remember
  (first_nonzero fld (series_stretch fld k s) (S (Pos.to_nat k * n))) as m
  eqn:Hm .
 symmetry in Hm.
 destruct m as [m| ].
  rewrite divmod_mod.
  remember (first_nonzero fld s (S n)) as p eqn:Hp .
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
    rewrite first_nonzero_stretch_succ with (p := p) in Hm; try assumption.
    symmetry in Hm.
    rewrite Nat.mul_comm.
    injection Hm; intros; assumption.

   rewrite Nat.mul_comm in Hm.
   rewrite first_nonzero_stretch_succ_inf in Hm.
    discriminate Hm.

    assumption.

  rewrite Nat.mul_comm in Hm.
  remember (first_nonzero fld s (S n)) as p eqn:Hp .
  symmetry in Hp.
  destruct p as [p| ]; [ idtac | auto ].
  apply first_nonzero_stretch_succ with (k := k) in Hp.
  rewrite Hm in Hp.
  discriminate Hp.
Qed.

(* en supposant que la version stretching_factor_gcd_prop fonctionne...
   ou alors en le prenant comme définition ? pourquoi pas. *)
Lemma vvv : ∀ s n p k,
  first_nonzero fld s 0 = fin n
  → first_nonzero fld s (S n) = fin p
    → stretching_factor fld (series_stretch fld k s) (n * Pos.to_nat k) =
      (k * stretching_factor fld s n)%positive.
Proof.
intros s n p k Hn Hp.
remember (stretching_factor fld s n) as m eqn:Hm .
symmetry in Hm.
apply stretching_factor_iff in Hm.
apply stretching_factor_iff.
apply www in Hm.
apply www.
unfold stretching_factor_gcd_prop in Hm |- *.
destruct Hm as (Hz, Hnz).
split.
 intros cnt.
 clear Hnz.
 revert n m p Hn Hp Hz.
 induction cnt; intros; simpl.
  rewrite Nat.mod_0_l; auto.
  apply Pos2Nat_ne_0.

  remember
   (first_nonzero fld (series_stretch fld k s) (S (n * Pos.to_nat k))) as q
   eqn:Hq .
  symmetry in Hq.
  destruct q as [q| ].
   rewrite divmod_mod.
   rewrite <- Nat.add_succ_r.
   rewrite first_nonzero_stretch_succ with (p := p) in Hq;
    [ idtac | assumption ].
   injection Hq; clear Hq; intros; subst q.
   rewrite <- Nat.sub_succ_l.
    rewrite Nat.sub_succ.
    rewrite Nat.sub_0_r.
    rewrite Nat.add_assoc, Nat.add_shuffle0, <- Nat.add_assoc.
    rewrite <- Nat.mul_succ_l.
    rewrite <- Nat.mul_add_distr_r.
    remember (n + S p)%nat as x.
    rewrite Nat.add_comm.
    rewrite <- Nat.mul_succ_l.
    subst x.
    rewrite Nat.mul_comm.
    rewrite stretching_factor_lim_stretch.
    rewrite Nat.mul_comm.
    rewrite Nat.mul_mod_distr_r.
     rewrite Nat.gcd_mul_mono_r.
     rewrite Pos2Nat.inj_mul.
     rewrite Nat.mul_comm.
     rewrite Nat.mul_mod_distr_l.
bbb.

(* en supposant que la version stretching_factor_gcd_prop fonctionne... *)L
Lemma yyy : ∀ s n k,
  first_nonzero fld s 1 = fin n
  → stretching_factor fld s 0 = 1%positive
    → stretching_factor fld (series_stretch fld k s) 0 = k.
Proof.
intros s n k Hn Hs.
apply stretching_factor_iff in Hs.
apply stretching_factor_iff.
apply www in Hs.
apply www.
unfold stretching_factor_gcd_prop in Hs |- *.
destruct Hs as (_, Hnz).
split.
 intros cnt.
 clear Hnz.
 revert n Hn.
 induction cnt; intros; simpl.
  rewrite Nat.mod_0_l; auto.
  apply Pos2Nat_ne_0.

  replace 1%nat with (S (0 * Pos.to_nat k))%nat by reflexivity.
  rewrite first_nonzero_stretch_succ with (p := n).
   rewrite divmod_mod.
   rewrite <- Nat.sub_succ_l.
    rewrite Nat.sub_succ.
    rewrite Nat.sub_0_r.
    remember (S n * Pos.to_nat k)%nat as m eqn:Hm .
bbb.

Lemma yyy : ∀ s n k,
  first_nonzero fld s 1 = fin n
  → stretching_factor fld s 0 = 1%positive
    → stretching_factor fld (series_stretch fld k s) 0 = k.
Proof.
(* si la version stretching_factor_gcd_prop ne fonctionne pas... *)
intros s n k Hn Hs.
apply stretching_factor_iff in Hs.
apply stretching_factor_iff.
unfold stretching_factor_prop in Hs |- *.
simpl in Hs |- *.
rewrite Hn in Hs.
remember (first_nonzero fld (series_stretch fld k s) 1) as m eqn:Hm .
symmetry in Hm.
destruct m as [m| ].
 Focus 2.
 destruct Hs as (_, Hnz).
 apply first_nonzero_iff in Hn.
 destruct Hn as (Hz₁, Hnz₁).
 apply first_nonzero_iff in Hm.
 rewrite <- series_nth_fld_mul_stretch with (k := k) in Hnz₁.
 remember (Pos.to_nat k) as kn eqn:Hkn .
 symmetry in Hkn.
 destruct kn as [| kn]; [ exfalso; revert Hkn; apply Pos2Nat_ne_0 | idtac ].
 simpl in Hnz₁.
 rewrite <- Nat.add_1_r, Nat.add_comm in Hnz₁.
 rewrite Hm in Hnz₁.
 exfalso; apply Hnz₁; reflexivity.

 destruct Hs as (_, Hnz).
 split.
  intros i Him.
  rewrite shifted_in_stretched; [ reflexivity | idtac ].
  apply Nat.neq_0_lt_0; assumption.

  intros k₁ Hk₁.
  remember (Pos.to_nat k) as kn eqn:Hkn .
  symmetry in Hkn.
  destruct kn; [ exfalso; revert Hkn; apply Pos2Nat_ne_0 | idtac ].
  assert (Pos.to_nat 1 < k₁)%nat as H₁.
   destruct k₁ as [| k₁].
    apply Nat.nle_gt in Hk₁.
    exfalso; apply Hk₁, le_0_n.

    unfold Pos.to_nat; simpl.
    apply lt_n_S.
    apply lt_S_n in Hk₁.
    destruct k₁ as [| k₁].
     apply Nat.nle_gt in Hk₁.
     exfalso; apply Hk₁, le_0_n.

     apply lt_0_Sn.

   apply Hnz in H₁.
   destruct H₁ as (j, (Hjm, Hjn)).
   destruct (zerop ((Pos.to_nat k * j) mod k₁)) as [H₁| H₁].
    Focus 2.
    exists (Pos.to_nat k * j)%nat.
    rewrite <- series_nth_fld_mul_stretch with (k := k) in Hjn.
    split; [ idtac | assumption ].
    apply Nat.neq_0_lt_0; assumption.

    rewrite <- Hkn in Hk₁.
bbb.
   destruct H₁ as (i, (Him, Hin)).
   destruct (zerop ((Pos.to_nat k * i) mod k₁)) as [H₁| H₁].
    Focus 2.
    exists (Pos.to_nat k * i)%nat.
    rewrite <- series_nth_fld_mul_stretch with (k := k) in Hin.
    split; [ idtac | assumption ].
    apply Nat.neq_0_lt_0; assumption.

    rename i into b.
    apply Nat.mod_divides in H₁; [ idtac | fast_omega Hk₁ ].
    destruct H₁ as (a, Ha).
    rewrite Nat.mul_comm in Ha.
    symmetry in Ha; rewrite Nat.mul_comm in Ha.
    rewrite <- Hkn in Hk₁.
    destruct kn as [| kn].
     exists b.
     split; [ assumption | idtac ].
     rewrite <- Pos2Nat.inj_1 in Hkn.
     apply Pos2Nat.inj in Hkn.
     subst k; rewrite series_stretch_1; assumption.
bbb.

(* c'est la merde, je trouve pas. Pourtant, ça a l'air vrai ! *)
Lemma zzz : ∀ s n k,
  first_nonzero fld s 1 = fin n
  → stretching_factor fld (series_stretch fld k s) 0 =
      (k * stretching_factor fld s 0)%positive.
Proof.
intros s n k Hn.
remember (stretching_factor fld s 0) as k₁ eqn:Hk₁ .
remember (stretching_factor fld (series_stretch fld k s) 0) as k₂ eqn:Hk₂ .
remember (first_nonzero fld (series_stretch fld k s) 1) as m eqn:Hm .
symmetry in Hk₁, Hk₂, Hm.
destruct m as [m| ].
 destruct (Z_dec (' k₂) (' (k * k₁))) as [[H₁| H₁]| H₁].
  exfalso.
  apply stretching_factor_iff in Hk₁.
  apply stretching_factor_iff in Hk₂.
  rewrite Hn in Hk₁.
  rewrite Hm in Hk₂.
  simpl in Hk₁, Hk₂.
  destruct Hk₁ as (Hz₁, Hnz₁).
  destruct Hk₂ as (Hz₂, Hnz₂).
  do 2 rewrite <- positive_nat_Z in H₁.
  apply Nat2Z.inj_lt in H₁.
  apply Hnz₂ in H₁.
  destruct H₁ as (i, (Him, Hin)).
  destruct (zerop (i mod Pos.to_nat k₁)) as [H₁| H₁].
   apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
   destruct H₁ as (c, Hc).
   rewrite Hc in Him.
   rewrite Pos2Nat.inj_mul in Him.
   rewrite Nat.mul_comm in Him.
   rewrite Nat.mul_mod_distr_r in Him; try apply Pos2Nat_ne_0.
   apply Nat.neq_mul_0 in Him.
   destruct Him as (Him, _).
   destruct (zerop (i mod Pos.to_nat k)) as [H₁| H₁].
    apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
    destruct H₁ as (d, Hd).
    remember Hin as Hin_v; clear HeqHin_v.
    rewrite Hd in Hin.
    rewrite series_nth_fld_mul_stretch in Hin.
    destruct (zerop (d mod Pos.to_nat k₁)) as [H₁| H₁].
     apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
     destruct H₁ as (e, He).
     rewrite He in Hd.
     rewrite Hc in Hd.
     rewrite Nat.mul_assoc, Nat.mul_shuffle0 in Hd.
     rewrite Nat.mul_comm in Hd.
     rewrite Nat.mul_cancel_r in Hd; [ idtac | apply Pos2Nat_ne_0 ].
     rewrite Hd in Him.
     rewrite Nat.mul_comm in Him.
     rewrite Nat.mod_mul in Him; [ idtac | apply Pos2Nat_ne_0 ].
     apply Him; reflexivity.

     assert (d mod Pos.to_nat k₁ ≠ 0)%nat as H.
      intros H; rewrite H in H₁; revert H₁; apply Nat.lt_irrefl.

      apply Hz₁ in H.
      rewrite H in Hin; apply Hin; reflexivity.

    rewrite shifted_in_stretched in Hin; [ idtac | assumption ].
    apply Hin; reflexivity.

   assert (i mod Pos.to_nat k₁ ≠ 0)%nat as H₂.
    intros H; rewrite H in H₁; revert H₁; apply Nat.lt_irrefl.

    destruct (zerop (i mod Pos.to_nat k)) as [H₃| H₃].
     apply Nat.mod_divides in H₃; [ idtac | apply Pos2Nat_ne_0 ].
     destruct H₃ as (c, Hc).
     rewrite Hc in Hin.
     rewrite series_nth_fld_mul_stretch in Hin.
     destruct (zerop (c mod Pos.to_nat k₁)) as [H₃| H₃].
      apply Nat.mod_divides in H₃; [ idtac | apply Pos2Nat_ne_0 ].
      destruct H₃ as (d, Hd).
      rewrite Hd in Hc.
      rewrite Nat.mul_assoc, Nat.mul_shuffle0, Nat.mul_comm in Hc.
      rewrite Nat.mul_assoc, <- Pos2Nat.inj_mul in Hc.
      rewrite Nat.mul_comm in Hc.
      rewrite Pos.mul_comm in Him.
      rewrite Hc in Him.
      rewrite Nat.mod_mul in Him; [ idtac | apply Pos2Nat_ne_0 ].
      apply Him; reflexivity.

      assert (c mod Pos.to_nat k₁ ≠ 0)%nat as H₄ by fast_omega H₃.
      apply Hz₁ in H₄.
      rewrite H₄ in Hin.
      apply Hin; reflexivity.

     rewrite shifted_in_stretched in Hin; [ idtac | assumption ].
     apply Hin; reflexivity.

  exfalso.
  destruct (Z_zerop (' k₂ mod ' (k * k₁))) as [H₂| H₂].
   apply Z.mod_divide in H₂; [ idtac | apply Pos2Z_ne_0 ].
   destruct H₂ as (q, Hq).
   destruct q as [| q| q].
    revert Hq; apply Pos2Z_ne_0.

    destruct (Pos.eq_dec q 1) as [H₃| H₃].
     subst q.
     rewrite Z.mul_1_l in Hq.
     apply Z.gt_lt in H₁.
     rewrite Hq in H₁; revert H₁; apply Z.lt_irrefl.

     assert (stretching_factor fld s 0 = q * k₁)%positive as H₄.
      apply stretching_factor_iff.
      rewrite Hn.
      split.
       intros i Him; simpl.
       apply stretching_factor_iff in Hk₂.
       rewrite Hm in Hk₂.
       simpl in Hk₂.
       destruct Hk₂ as (Hz₂, Hnz₂).
       rewrite <- series_nth_fld_mul_stretch with (k := k).
       apply Hz₂.
       intros H; apply Him; clear Him.
       simpl in Hq.
       do 2 rewrite <- positive_nat_Z in Hq.
       apply Nat2Z.inj in Hq.
       rewrite Hq in H.
       rewrite Pos.mul_assoc, Pos_mul_shuffle0, Nat.mul_comm in H.
       rewrite Pos2Nat.inj_mul in H.
       rewrite Nat.mul_mod_distr_r in H; try apply Pos2Nat_ne_0.
       apply Nat.eq_mul_0_l in H; [ assumption | apply Pos2Nat_ne_0 ].

       intros k' Hk'; simpl.
       apply stretching_factor_iff in Hk₁.
       simpl in Hk₁.
       rewrite Hn in Hk₁.
       destruct Hk₁ as (Hz₁, Hnz₁).
       apply Hnz₁.
       eapply Nat.le_lt_trans; [ idtac | eassumption ].
       rewrite Pos2Nat.inj_mul.
       edestruct mult_O_le; [ idtac | eassumption ].
       exfalso; revert H; apply Pos2Nat_ne_0.

      rewrite Hk₁ in H₄.
      symmetry in H₄.
      rewrite <- Pos.mul_1_l in H₄.
      apply Pos.mul_reg_r in H₄; contradiction.

    discriminate Hq.

   assert (' (k * k₁) ≠ 0)%Z as H₃ by apply Pos2Z_ne_0.
   apply Z.div_mod with (a := Zpos k₂) in H₃.
   remember (' k₂ / ' (k * k₁))%Z as q eqn:Hq .
   remember (' k₂ mod ' (k * k₁))%Z as r eqn:Hr .
   apply stretching_factor_iff in Hk₂.
   simpl in Hk₂.
   rewrite Hm in Hk₂.
   destruct Hk₂ as (Hz₂, Hnz₂).
   assert (Pos.to_nat k₂ < Z.to_nat (' (k * k₁) * (q + 1)))%nat as H₄.
    rewrite <- positive_nat_Z in H₃.
    apply Nat2Z.inj_lt.
    rewrite H₃.
    rewrite Z2Nat.id.
     rewrite Z.mul_add_distr_l.
     apply Z.add_lt_mono_l.
     rewrite Z.mul_1_r.
     rewrite Hr.
     assert (0 < ' (k * k₁))%Z as H₄ by apply Pos2Z.is_pos.
     apply Z.mod_pos_bound with (a := Zpos k₂) in H₄.
     destruct H₄; assumption.

     assert (0 <= q)%Z as H₄.
      rewrite Hq; apply Z_div_pos_is_nonneg.

      destruct q as [| q| q].
       apply Pos2Z.is_nonneg.

       apply Pos2Z.is_nonneg.

       apply Z.nlt_ge in H₄.
       exfalso; apply H₄; apply Pos2Z.neg_is_neg.

    apply Hnz₂ in H₄.
    destruct H₄ as (i, (Him, Hin)).
    destruct (zerop (i mod Pos.to_nat k₂)) as [H₄| H₄].
     Focus 2.
     assert (i mod Pos.to_nat k₂ ≠ 0)%nat as H₅.
      intros H.
      rewrite H in H₄; revert H₄; apply Nat.lt_irrefl.

      apply Hz₂ in H₅.
      rewrite H₅ in Hin; apply Hin; reflexivity.

     destruct (zerop (i mod Pos.to_nat k)) as [H₅| H₅].
      Focus 2.
      apply shifted_in_stretched with (s := s) in H₅.
      rewrite H₅ in Hin; apply Hin; reflexivity.

      apply Nat.mod_divides in H₅; [ idtac | apply Pos2Nat_ne_0 ].
      destruct H₅ as (c, Hc).
      rewrite Hc in Hin.
      rewrite series_nth_fld_mul_stretch in Hin.
      (* aussi : c mod k₁ = 0 ! *)
      apply stretching_factor_iff in Hk₁.
      simpl in Hk₁.
      rewrite Hn in Hk₁.
      destruct Hk₁ as (Hz₁, Hnz₁).
      assert (Pos.to_nat k₁ < Pos.to_nat k₂)%nat as H₅.
       do 2 rewrite <- positive_nat_Z in H₁.
       apply Z.gt_lt in H₁.
       apply Nat2Z.inj_lt in H₁.
       rewrite Pos2Nat.inj_mul in H₁.
       eapply le_lt_trans; [ idtac | eassumption ].
       remember (Pos.to_nat k) as kn eqn:Hkn .
       symmetry in Hkn.
       destruct kn as [| kn].
        exfalso; revert Hkn; apply Pos2Nat_ne_0.

        simpl.
        apply le_plus_l.

       apply Hnz₁ in H₅.
       destruct H₅ as (j, (Hjm, Hjn)).
       assert (i mod Pos.to_nat (k * k₁) = 0)%nat as H₅.
        rewrite Hc.
        rewrite Pos2Nat.inj_mul.
        rewrite Nat.mul_mod_distr_l; try apply Pos2Nat_ne_0.
        destruct (zerop (c mod Pos.to_nat k₁)) as [H₅| H₅].
         rewrite H₅, Nat.mul_comm; reflexivity.

         assert (c mod Pos.to_nat k₁ ≠ 0)%nat as H₆.
          intros H; rewrite H in H₅; revert H₅; apply Nat.lt_irrefl.

          apply Hz₁ in H₆.
          rewrite H₆ in Hin; exfalso; apply Hin; reflexivity.

        apply Nat.mod_divides in H₅; [ idtac | apply Pos2Nat_ne_0 ].
        destruct H₅ as (u, Hu).
bbb.
So what ?
*)

(* vraiment intéressant... à voir...
   oui mais avec zzz plus simple ci-dessus (n = 0), j'y arrive même pas !
Lemma stretching_factor_stretch : ∀ s n k,
  first_nonzero fld s 0 = fin n
  → first_nonzero fld s (S n) ≠ ∞
    → stretching_factor fld (series_stretch fld k s) (n * Pos.to_nat k) =
      (k * stretching_factor fld s n)%positive.
Proof.
intros s n k Hn Hsn.
remember (Pos.to_nat k) as kn eqn:Hkn .
symmetry in Hkn.
destruct kn as [| kn].
 exfalso; revert Hkn; apply Pos2Nat_ne_0.

 destruct kn as [| kn].
  rewrite Nat.mul_1_r.
  replace 1%nat with (Pos.to_nat xH) in Hkn ; [ idtac | reflexivity ].
  apply Pos2Nat.inj in Hkn.
  subst k.
  rewrite series_stretch_1, Pos.mul_1_l.
  reflexivity.

  rewrite <- Hkn.
  remember (series_stretch fld k s) as s₁.
  remember (stretching_factor fld s₁ (n * Pos.to_nat k)) as k₁ eqn:Hk₁ .
  symmetry in Hk₁.
  apply stretching_factor_iff in Hk₁.
  remember (first_nonzero fld s₁ (S (n * Pos.to_nat k))) as m eqn:Hm .
  symmetry in Hm.
  destruct m as [m| ].
   rewrite Heqs₁ in Hm.
   remember (first_nonzero fld s (S n)) as p eqn:Hp .
   symmetry in Hp.
   destruct p as [p| ]; [ clear Hsn | exfalso; apply Hsn; reflexivity ].
   remember Hm as Hm'; clear HeqHm'.
   erewrite first_nonzero_stretch_succ in Hm'; try eassumption.
   rewrite <- Hm' in Hm; clear Hm'.
   clear m.
   remember (stretching_factor fld s n) as k₂ eqn:Hk₂ .
   symmetry in Hk₂.
   destruct (Z_dec (Zpos k₁) (Zpos (k * k₂))) as [[H₁| H₁]| H₁].
    Focus 3.
    injection H₁; clear H₁; intros; subst k₁.
    reflexivity.

    exfalso.
    do 2 rewrite <- positive_nat_Z in H₁.
    apply Nat2Z.inj_lt in H₁.
    apply Pos2Nat.inj_lt in H₁.
    apply stretching_factor_iff in Hk₂.
    rewrite Hp in Hk₂.
bbb.
  remember (stretching_factor fld s b) as k₁ eqn:Hk₁ .
  remember (series_stretch fld k s) as t.
  remember (stretching_factor fld t (b * Pos.to_nat k)) as k₂ eqn:Hk₂ .
  subst t.
  symmetry in Hk₁, Hk₂.
  apply stretching_factor_iff in Hk₁.
  apply stretching_factor_iff in Hk₂.
  remember (first_nonzero fld s (S b)) as n₁ eqn:Hn₁ .
  remember (series_stretch fld k s) as t.
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
