(* $Id: Puiseux_series.v,v 2.102 2013-12-17 23:19:21 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Nbar.
Require Import Power_series.

Set Implicit Arguments.

Record puiseux_series α := mkps
  { ps_terms : power_series α;
    ps_valnum : Z;
    ps_comden : positive }.

Section Axioms.

(* [null_coeff_range_length rng s n] returns the number of consecutive
   null coefficients in the series [s], from the [n]th one. *)
Definition null_coeff_range_length : ∀ α,
  Lfield.r α → power_series α → nat → Nbar.
Admitted.

Definition null_coeff_range_length_prop s n v :=
  match v with
  | fin k =>
      (∀ i, (i < k)%nat → (series_nth rng (n + i) s = 0)%rng) ∧
      (series_nth rng (n + k) s ≠ 0)%rng
  | ∞ =>
      (∀ i, (series_nth rng (n + i) s = 0)%rng)
  end.

Axiom null_coeff_range_length_iff : ∀ s n v,
  null_coeff_range_length rng s n = v ↔ null_coeff_range_length_prop s n v.

(* [greatest_series_x_power rng s n] returns the greatest nat value [k]
   such that [s], starting at index [n], is a series in [x^k]. *)
Definition greatest_series_x_power : ∀ α,
  Lfield.r α → power_series α → nat → nat.
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
  ∀ n, (k | nth_null_coeff_range_length s n b).

Definition is_the_greatest_series_x_power s b k :=
  match null_coeff_range_length rng s (S b) with
  | fin _ =>
      is_a_series_in_x_power s b k ∧
      (∀ k', (k < k')%nat → ∃ n, ¬(k' | nth_null_coeff_range_length s n b))
  | ∞ =>
      k = 0%nat
  end.

Axiom greatest_series_x_power_iff : ∀ s n k,
  greatest_series_x_power rng s n = k ↔
  is_the_greatest_series_x_power s n k.

End Axioms.

Definition series_stretch k s :=
  {| terms i :=
       if zerop (i mod Pos.to_nat k) then series_nth rng (i / Pos.to_nat k) s
       else 0%rng;
     stop :=
       stop s * fin (Pos.to_nat k) |}.

Definition series_shift n s :=
  {| terms i := if lt_dec i n then 0%rng else terms s (i - n);
     stop := stop s + fin n |}.

Definition series_shrink k (s : power_series α) :=
  {| terms i := terms s (i * Pos.to_nat k);
     stop := Nbar.div_sup (stop s) (fin (Pos.to_nat k)) |}.

Definition series_left_shift n (s : power_series α) :=
  {| terms i := terms s (n + i);
     stop := stop s - fin n |}.

Definition canonify_series n k (s : power_series α) :=
  series_shrink k (series_left_shift n s).

Definition gcd_ps n k (ps : puiseux_series α) :=
  Z.gcd (Z.gcd (ps_valnum ps + Z.of_nat n) (' ps_comden ps)) (Z.of_nat k).

Definition ps_zero := {| ps_terms := 0%ser; ps_valnum := 0; ps_comden := 1 |}.

Definition canonic_ps ps :=
  match null_coeff_range_length rng (ps_terms ps) 0 with
  | fin n =>
      let k := greatest_series_x_power rng (ps_terms ps) n in
      let g := gcd_ps n k ps in
      {| ps_terms := canonify_series n (Z.to_pos g) (ps_terms ps);
         ps_valnum := (ps_valnum ps + Z.of_nat n) / g;
         ps_comden := Z.to_pos (' ps_comden ps / g) |}
  | ∞ =>
      ps_zero
  end.

Inductive eq_ps_strong : puiseux_series α → puiseux_series α → Prop :=
  | eq_strong_base : ∀ ps₁ ps₂,
      ps_valnum ps₁ = ps_valnum ps₂
      → ps_comden ps₁ = ps_comden ps₂
        → (ps_terms ps₁ = ps_terms ps₂)%ser
          → eq_ps_strong ps₁ ps₂.

Inductive eq_ps : puiseux_series α → puiseux_series α → Prop :=
  | eq_ps_base : ∀ ps₁ ps₂,
      eq_ps_strong (canonic_ps ps₁) (canonic_ps ps₂)
      → eq_ps ps₁ ps₂.

Definition ps_monom (c : α) pow :=
  {| ps_terms := {| terms i := c; stop := 1 |};
     ps_valnum := Qnum pow;
     ps_comden := Qden pow |}.

Definition ps_const c : puiseux_series α := ps_monom c 0.
Definition ps_one := ps_const 1%rng.

Notation "a ≐ b" := (eq_ps_strong a b) (at level 70).

Delimit Scope ps_scope with ps.
Notation "a = b" := (eq_ps a b) : ps_scope.
Notation "a ≠ b" := (not (eq_ps a b)) : ps_scope.
Notation "0" := ps_zero : ps_scope.
Notation "1" := ps_one : ps_scope.

Lemma series_stretch_1 : ∀ s, (series_stretch 1 s = s)%ser.
Proof.
intros s.
unfold series_stretch; simpl.
constructor; intros i.
unfold series_nth; simpl.
rewrite divmod_div, Nbar.mul_1_r, Nat.div_1_r.
destruct (Nbar.lt_dec (fin i) (stop s)); reflexivity.
Qed.

Theorem eq_strong_refl : reflexive _ eq_ps_strong.
Proof. intros ps; constructor; reflexivity. Qed.

Theorem eq_strong_sym : symmetric _ eq_ps_strong.
Proof. intros ps₁ ps₂ H; induction H; constructor; symmetry; assumption. Qed.

Theorem eq_strong_trans : transitive _ eq_ps_strong.
Proof.
intros ps₁ ps₂ ps₃ H₁ H₂.
induction H₁, H₂.
constructor; etransitivity; eassumption.
Qed.

Add Parametric Relation : (puiseux_series α) eq_ps_strong
 reflexivity proved by eq_strong_refl
 symmetry proved by eq_strong_sym
 transitivity proved by eq_strong_trans
 as eq_strong_rel.

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

Add Parametric Morphism : (@mkps α)
  with signature eq_series ==> eq ==> eq ==> eq_ps_strong
  as mkps_strong_eq_morphism.
Proof.
intros a b Hab v n.
constructor; [ reflexivity | reflexivity | assumption ].
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
remember (null_coeff_range_length rng s₁ (S n)) as p₁ eqn:Hp₁ .
symmetry in Hp₁.
rewrite Heq in Hp₁.
rewrite Hp₁ in Hk.
destruct p₁ as [p₁| ]; [ idtac | assumption ].
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
unfold series_nth; simpl.
unfold series_nth; simpl.
unfold series_nth in Heq; simpl in Heq.
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
unfold series_nth; simpl.
do 2 rewrite Nbar.fold_sub, Nbar.fold_div, Nbar.fold_div_sup.
inversion Heq; subst.
clear Heq; rename H into Heq.
unfold series_nth in Heq; simpl in Heq.
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
unfold series_nth; simpl.
unfold series_nth in H; simpl in H.
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

Add Parametric Morphism : canonify_series
  with signature eq ==> eq ==> eq_series ==> eq_series
  as canonify_morph.
Proof.
intros n k ps₁ ps₂ Heq.
constructor; intros i.
inversion Heq; subst.
unfold canonify_series.
unfold series_shrink, series_left_shift.
remember Nbar.div_sup as f; simpl; subst f.
do 2 rewrite Nbar.fold_sub.
pose proof (H (n + i * Pos.to_nat k)%nat) as Hi.
remember Nbar.div_sup as f.
unfold series_nth in Hi |- *; simpl.
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

Add Parametric Morphism : canonic_ps
  with signature eq_ps_strong ==> eq_ps_strong
  as canonic_ps_morph.
Proof.
intros ps₁ ps₂ Heq.
inversion Heq; subst.
unfold canonic_ps.
rewrite H, H0, H1.
remember (null_coeff_range_length rng (ps_terms ps₂) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
unfold gcd_ps.
rewrite H, H0.
constructor; simpl; rewrite H1; reflexivity.
Qed.

Theorem eq_ps_refl : reflexive _ eq_ps.
Proof.
intros ps.
destruct ps; constructor; reflexivity.
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
unfold series_nth; simpl.
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

Lemma series_shift_series_0 : ∀ n, (series_shift n 0 = 0)%ser.
Proof.
intros n.
constructor; intros i.
rewrite series_nth_series_0.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) (fin n)); [ idtac | reflexivity ].
destruct (lt_dec i n); reflexivity.
Qed.

Lemma series_stretch_series_0 : ∀ k, (series_stretch k 0 = 0)%ser.
Proof.
intros k.
constructor; intros i.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) 0); [ idtac | reflexivity ].
destruct (zerop (i mod Pos.to_nat k)); [ idtac | reflexivity ].
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin (i / Pos.to_nat k)) 0); reflexivity.
Qed.

Lemma series_stretch_0_if : ∀ k s, (series_stretch k s = 0)%ser → (s = 0)%ser.
Proof.
intros k s Hs.
constructor.
intros i.
inversion Hs; subst.
pose proof (H (i * Pos.to_nat k)%nat) as Hi.
unfold series_nth in Hi; simpl in Hi.
rewrite Nat.mod_mul in Hi; [ simpl in Hi | apply Pos2Nat_ne_0 ].
rewrite Nat.div_mul in Hi; [ simpl in Hi | apply Pos2Nat_ne_0 ].
remember (stop s * fin (Pos.to_nat k))%Nbar as ss.
destruct (Nbar.lt_dec (fin (i * Pos.to_nat k)) ss).
 rewrite Hi.
 unfold series_nth; simpl.
 destruct (Nbar.lt_dec (fin (i * Pos.to_nat k)) 0).
  destruct (Nbar.lt_dec (fin i) 0); reflexivity.

  destruct (Nbar.lt_dec (fin i) 0); reflexivity.

 unfold series_nth; simpl.
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
unfold series_stretch, series_nth; simpl.
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
unfold series_nth; simpl.
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
unfold series_nth; simpl.
rewrite Nbar.fold_sub.
destruct (Nbar.le_dec (fin n) (stop s)) as [H₁| H₁].
 rewrite Nbar.sub_add; auto.
 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₂| H₂].
  destruct (lt_dec i n) as [H₃| H₃].
   apply Hz in H₃.
   unfold series_nth in H₃.
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
    unfold series_nth in H₃.
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
unfold series_nth; simpl.
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
unfold series_nth; simpl.
do 2 rewrite Nbar.fold_sub.
rewrite Nbar.fin_inj_mul.
rewrite <- Nbar.mul_sub_distr_r; [ idtac | intros H; discriminate H ].
rewrite Nat.add_comm.
rewrite Nat.mod_add; auto.
rewrite Nat.div_add; auto.
remember ((stop s - fin n) * fin (Pos.to_nat k))%Nbar as x eqn:Hx .
destruct (Nbar.lt_dec (fin i) x) as [H₁| H₁]; [ idtac | reflexivity ].
destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂]; [ idtac | reflexivity ].
unfold series_nth; simpl.
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
Qed.

Add Parametric Relation : (puiseux_series α) eq_ps
 reflexivity proved by eq_ps_refl
 symmetry proved by eq_ps_sym
 transitivity proved by eq_ps_trans
 as eq_ps_rel.

Lemma series_shift_0 : ∀ s, (series_shift 0 s = s)%ser.
Proof.
intros s.
constructor; intros i.
unfold series_shift, series_nth; simpl.
rewrite Nbar.add_0_r, Nat.sub_0_r; reflexivity.
Qed.

Lemma series_nth_shift_S : ∀ s n i,
  series_nth rng i (series_shift n s) =
  series_nth rng (S i) (series_shift (S n) s).
Proof.
intros s n i.
unfold series_nth; simpl.
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
    unfold series_nth in Hv; simpl in Hv.
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
  unfold series_nth in Hv; simpl in Hv.
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
  → series_nth rng i (series_stretch k s) = 0%rng.
Proof.
intros s k i Hi.
unfold series_nth; simpl.
unfold series_nth; simpl.
destruct (zerop (i mod Pos.to_nat k)) as [Hz| Hnz].
 exfalso; revert Hi; rewrite Hz; apply Nat.lt_irrefl.

 destruct (Nbar.lt_dec (fin i) (stop s * fin (Pos.to_nat k))); reflexivity.
Qed.

Lemma series_nth_mul_stretch : ∀ s k i,
  series_nth rng (Pos.to_nat k * i) (series_stretch k s) =
  series_nth rng i s.
Proof.
intros s k i.
unfold series_nth; simpl.
rewrite Nat.mul_comm.
rewrite Nat.mod_mul; [ simpl | apply Pos2Nat_ne_0 ].
rewrite Nat.div_mul; [ simpl | apply Pos2Nat_ne_0 ].
unfold series_nth.
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

Lemma series_nth_mul_shrink : ∀ s k i,
  series_nth rng (Pos.to_nat k * i) s =
  series_nth rng i (series_shrink k s).
Proof.
intros s k i.
unfold series_nth; simpl.
rewrite Nbar.fold_sub.
rewrite Nbar.fold_div.
rewrite Nbar.fold_div_sup.
remember (Nbar.div_sup (stop s) (fin (Pos.to_nat k))) as x eqn:Hx .
destruct (Nbar.lt_dec (fin (Pos.to_nat k * i)) (stop s)) as [H₁| H₁].
 rewrite Nat.mul_comm, Nbar.fin_inj_mul in H₁.
 rewrite Nat.mul_comm.
 destruct (Nbar.lt_dec (fin i) x) as [| H₂]; [ reflexivity | idtac ].
 exfalso; apply H₂; subst x.
 apply Nbar.lt_mul_r_lt_div_sup; [ idtac | assumption ].
 apply Nbar.fin_lt_mono, Pos2Nat.is_pos.

 destruct (Nbar.lt_dec (fin i) x) as [H₂| ]; [ idtac | reflexivity ].
 exfalso; apply H₁; subst x.
 rewrite Nat.mul_comm, Nbar.fin_inj_mul.
 apply Nbar.lt_div_sup_lt_mul_r; assumption.
Qed.

Lemma stretch_finite_series : ∀ s b k,
  (∀ i, (series_nth rng (b + i) s = 0)%rng)
  → ∀ i,
    (series_nth rng (b * Pos.to_nat k + i) (series_stretch k s) = 0)%rng.
Proof.
intros s b k Hz i.
destruct (zerop (i mod Pos.to_nat k)) as [H₁| H₁].
 apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
 destruct H₁ as (c, H₁).
 subst i.
 rewrite Nat.mul_comm, <- Nat.mul_add_distr_l.
 rewrite series_nth_mul_stretch.
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
   rewrite series_nth_mul_stretch.
   apply Hz.
   rewrite H₁ in Hin.
   rewrite Nat.mul_comm in Hin.
   apply Nat.mul_lt_mono_pos_r in Hin; [ assumption | apply Pos2Nat.is_pos ].

   rewrite shifted_in_stretched; [ reflexivity | idtac ].
   rewrite Nat.add_comm.
   rewrite Nat.mod_add; [ assumption | apply Pos2Nat_ne_0 ].

  rewrite <- Nat.mul_add_distr_r.
  rewrite Nat.mul_comm.
  rewrite series_nth_mul_stretch.
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
  series_nth rng (i + n) (series_shift n s) =
  series_nth rng i s.
Proof.
intros s i n.
unfold series_nth; simpl.
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

Lemma series_nth_add_left_shift : ∀ s i n,
  series_nth rng (i + n) s =
  series_nth rng i (series_left_shift n s).
Proof.
intros s i n.
unfold series_nth; simpl.
rewrite Nbar.fold_sub.
destruct (Nbar.lt_dec (fin (i + n)) (stop s)) as [H₁| H₁].
 rewrite Nat.add_comm.
 destruct (Nbar.lt_dec (fin i) (stop s - fin n)) as [H₂| H₂].
  reflexivity.

  exfalso; apply H₂.
  apply Nbar.lt_add_lt_sub_r; assumption.

 destruct (Nbar.lt_dec (fin i) (stop s - fin n)) as [H₂| H₂].
  exfalso; apply H₁.
  rewrite Nbar.fin_inj_add.
  apply Nbar.lt_add_lt_sub_r; assumption.

  reflexivity.
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
rewrite <- Nat.add_succ_l, Nat.add_comm.
rewrite null_coeff_range_length_shift_add.
remember (null_coeff_range_length rng s (S b)) as p eqn:Hp .
symmetry in Hp.
destruct p as [p| ]; [ idtac | assumption ].
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
  rewrite series_nth_mul_stretch in Hnzq.
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
      rewrite series_nth_mul_stretch in H.
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
 rewrite <- series_nth_mul_stretch with (k := k) in Hnzp.
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

Lemma series_shrink_shrink : ∀ (s : power_series α) k₁ k₂,
  (series_shrink (k₁ * k₂) s = series_shrink k₁ (series_shrink k₂ s))%ser.
Proof.
intros s k₁ k₂.
constructor; intros i.
unfold series_shrink; simpl.
unfold series_nth; simpl.
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
unfold series_nth; simpl.
rewrite Nbar.fold_sub.
rewrite Nbar.fold_div.
rewrite Nbar.fold_div_sup.
rewrite Nbar.div_sup_mul.
 rewrite Nat.mod_mul; simpl.
  rewrite Nat.div_mul; simpl.
   unfold series_nth.
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

Definition rank_of_nonzero_before s i :=
  pred (rank_of_nonzero_after_from s (S i) i 0).

Lemma series_nth_0_in_interval_from_any : ∀ s i c b k,
  (i < c)%nat
  → (∀ n, (Pos.to_nat k | nth_null_coeff_range_length s n b)%nat)
    → (Pos.to_nat k |
       nth_null_coeff_range_length s
         (pred (rank_of_nonzero_after_from s c (b + i) b)) b)%nat
      → i mod Pos.to_nat k ≠ O
        → (series_nth rng (b + i) s = 0)%rng.
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
    → (series_nth rng i s = 0)%rng.
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
  (Pos.to_nat k | greatest_series_x_power rng s 0)
  → (series_stretch k (series_shrink k s) = s)%ser.
Proof.
intros s k Hk.
constructor; intros i.
unfold series_nth; simpl.
rewrite Nbar.fold_sub.
rewrite Nbar.fold_div.
rewrite Nbar.fold_div_sup.
remember (fin (Pos.to_nat k)) as kn eqn:Hkn .
destruct (Nbar.lt_dec (fin i) (Nbar.div_sup (stop s) kn * kn)) as [H₁| H₁].
 destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂].
  unfold series_nth.
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
   remember (null_coeff_range_length rng s 1) as p eqn:Hp .
   symmetry in Hp.
   destruct p as [p| ].
    destruct Hk as (Hz, Hnz).
    symmetry.
    destruct c.
     simpl in Hz.
     unfold is_a_series_in_x_power in Hz.
     pose proof (Hz O) as H.
     simpl in H.
     rewrite Hp in H.
     destruct H as (c, Hc).
     rewrite Nat.mul_0_r in Hc.
     discriminate Hc.

     assert (i mod (S c * Pos.to_nat k) ≠ 0)%nat as H.
      intros H.
      apply Nat.mod_divides in H.
       destruct H as (d, Hd).
       rewrite Nat.mul_shuffle0 in Hd.
       rewrite Hd in H₂.
       rewrite Nat.mod_mul in H₂; [ idtac | apply Pos2Nat_ne_0 ].
       revert H₂; apply Nat.lt_irrefl.

       apply Nat.neq_mul_0.
       split; auto.

      remember (S c) as d eqn:Hd .
      rewrite <- Nat2Pos.id in Hd; auto; subst d.
      rewrite <- Pos2Nat.inj_mul in H.
      rewrite <- Pos2Nat.inj_mul in Hz.
      eapply series_nth_0_in_interval in H; [ idtac | eassumption ].
      unfold series_nth in H.
      destruct (Nbar.lt_dec (fin i) (stop s)); [ assumption | contradiction ].

    symmetry.
    apply null_coeff_range_length_iff in Hp.
    simpl in Hp.
    destruct i.
     rewrite Nat.mod_0_l in H₂; auto.
     exfalso; revert H₂; apply Nat.lt_irrefl.

     pose proof (Hp i) as Hi.
     unfold series_nth in Hi.
     destruct (Nbar.lt_dec (fin (S i)) (stop s)); auto.
     contradiction.

   reflexivity.

 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₂| H₂]; [ idtac | reflexivity ].
 exfalso; apply H₁.
 eapply Nbar.lt_le_trans; [ eassumption | idtac ].
 apply Nbar.le_mul_div_sup.
 subst kn.
 intros H.
 injection H; apply Pos2Nat_ne_0.
Qed.

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

Definition is_the_greatest_series_x_power₂ s b k :=
  match null_coeff_range_length rng s (S b) with
  | fin _ =>
      is_a_series_in_x_power s b k ∧
      (∀ u, (1 < u)%positive
       → ∃ n, ¬(Pos.to_nat (u * k) | nth_null_coeff_range_length s n b))
  | ∞ =>
      k = 1%positive
  end.

Lemma is_the_greatest_series_x_power_equiv : ∀ s b k,
  is_the_greatest_series_x_power s b k
  ↔ is_the_greatest_series_x_power₂ s b k.
Proof.
intros s b k.
split; intros H.
 unfold is_the_greatest_series_x_power in H.
 unfold is_the_greatest_series_x_power₂.
 remember (null_coeff_range_length rng s (S b)) as p eqn:Hp₁ .
 destruct p as [p| ]; [ idtac | assumption ].
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
 unfold is_the_greatest_series_x_power.
 remember (null_coeff_range_length rng s (S b)) as p eqn:Hp₁ .
 destruct p as [p| ]; [ idtac | assumption ].
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

Lemma greatest_series_x_power_stretch : ∀ s b k,
  null_coeff_range_length rng s (S b) ≠ ∞
  → greatest_series_x_power rng (series_stretch k s) (b * Pos.to_nat k) =
      (k * greatest_series_x_power rng s b)%positive.
Proof.
(* à nettoyer *)
intros s b k Hinf.
remember (greatest_series_x_power rng s b) as m eqn:Hm .
symmetry in Hm.
apply greatest_series_x_power_iff.
apply is_the_greatest_series_x_power_equiv.
unfold is_the_greatest_series_x_power₂.
apply greatest_series_x_power_iff in Hm.
unfold is_the_greatest_series_x_power in Hm.
remember (null_coeff_range_length rng s (S b)) as p eqn:Hp .
symmetry in Hp.
destruct p as [p| ].
 apply null_coeff_range_length_stretch_succ with (k := k) in Hp.
 rewrite Hp.
 split.
  intros n.
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
  destruct Hm as (Hm, Hmk).
  assert (m < m * u)%positive as Hmu.
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

 exfalso; apply Hinf; reflexivity.
Qed.

Lemma gcd_ps_is_pos : ∀ n k ps, (0 < gcd_ps n k ps)%Z.
Proof.
intros n k ps.
unfold gcd_ps; simpl.
remember (ps_valnum ps + Z.of_nat n)%Z as x.
rewrite <- Z.gcd_assoc.
remember (Z.gcd (' ps_comden ps) (' k))%Z as y eqn:Hy .
pose proof (Z.gcd_nonneg x y) as Hp.
destruct (Z_zerop (Z.gcd x y)) as [H₁| H₁]; [ idtac | omega ].
apply Z.gcd_eq_0_r in H₁.
rewrite Hy in H₁.
apply Z.gcd_eq_0_r in H₁.
exfalso; revert H₁; apply Pos2Z_ne_0.
Qed.

Lemma series_null_power : ∀ s b p,
  is_a_series_in_x_power s b p
  → ∀ i,
    ((i - b) mod Pos.to_nat p)%nat ≠ O
    → (series_nth rng i s = 0)%rng.
Proof.
intros s b p Hxp i Hip.
destruct (le_dec i b) as [H₁| H₁].
 apply Nat.sub_0_le in H₁.
 rewrite H₁, Nat.mod_0_l in Hip; auto.
 exfalso; apply Hip; reflexivity.

 apply Nat.nle_gt in H₁.
 remember (i - b)%nat as j eqn:Hj .
 replace i with (b + j)%nat in * by omega.
 clear i Hj.
 eapply series_nth_0_in_interval_from_any with (c := S j).
  apply Nat.lt_succ_r; reflexivity.

  eassumption.

  unfold is_a_series_in_x_power in Hxp.
  apply Hxp.

  assumption.
Qed.

Lemma null_coeff_range_length_inf_iff : ∀ ps,
  null_coeff_range_length rng (ps_terms ps) 0 = ∞
  ↔ (ps = 0)%ps.
Proof.
intros ps.
split; intros H.
 constructor.
 unfold canonic_ps; simpl.
 rewrite H.
 remember (null_coeff_range_length rng 0%ser 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ]; [ idtac | reflexivity ].
 apply null_coeff_range_length_iff in Hn.
 simpl in Hn.
 destruct Hn as (_, Hn).
 rewrite series_nth_series_0 in Hn.
 exfalso; apply Hn; reflexivity.

 inversion H; subst.
 apply null_coeff_range_length_iff; simpl; intros i.
 unfold canonic_ps in H0; simpl in H0.
 remember (null_coeff_range_length rng 0%ser 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ].
  exfalso; clear H0.
  apply null_coeff_range_length_iff in Hn.
  simpl in Hn.
  destruct Hn as (_, Hn).
  apply Hn.
  apply series_nth_series_0.

  remember (null_coeff_range_length rng (ps_terms ps) 0) as m eqn:Hm .
  symmetry in Hm.
  destruct m as [m| ].
   Focus 2.
   apply null_coeff_range_length_iff in Hm.
   simpl in Hm.
   apply Hm.

   inversion_clear H0.
   simpl in H1, H2, H3.
   remember (greatest_series_x_power rng (ps_terms ps) m) as p eqn:Hp .
   remember (gcd_ps m p ps) as g eqn:Hg .
   unfold canonify_series in H3.
   inversion_clear H3.
   apply null_coeff_range_length_iff in Hm.
   simpl in Hm.
   destruct Hm as (Hz, Hnz).
   destruct (lt_dec i m) as [H₁| H₁]; [ apply Hz; assumption | idtac ].
   apply Nat.nlt_ge in H₁.
   destruct (zerop ((i - m) mod Z.to_nat g)) as [H₂| H₂].
    apply Nat.mod_divides in H₂.
     destruct H₂ as (c, Hc).
     pose proof (H0 c) as Hi.
     rewrite series_nth_series_0 in Hi.
     rewrite <- series_nth_mul_shrink in Hi.
     rewrite Pos2Nat_to_pos in Hi.
      rewrite <- Hc in Hi.
      rewrite <- series_nth_add_left_shift in Hi.
      rewrite Nat.sub_add in Hi; assumption.

      rewrite Hg; apply gcd_ps_is_pos.

     pose proof (gcd_ps_is_pos m p ps) as H₃.
     rewrite <- Hg in H₃.
     rewrite <- Z2Nat.inj_0.
     intros H₄.
     apply Z2Nat.inj in H₄; [ idtac | idtac | reflexivity ].
      rewrite H₄ in H₃; revert H₃; apply Z.lt_irrefl.

      apply Z.lt_le_incl; assumption.

    symmetry in Hp.
    apply greatest_series_x_power_iff in Hp.
    unfold is_the_greatest_series_x_power in Hp.
    remember (null_coeff_range_length rng (ps_terms ps) (S m)) as q eqn:Hq .
    symmetry in Hq.
    destruct q as [q| ].
     destruct Hp as (Hxp, Hnxp).
     eapply series_null_power; [ eassumption | idtac ].
     apply Nat.sub_gt in H₂; rewrite Nat.sub_0_r in H₂.
     intros H₃; apply H₂; clear H₂.
     pose proof (gcd_ps_is_pos m p ps) as Hgp.
     rewrite <- Hg in Hgp.
     unfold gcd_ps in Hg.
     remember (ps_valnum ps + Z.of_nat m)%Z as x.
     remember (Z.gcd x (' ps_comden ps)) as z.
     pose proof (Z.gcd_divide_r z (Zpos p)) as H₄.
     rewrite <- Hg in H₄.
     apply Nat.mod_divide in H₃; auto.
     apply Nat.mod_divide; auto.
      intros H₅.
      rewrite <- Z2Nat.inj_0 in H₅.
      apply Z2Nat.inj in H₅.
       rewrite H₅ in Hgp; revert Hgp; apply Z.lt_irrefl.

       apply Z.lt_le_incl; assumption.

       reflexivity.

      eapply Nat.divide_trans; [ idtac | eassumption ].
      destruct H₄ as (c, Hc).
      rewrite <- Z2Nat.inj_pos.
      rewrite Hc; simpl.
      exists (Z.to_nat c).
      rewrite Z2Nat.inj_mul.
       reflexivity.

       apply <- Z.mul_le_mono_pos_r; [ idtac | eassumption ].
       rewrite <- Hc; apply Pos2Z.is_nonneg.

       apply Z.lt_le_incl; assumption.

     subst p.
     unfold gcd_ps in Hg.
     rewrite Z.gcd_1_r in Hg.
     subst g.
     rewrite Nat.mod_1_r in H₂.
     exfalso; revert H₂; apply Nat.lt_irrefl.
Qed.

(*
Definition cm ps₁ ps₂ := Plcm (ps_comden ps₁) (ps_comden ps₂).
Definition cm_factor α (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (ps_comden ps₁) (ps_comden ps₂) in
  Pos.of_nat (Pos.to_nat l / Pos.to_nat (ps_comden ps₁))%nat.
*)
Definition cm (ps₁ ps₂ : puiseux_series α) :=
  (ps_comden ps₁ * ps_comden ps₂)%positive.
Definition cm_factor α (ps₁ ps₂ : puiseux_series α) :=
  ps_comden ps₂.
(**)

Lemma eq_strong_eq : ∀ ps₁ ps₂, ps₁ ≐ ps₂ → (ps₁ = ps₂)%ps.
Proof.
intros ps₁ ps₂ Heq.
constructor.
rewrite Heq.
reflexivity.
Qed.

Add Parametric Morphism : (@mkps α)
  with signature eq_series ==> eq ==> eq ==> eq_ps
  as mkps_morphism.
Proof.
intros a b Hab v n.
constructor; rewrite Hab; reflexivity.
Qed.
