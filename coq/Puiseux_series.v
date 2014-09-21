(* Puiseux_series.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Nbar.
Require Import Field.
Require Import Power_series.

Set Implicit Arguments.

(* ps_terms: power series (in x^(1/ps_polord))
   ps_ordnum: order numerator
   ps_polord: polydromy order (common denominator) *)
Record puiseux_series α := mkps
  { ps_terms : power_series α;
    ps_ordnum : Z;
    ps_polord : positive }.

Arguments mkps α%type ps_terms%ser ps_ordnum%Z ps_polord%positive.
Delimit Scope ps_scope with ps.

Arguments ps_terms α%type p%ps.
Arguments ps_ordnum α%type p%ps.
Arguments ps_polord α%type p%ps.

Section Axioms.

(* [null_coeff_range_length fld s n] returns the number of consecutive
   null coefficients in the series [s], starting from the [n]th one. *)
Definition null_coeff_range_length : ∀ α,
  ring α → power_series α → nat → Nbar.
Admitted.

Arguments null_coeff_range_length _ _ s%ser _.

Definition null_coeff_range_length_prop α {R : ring α} s n v :=
  match v with
  | fin k =>
      (∀ i : nat, (i < k)%nat → (s .[n + i] = 0)%K)
      ∧ (s .[n + k] ≠ 0)%K
  | ∞ =>
      ∀ i : nat, (s .[n + i] = 0)%K
  end.

Axiom null_coeff_range_length_iff : ∀ α (r : ring α) s n v,
  null_coeff_range_length r s n = v ↔ null_coeff_range_length_prop s n v.

(* [greatest_series_x_power fld s n] returns the greatest nat value [k]
   such that [s], starting at index [n], is a series in [x^k]. *)
Definition greatest_series_x_power : ∀ α,
  ring α → power_series α → nat → nat.
Admitted.

Fixpoint nth_null_coeff_range_length α (r : ring α) s n b :=
  match null_coeff_range_length r s (S b) with
  | fin p =>
      match n with
      | O => S p
      | S n₁ => nth_null_coeff_range_length r s n₁ (S b + p)%nat
      end
  | ∞ => O
  end.

Definition is_a_series_in_x_power α {R : ring α} s b k :=
  ∀ n, (k | nth_null_coeff_range_length R s n b).

Definition is_the_greatest_series_x_power α {R : ring α} s b k :=
  match null_coeff_range_length R s (S b) with
  | fin _ =>
      is_a_series_in_x_power s b k ∧
      (∀ k', (k < k')%nat → ∃ n, ¬(k' | nth_null_coeff_range_length R s n b))
  | ∞ =>
      k = O
  end.

Axiom greatest_series_x_power_iff : ∀ α (r : ring α) s n k,
  greatest_series_x_power r s n = k ↔
  is_the_greatest_series_x_power s n k.

End Axioms.

Definition series_stretch α {R : ring α} k s :=
  {| terms i :=
       if zerop (i mod Pos.to_nat k) then s .[i / Pos.to_nat k]
       else rng_zero |}.

Definition series_shift α {R : ring α} n s :=
  {| terms i := if lt_dec i n then rng_zero else s .[i - n] |}.

Definition series_shrink α k (s : power_series α) :=
  {| terms i := s.[i * Pos.to_nat k] |}.

Definition series_left_shift α n (s : power_series α) :=
  {| terms i := s.[n + i] |}.

Arguments series_stretch α%type _ k%positive s%ser.
Arguments series_shift α%type _ n%nat s%ser.
Arguments series_shrink α%type k%positive s%ser.
Arguments series_left_shift α%type n%nat s%ser.

Definition normalise_series α n k (s : power_series α) :=
  series_shrink k (series_left_shift n s).

Definition gcd_ps α n k (ps : puiseux_series α) :=
  Z.gcd (Z.gcd (ps_ordnum ps + Z.of_nat n) (' ps_polord ps)) (Z.of_nat k).

Definition ps_zero {α} {r : ring α} :=
  {| ps_terms := 0%ser; ps_ordnum := 0; ps_polord := 1 |}.

Definition normalise_ps α {R : ring α} ps :=
  match null_coeff_range_length R (ps_terms ps) 0 with
  | fin n =>
      let k := greatest_series_x_power R (ps_terms ps) n in
      let g := gcd_ps n k ps in
      {| ps_terms := normalise_series n (Z.to_pos g) (ps_terms ps);
         ps_ordnum := (ps_ordnum ps + Z.of_nat n) / g;
         ps_polord := Z.to_pos (' ps_polord ps / g) |}
  | ∞ =>
      ps_zero
  end.

Arguments normalise_ps _ _ ps%ps.

Inductive eq_ps_strong {α} {r : ring α} :
  puiseux_series α → puiseux_series α → Prop :=
  | eq_strong_base : ∀ ps₁ ps₂,
      ps_ordnum ps₁ = ps_ordnum ps₂
      → ps_polord ps₁ = ps_polord ps₂
        → eq_series (ps_terms ps₁) (ps_terms ps₂)
          → eq_ps_strong ps₁ ps₂.

Inductive eq_ps {α} {r : ring α} :
  puiseux_series α → puiseux_series α → Prop :=
  | eq_ps_base : ∀ ps₁ ps₂,
      eq_ps_strong (normalise_ps ps₁) (normalise_ps ps₂)
      → eq_ps ps₁ ps₂.
Arguments eq_ps _ _ ps₁%ps ps₂%ps.

Definition ps_monom {α} {r : ring α} (c : α) pow :=
  {| ps_terms := {| terms i := if zerop i then c else 0%K |};
     ps_ordnum := Qnum pow;
     ps_polord := Qden pow |}.

Definition ps_one {α} {r : ring α} := ps_monom rng_one 0.

Notation "a ≐ b" := (eq_ps_strong a b) (at level 70, r at level 0).
Notation "a = b" := (eq_ps a b) : ps_scope.
Notation "a ≠ b" := (not (eq_ps a b)) : ps_scope.
Notation "0" := ps_zero : ps_scope.
Notation "1" := ps_one : ps_scope.

Theorem series_stretch_1 : ∀ α (r : ring α) s, (series_stretch 1 s = s)%ser.
Proof.
intros α r s.
unfold series_stretch; simpl.
constructor; intros i; simpl.
rewrite divmod_div, Nat.div_1_r; reflexivity.
Qed.

Theorem eq_strong_refl α (r : ring α) : reflexive _ eq_ps_strong.
Proof. intros ps. constructor; reflexivity. Qed.

Theorem eq_strong_sym α (r : ring α) : symmetric _ eq_ps_strong.
Proof. intros ps₁ ps₂ H; induction H; constructor; symmetry; assumption. Qed.

Theorem eq_strong_trans α (r : ring α) : transitive _ eq_ps_strong.
Proof.
intros ps₁ ps₂ ps₃ H₁ H₂.
induction H₁, H₂.
constructor; etransitivity; eassumption.
Qed.

Add Parametric Relation α (r : ring α) : (puiseux_series α) eq_ps_strong
 reflexivity proved by (eq_strong_refl r)
 symmetry proved by (eq_strong_sym (r := r))
 transitivity proved by (eq_strong_trans (r := r))
 as eq_strong_rel.

Add Parametric Morphism α (r : ring α) : (@mkps α)
  with signature eq_series ==> eq ==> eq ==> eq_ps_strong
  as mkps_strong_eq_morphism.
Proof.
intros a b Hab v n.
constructor; [ reflexivity | reflexivity | assumption ].
Qed.

Add Parametric Morphism α (r : ring α) : (null_coeff_range_length r)
  with signature eq_series ==> eq ==> eq
  as null_coeff_range_length_morph.
Proof.
intros s₁ s₂ Heq n.
remember (null_coeff_range_length r s₁ n) as n₁ eqn:Hn₁ .
remember (null_coeff_range_length r s₂ n) as n₂ eqn:Hn₂ .
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

Add Parametric Morphism α (r : ring α) : (nth_null_coeff_range_length r)
  with signature eq_series ==> eq ==> eq ==> eq
  as nth_null_coeff_range_length_morph.
Proof.
intros s₁ s₂ Heq c n.
revert n.
induction c; intros; simpl; rewrite Heq; [ reflexivity | idtac ].
destruct (null_coeff_range_length r s₂ (S n)); [ apply IHc | reflexivity ].
Qed.

Add Parametric Morphism α (r : ring α) : (greatest_series_x_power r)
  with signature eq_series ==> eq ==> eq
  as greatest_series_x_power_morph.
Proof.
intros s₁ s₂ Heq n.
remember (greatest_series_x_power r s₂ n) as k eqn:Hk .
symmetry in Hk.
apply greatest_series_x_power_iff in Hk.
apply greatest_series_x_power_iff.
unfold is_the_greatest_series_x_power in Hk |- *.
remember (null_coeff_range_length r s₁ (S n)) as p₁ eqn:Hp₁ .
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

Add Parametric Morphism α (R : ring α) : (@series_stretch _ R)
  with signature eq ==> eq_series ==> eq_series
  as stretch_morph.
Proof.
intros kp s₁ s₂ Heq.
inversion Heq; subst.
constructor; intros i; simpl.
remember (Pos.to_nat kp) as k.
assert (k ≠ O) as Hk by (subst k; apply Pos2Nat_ne_0).
destruct (zerop (i mod k)) as [Hz| Hnz]; [ idtac | reflexivity ].
apply Nat.mod_divides in Hz; [ idtac | assumption ].
destruct Hz as (c, Hi).
subst i.
pose proof (H c) as Hc.
rewrite Nat.mul_comm.
rewrite Nat.div_mul; assumption.
Qed.

Add Parametric Morphism α (r : ring α) : (@series_shrink α)
  with signature eq ==> eq_series ==> eq_series
  as shrink_morph.
Proof.
intros n s₁ s₂ Heq.
constructor; intros; simpl.
inversion Heq; subst.
apply H.
Qed.

Add Parametric Morphism α (R : ring α) : (@series_shift _ R)
  with signature eq ==> eq_series ==> eq_series
  as series_shift_morph.
Proof.
intros n s₁ s₂ Heq.
constructor; intros i.
inversion Heq; subst; simpl.
destruct (lt_dec i n); [ reflexivity | apply H ].
Qed.

Add Parametric Morphism α (r : ring α) : (@normalise_series α)
  with signature eq ==> eq ==> eq_series ==> eq_series
  as normalise_series_morph.
Proof.
intros n k ps₁ ps₂ Heq.
constructor; intros i.
inversion Heq; subst.
unfold normalise_series.
unfold series_shrink, series_left_shift; simpl.
apply H.
Qed.

Add Parametric Morphism α (R : ring α) : (@normalise_ps _ R)
  with signature eq_ps_strong ==> eq_ps_strong
  as normalise_ps_morph.
Proof.
intros ps₁ ps₂ Heq.
inversion Heq; subst.
unfold normalise_ps.
rewrite H, H0, H1.
remember (null_coeff_range_length R (ps_terms ps₂) 0) as n eqn:Hn .
symmetry in Hn.
destruct n as [n| ]; [ idtac | reflexivity ].
unfold gcd_ps.
rewrite H, H0.
constructor; simpl; rewrite H1; reflexivity.
Qed.

Add Parametric Morphism α (r : ring α) : (@mkps α)
  with signature eq_series ==> eq ==> eq ==> eq_ps
  as mkps_morphism.
Proof.
intros a b Hab v n.
constructor; rewrite Hab; reflexivity.
Qed.

Section eq_ps_equiv_rel.

Variable α : Type.
Variable r : ring α.

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

Theorem series_stretch_stretch : ∀ a b s,
  (series_stretch (a * b) s =
   series_stretch a (series_stretch b s))%ser.
Proof.
intros ap bp s.
unfold series_stretch; simpl.
constructor; intros i; simpl.
rewrite Pos2Nat.inj_mul.
remember (Pos.to_nat ap) as a.
remember (Pos.to_nat bp) as b.
assert (a ≠ O) as Ha by (subst a; apply Pos2Nat_ne_0).
assert (b ≠ O) as Hb by (subst b; apply Pos2Nat_ne_0).
destruct (zerop (i mod (a * b))) as [Hz| Hnz].
 apply Nat.mod_divides in Hz.
  destruct Hz as (c, Hz).
  subst i.
  rewrite Nat.mul_comm, Nat.div_mul.
   rewrite Nat.mul_assoc, Nat.mul_shuffle0.
   rewrite Nat.mod_mul; [ simpl | assumption ].
   rewrite Nat.div_mul; [ simpl | assumption ].
   rewrite Nat.mod_mul; [ simpl | assumption ].
   rewrite Nat.div_mul; [ simpl | assumption ].
   reflexivity.

   apply Nat.neq_mul_0; split; assumption.

  apply Nat.neq_mul_0; split; assumption.

 destruct (zerop (i mod a)) as [Hz| ]; [ idtac | reflexivity ].
 apply Nat.mod_divides in Hz; [ idtac | assumption ].
 destruct Hz as (c, Hz).
 subst i.
 rewrite Nat.mul_comm, Nat.div_mul; [ idtac | assumption ].
 destruct (zerop (c mod b)) as [Hlt₂| ]; [ idtac | reflexivity ].
 apply Nat.mod_divides in Hlt₂; [ idtac | assumption ].
 destruct Hlt₂ as (c₂, Hlt₂).
 subst c.
 rewrite Nat.mul_assoc, Nat.mul_comm in Hnz.
 rewrite Nat.mod_mul in Hnz.
  exfalso; revert Hnz; apply lt_irrefl.

  apply Nat.neq_mul_0; split; assumption.
Qed.

Theorem series_shift_series_0 : ∀ n, (series_shift n 0 = 0)%ser.
Proof.
intros n.
constructor; intros i; simpl.
destruct (lt_dec i n); reflexivity.
Qed.

Theorem series_stretch_series_0 : ∀ k, (series_stretch k 0 = 0)%ser.
Proof.
intros k.
constructor; intros i; simpl.
destruct (zerop (i mod Pos.to_nat k)); [ idtac | reflexivity ].
destruct (Nbar.lt_dec (fin (i / Pos.to_nat k)) 0); reflexivity.
Qed.

Theorem stretch_shift_series_distr : ∀ kp n s,
  (series_stretch kp (series_shift n s) =
   series_shift (n * Pos.to_nat kp) (series_stretch kp s))%ser.
Proof.
intros kp n s.
constructor; intros i; simpl.
remember (Pos.to_nat kp) as k.
assert (k ≠ O) as Hk by (subst k; apply Pos2Nat_ne_0).
destruct (zerop (i mod k)) as [Hz| Hnz].
 apply Nat.mod_divides in Hz; [ idtac | assumption ].
 destruct Hz as (c, Hi); subst i.
 rewrite mult_comm.
 rewrite <- Nat.mul_sub_distr_r.
 rewrite Nat.div_mul; [ idtac | assumption ].
 rewrite Nat.div_mul; [ idtac | assumption ].
 rewrite Nat.mod_mul; [ simpl | assumption ].
 destruct (lt_dec c n) as [H₁| H₁].
  destruct (lt_dec (c * k) (n * k)) as [| H₂]; [ reflexivity | idtac ].
  exfalso; apply H₂.
  apply Nat.mul_lt_mono_pos_r; [ idtac | assumption ].
  rewrite Heqk; apply Pos2Nat.is_pos.

  destruct (lt_dec (c * k) (n * k)) as [H₂| ]; [ idtac | reflexivity ].
  exfalso; apply H₁.
  apply Nat.mul_lt_mono_pos_r in H₂; [ assumption | idtac ].
  rewrite Heqk; apply Pos2Nat.is_pos.

 destruct (lt_dec i (n * k)) as [| H₁]; [ reflexivity | idtac ].
 destruct (zerop ((i - n * k) mod k)) as [H₂| ]; [ idtac | reflexivity ].
 apply Nat.mod_divides in H₂; [ idtac | assumption ].
 destruct H₂ as (c, Hc).
 destruct c.
  rewrite Nat.mul_0_r in Hc.
  apply Nat.sub_0_le in Hc.
  apply Nat.nlt_ge in H₁.
  apply le_antisym in Hc; [ idtac | assumption ].
  subst i.
  rewrite Nat.mod_mul in Hnz; [ idtac | assumption ].
  exfalso; revert Hnz; apply Nat.lt_irrefl.

  apply Nat.add_sub_eq_nz in Hc.
   rewrite Nat.mul_comm, <- Nat.mul_add_distr_l, Nat.mul_comm in Hc.
   subst i.
   rewrite Nat.mod_mul in Hnz; [ idtac | assumption ].
   exfalso; revert Hnz; apply Nat.lt_irrefl.

   apply Nat.neq_mul_0.
   split; [ assumption | idtac ].
   intros H; discriminate H.
Qed.

Theorem series_shift_shift : ∀ x y ps,
  (series_shift x (series_shift y ps) = series_shift (x + y) ps)%ser.
Proof.
intros x y ps.
constructor; intros i; simpl.
destruct (lt_dec i x) as [Hlt| Hge].
 destruct (lt_dec i (x + y)) as [| H₂]; [ reflexivity | idtac ].
 exfalso; apply H₂.
 apply Nat.lt_lt_add_r; assumption.

 destruct (lt_dec (i - x) y) as [H₂| H₂].
  destruct (lt_dec i (x + y)) as [| H₃]; [ reflexivity | idtac ].
  exfalso; apply H₃.
  apply Nat.lt_sub_lt_add_l; assumption.

  rewrite Nat.sub_add_distr.
  destruct (lt_dec i (x + y)) as [H₃| ]; [ idtac | reflexivity ].
  exfalso; apply H₂.
  apply not_gt in Hge.
  unfold lt.
  rewrite <- Nat.sub_succ_l; [ idtac | assumption ].
  apply Nat.le_sub_le_add_l.
  assumption.
Qed.

Theorem series_shift_left_shift : ∀ s n,
  null_coeff_range_length r s 0 = fin n
  → (series_shift n (series_left_shift n s) = s)%ser.
Proof.
intros s n Hn.
apply null_coeff_range_length_iff in Hn.
simpl in Hn.
destruct Hn as (Hz, Hnz).
constructor; intros i; simpl.
destruct (lt_dec i n) as [H₁| H₁].
 apply Hz in H₁.
 symmetry; assumption.

 apply Nat.nlt_ge in H₁.
 rewrite Nat.add_sub_assoc; [ idtac | assumption ].
 rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Theorem series_left_shift_shift : ∀ s n m,
  (m ≤ n)%nat
  → (series_left_shift n (series_shift m s) =
     series_left_shift (n - m) s)%ser.
Proof.
intros s n m Hmn.
constructor; intros i; simpl.
destruct (lt_dec (n + i) m) as [H₁| H₁].
 apply Nat.nle_gt in H₁.
 exfalso; apply H₁.
 transitivity n; [ assumption | apply Nat.le_add_r ].

 apply Nat.nlt_ge in H₁.
 rewrite Nat.add_sub_swap; [ reflexivity | assumption ].
Qed.

Theorem series_left_shift_stretch : ∀ s n k,
  (series_left_shift (n * Pos.to_nat k) (series_stretch k s) =
   series_stretch k (series_left_shift n s))%ser.
Proof.
intros s n k.
constructor; intros i; simpl.
rewrite Nat.add_comm.
rewrite Nat.mod_add; auto.
rewrite Nat.div_add; auto.
destruct (zerop (i mod Pos.to_nat k)) as [H₂| H₂]; [ idtac | reflexivity ].
rewrite Nat.add_comm; reflexivity.
Qed.

Theorem eq_ps_trans : transitive _ eq_ps.
Proof.
intros ps₁ ps₂ ps₃ H₁ H₂.
induction H₁.
inversion H₂; subst.
constructor; etransitivity; eassumption.
Qed.

End eq_ps_equiv_rel.

Add Parametric Relation α (r : ring α) : (puiseux_series α) eq_ps
 reflexivity proved by (eq_ps_refl r)
 symmetry proved by (eq_ps_sym (r := r))
 transitivity proved by (eq_ps_trans (r := r))
 as eq_ps_rel.

Section other_theorems.

Variable α : Type.
Variable r : ring α.

Theorem ps_zero_monom_eq : (ps_monom 0%K 0 = 0)%ps.
Proof.
unfold ps_zero, ps_monom; simpl.
apply mkps_morphism; try reflexivity.
constructor; intros n; simpl.
destruct (zerop n); reflexivity.
Qed.

Theorem series_shift_0 : ∀ s, (series_shift 0 s = s)%ser.
Proof.
intros s.
constructor; intros i; simpl.
rewrite Nat.sub_0_r; reflexivity.
Qed.

Theorem series_left_shift_0 : ∀ s, (series_left_shift 0 s = s)%ser.
Proof.
intros s.
constructor; intros i; simpl.
reflexivity.
Qed.

Theorem series_nth_shift_S : ∀ s n i,
  (series_shift n s) .[i] = (series_shift (S n) s) .[S i].
Proof.
intros s n i; simpl.
destruct (lt_dec i n) as [H₁| H₁].
 destruct (lt_dec (S i) (S n)) as [| H₂]; [ reflexivity | idtac ].
 apply Nat.succ_lt_mono in H₁; contradiction.

 destruct (lt_dec (S i) (S n)) as [H₂| ]; [ idtac | reflexivity ].
 apply Nat.succ_lt_mono in H₂; contradiction.
Qed.

Theorem null_coeff_range_length_shift_S : ∀ s c n,
  (c ≤ n)%nat
  → null_coeff_range_length r (series_shift (S n) s) c =
    NS (null_coeff_range_length r (series_shift n s) c).
Proof.
intros s c n Hcn.
remember (null_coeff_range_length r (series_shift n s) c) as u eqn:Hu .
remember (null_coeff_range_length r (series_shift (S n) s) c) as v eqn:Hv .
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
    simpl in Hv.
    exfalso.
    rewrite Nat.add_0_r in Hv.
    destruct (lt_dec c (S n)) as [H₂| H₂].
     apply Hv; reflexivity.

     apply H₂.
     apply Nat.succ_le_mono in Hcn; assumption.

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
  rewrite Nat.add_0_r in Hv.
  exfalso.
  simpl in Hv.
  destruct (lt_dec c (S n)) as [H₂| H₂].
   apply Hv; reflexivity.

   apply H₂.
   apply Nat.succ_le_mono in Hcn; assumption.

  rewrite Nat.add_succ_r in Hv.
  rewrite <- series_nth_shift_S in Hv.
  exfalso; apply Hv, Hu.
Qed.

Theorem null_coeff_range_length_shift : ∀ s n,
  null_coeff_range_length r (series_shift n s) 0 =
    (fin n + null_coeff_range_length r s 0)%Nbar.
Proof.
intros s n.
induction n.
 rewrite series_shift_0, Nbar.add_0_l; reflexivity.

 rewrite null_coeff_range_length_shift_S; [ idtac | apply Nat.le_0_l ].
 rewrite IHn; simpl.
 destruct (null_coeff_range_length r s); reflexivity.
Qed.

Theorem shifted_in_stretched : ∀ s k i,
  (0 < i mod Pos.to_nat k)%nat
  → (series_stretch k s) .[i] = 0%K.
Proof.
intros s k i Hi; simpl.
destruct (zerop (i mod Pos.to_nat k)) as [Hz| ]; [ idtac | reflexivity ].
exfalso; revert Hi; rewrite Hz; apply Nat.lt_irrefl.
Qed.

Theorem series_stretch_const : ∀ k c,
  (series_stretch k (series_const c) = series_const c)%ser.
Proof.
intros k c.
constructor; intros i; simpl.
destruct (zerop (i mod Pos.to_nat k)) as [H| H].
 apply Nat.mod_divides in H; auto.
 destruct H as (d, Hd); rewrite Hd.
 rewrite Nat.mul_comm.
 rewrite Nat.div_mul; auto.
 destruct d; [ reflexivity | idtac ].
 rewrite Nat.mul_comm; simpl.
 rewrite <- Hd.
 destruct i; [ idtac | reflexivity ].
 symmetry in Hd.
 apply Nat.mul_eq_0_r in Hd; auto; discriminate Hd.

 destruct i; [ simpl | reflexivity ].
 rewrite Nat.mod_0_l in H; auto.
 exfalso; revert H; apply Nat.lt_irrefl.
Qed.

Theorem stretch_series_1 : ∀ k, (series_stretch k 1 = 1)%ser.
Proof.
intros k.
apply series_stretch_const.
Qed.

Theorem series_nth_mul_stretch : ∀ s k i,
  (series_stretch k s) .[Pos.to_nat k * i] = s .[i].
Proof.
intros s k i; simpl.
rewrite Nat.mul_comm.
rewrite Nat.mod_mul; [ simpl | apply Pos2Nat_ne_0 ].
rewrite Nat.div_mul; [ simpl | apply Pos2Nat_ne_0 ].
reflexivity.
Qed.

Theorem series_nth_mul_shrink : ∀ (s : power_series α) k i,
  s .[Pos.to_nat k * i] = (series_shrink k s) .[i].
Proof.
intros s k i; simpl.
rewrite Nat.mul_comm; reflexivity.
Qed.

Theorem stretch_finite_series : ∀ s b k,
  (∀ i, (s .[b + i] = 0)%K)
  → ∀ i, ((series_stretch k s) .[b * Pos.to_nat k + i] = 0)%K.
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

Theorem null_coeff_range_length_stretch : ∀ s b k,
  null_coeff_range_length r (series_stretch k s) (b * Pos.to_nat k) =
    (fin (Pos.to_nat k) * null_coeff_range_length r s b)%Nbar.
Proof.
intros s b k.
remember (null_coeff_range_length r s b) as n eqn:Hn .
symmetry in Hn.
apply null_coeff_range_length_iff in Hn.
apply null_coeff_range_length_iff.
rewrite Nbar.mul_comm.
destruct n as [n| ]; simpl.
 destruct Hn as (Hz, Hnz).
 split.
  intros i Hin.
  rewrite Nat.add_comm.
  rewrite Nat.mod_add; auto.
  rewrite Nat.div_add; auto.
  destruct (zerop (i mod Pos.to_nat k)) as [H₁| ]; [ idtac | reflexivity ].
  apply Nat.mod_divides in H₁; [ idtac | apply Pos2Nat_ne_0 ].
  destruct H₁ as (c, H₁).
  rewrite H₁.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; auto.
  rewrite Nat.add_comm.
  apply Hz.
  rewrite H₁ in Hin.
  rewrite Nat.mul_comm in Hin.
  apply Nat.mul_lt_mono_pos_r in Hin; auto.

  rewrite <- Nat.mul_add_distr_r.
  rewrite Nat.mod_mul; auto; simpl.
  rewrite Nat.div_mul; auto.

 intros i.
 apply stretch_finite_series; assumption.
Qed.

Theorem null_coeff_range_length_stretch_0 : ∀ s k,
  null_coeff_range_length r (series_stretch k s) 0 =
    (fin (Pos.to_nat k) * null_coeff_range_length r s 0)%Nbar.
Proof.
intros s k.
rewrite <- null_coeff_range_length_stretch.
rewrite Nat.mul_0_l; reflexivity.
Qed.

Theorem series_nth_add_shift : ∀ s i n,
  (series_shift n s) .[i + n] = s .[i].
Proof.
intros s i n; simpl.
rewrite Nat.add_sub.
destruct (lt_dec (i + n) n) as [H| H]; [ idtac | reflexivity ].
apply Nat.lt_add_lt_sub_r in H.
rewrite Nat.sub_diag in H.
exfalso; revert H; apply Nat.nlt_0_r.
Qed.

Theorem series_nth_add_left_shift : ∀ (s : power_series α) i n,
  s .[i + n] = (series_left_shift n s) .[i].
Proof.
intros s i n; simpl.
rewrite Nat.add_comm; reflexivity.
Qed.

Theorem null_coeff_range_length_shift_add : ∀ s m n,
  null_coeff_range_length r (series_shift m s) (m + n) =
  null_coeff_range_length r s n.
Proof.
intros s m n.
remember (null_coeff_range_length r s n) as v eqn:Hv .
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

Theorem nth_null_coeff_range_length_shift : ∀ s cnt n b,
  nth_null_coeff_range_length r (series_shift n s) cnt (b + n) =
  nth_null_coeff_range_length r s cnt b.
Proof.
intros s cnt n b.
revert b.
induction cnt; intros; simpl.
 rewrite <- Nat.add_succ_l, Nat.add_comm.
 rewrite null_coeff_range_length_shift_add.
 destruct (null_coeff_range_length r s (S b)); reflexivity.

 rewrite <- Nat.add_succ_l, Nat.add_comm.
 rewrite null_coeff_range_length_shift_add.
 remember (null_coeff_range_length r s (S b)) as m eqn:Hm .
 symmetry in Hm.
 destruct m as [m| ]; [ idtac | reflexivity ].
 rewrite Nat.add_shuffle0.
 rewrite <- Nat.add_succ_l.
 apply IHcnt.
Qed.

Theorem greatest_series_x_power_shift : ∀ n s b,
  greatest_series_x_power r (series_shift n s) (b + n) =
  greatest_series_x_power r s b.
Proof.
intros n s b.
remember (greatest_series_x_power r s b) as k eqn:Hk .
symmetry in Hk.
apply greatest_series_x_power_iff in Hk.
apply greatest_series_x_power_iff.
unfold is_the_greatest_series_x_power in Hk |- *.
rewrite <- Nat.add_succ_l, Nat.add_comm.
rewrite null_coeff_range_length_shift_add.
remember (null_coeff_range_length r s (S b)) as p eqn:Hp .
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

Theorem null_coeff_range_length_stretch_succ : ∀ s n p k,
  null_coeff_range_length r s (S n) = fin p
  → null_coeff_range_length r (series_stretch k s)
      (S (n * Pos.to_nat k)) = fin (S p * Pos.to_nat k - 1).
Proof.
(* à nettoyer *)
intros s n p k Hp.
remember (series_stretch k s) as s₁ eqn:Hs₁ .
remember (null_coeff_range_length r s₁ (S (n * Pos.to_nat k))) as q eqn:Hq .
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

      assert (p < S p)%nat as H by apply Nat.lt_succ_diag_r.
      apply Hzp in H.
      rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
      rewrite H in Hnzq; apply Hnzq; reflexivity.

     remember H₁ as H; clear HeqH.
     apply le_S_n, le_neq_lt in H; auto.
     destruct q' as [| q'].
      rewrite Nat.mul_0_r in Hq'; discriminate Hq'.

      apply lt_S_n in H₁.
      apply Hzp in H₁.
      rewrite Nat.add_succ_l, <- Nat.add_succ_r in H₁.
      rewrite H₁ in Hnzq; apply Hnzq; reflexivity.

    assumption.

    exfalso.
    assert (Pos.to_nat k * S p - 1 < q)%nat as H.
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

   subst q'.
   rewrite Nat.mul_comm.
   rewrite <- Hq'.
   simpl.
   rewrite Nat.sub_0_r; reflexivity.

  assert (0 < (n * Pos.to_nat k + S q) mod Pos.to_nat k)%nat as H.
   rewrite Nat.add_comm.
   rewrite Nat.mod_add; [ idtac | apply Pos2Nat_ne_0 ].
   assumption.

   apply shifted_in_stretched with (s := s) in H.
   rewrite <- Hs₁ in H.
   rewrite H in Hnzq.
   exfalso; apply Hnzq; reflexivity.

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

Theorem null_coeff_range_length_stretch_succ_inf : ∀ s n k,
  null_coeff_range_length r s (S n) = ∞
  → null_coeff_range_length r (series_stretch k s) (S (n * Pos.to_nat k)) =
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
 eapply Nat.add_sub_assoc in H; symmetry in H.
 rewrite Nat.add_comm, Nat.add_sub in H; rewrite H.
 rewrite Nat.add_assoc, Nat.mul_comm.
 rewrite <- Nat.mul_succ_r, Nat.mul_comm.
 apply stretch_finite_series.
 assumption.
Qed.

Theorem series_shrink_shrink : ∀ (s : power_series α) k₁ k₂,
  (series_shrink (k₁ * k₂) s =
   series_shrink k₁ (series_shrink k₂ s))%ser.
Proof.
intros s k₁ k₂.
constructor; intros i; simpl.
rewrite Pos2Nat.inj_mul, Nat.mul_assoc; reflexivity.
Qed.

Theorem series_shrink_stretch : ∀ s k,
  (series_shrink k (series_stretch k s) = s)%ser.
Proof.
intros s k.
constructor; intros i; simpl.
rewrite Nat.mod_mul; auto; simpl.
rewrite Nat.div_mul; auto; reflexivity.
Qed.

Fixpoint rank_of_nonzero_after_from s n i b :=
  match n with
  | O => O
  | S n₁ =>
      if lt_dec b i then
        match null_coeff_range_length r s (S b) with
        | fin m => S (rank_of_nonzero_after_from s n₁ i (S b + m)%nat)
        | ∞ => O
        end
      else O
  end.

Definition rank_of_nonzero_before s i :=
  pred (rank_of_nonzero_after_from s (S i) i 0).

Theorem series_nth_0_in_interval_from_any : ∀ s i c b k,
  (i < c)%nat
  → (∀ n, (Pos.to_nat k | nth_null_coeff_range_length r s n b)%nat)
    → (Pos.to_nat k |
       nth_null_coeff_range_length r s
         (pred (rank_of_nonzero_after_from s c (b + i) b)) b)%nat
      → i mod Pos.to_nat k ≠ O
        → (s .[b + i] = 0)%K.
Proof.
intros s i c b k Hic Has Hs Hm.
remember (pred (rank_of_nonzero_after_from s c (b + i) b)) as n eqn:Hn .
symmetry in Hn.
destruct c; [ exfalso; revert Hic; apply Nat.nlt_0_r | simpl in Hn ].
destruct i.
 rewrite Nat.mod_0_l in Hm; [ idtac | apply Pos2Nat_ne_0 ].
 exfalso; apply Hm; reflexivity.

 apply Nat.succ_lt_mono in Hic.
 destruct (lt_dec b (b + S i)) as [H₁| H₁].
  clear H₁.
  remember (null_coeff_range_length r s (S b)) as len eqn:Hlen .
  symmetry in Hlen.
  destruct len as [len| ].
   simpl in Hn.
   revert i b len n Has Hic Hlen Hn Hs Hm.
   induction c; intros; [ exfalso; revert Hic; apply Nat.nlt_0_r | idtac ].
   simpl in Hn.
   destruct (lt_dec (S (b + len)) (b + S i)) as [H₁| H₁].
    rewrite Nat.add_succ_r in H₁.
    apply Nat.succ_lt_mono in H₁.
    apply Nat.add_lt_mono_l in H₁.
    remember (null_coeff_range_length r s (S (S (b + len)))) as len₁.
    rename Heqlen₁ into Hlen₁.
    symmetry in Hlen₁.
    destruct len₁ as [len₁| ].
     destruct n; [ discriminate Hn | idtac ].
     apply Nat.succ_inj in Hn.
     destruct i; [ exfalso; revert H₁; apply Nat.nlt_0_r | idtac ].
     apply Nat.succ_lt_mono in Hic.
     apply Nat.succ_le_mono in H₁.
     replace (b + S (S i))%nat with (S (b + len) + S (i - len))%nat .
      eapply IHc; try eassumption.
       intros m.
       pose proof (Has (S m)) as H; simpl in H.
       rewrite Hlen in H; assumption.

       eapply Nat.le_lt_trans; [ apply Nat.le_sub_l | auto ].

       replace (S (b + len) + S (i - len))%nat with (b + S (S i))%nat .
        simpl; apply Hn.

        simpl.
        do 3 rewrite Nat.add_succ_r.
        do 2 apply Nat.succ_inj_wd.
        rewrite <- Nat.add_assoc.
        apply Nat.add_cancel_l.
        rewrite Nat.add_comm.
        rewrite Nat.sub_add; [ reflexivity | assumption ].

       simpl in Hs.
       rewrite Hlen in Hs; assumption.

       replace (S (S i)) with (S (i - len) + S len)%nat in Hm .
        pose proof (Has O) as H; simpl in H.
        rewrite Hlen in H.
        rewrite Nat.add_mod in Hm; auto.
        destruct H as (c₁, Hc₁).
        rewrite Hc₁ in Hm.
        rewrite Nat.mod_mul, Nat.add_0_r in Hm; auto.
        rewrite Nat.mod_mod in Hm; auto.

        rewrite Nat.add_succ_l, Nat.add_succ_r.
        do 2 apply Nat.succ_inj_wd.
        rewrite Nat.sub_add; [ reflexivity | assumption ].

      do 3 rewrite Nat.add_succ_r.
      rewrite Nat.add_succ_l.
      do 2 apply Nat.succ_inj_wd.
      rewrite <- Nat.add_assoc.
      apply Nat.add_cancel_l.
      rewrite Nat.add_comm.
      rewrite Nat.sub_add; [ reflexivity | assumption ].

     apply null_coeff_range_length_iff in Hlen₁; simpl in Hlen₁.
     pose proof (Hlen₁ (i - len - 1)%nat) as H.
     replace (b + S i)%nat with (S (S (b + len + (i - len - 1)))) .
      assumption.

      rewrite Nat.add_succ_r.
      apply Nat.succ_inj_wd.
      rewrite <- Nat.sub_add_distr, Nat.add_1_r.
      rewrite <- Nat.add_succ_l, <- Nat.add_succ_r.
      rewrite <- Nat.add_assoc.
      rewrite Nat.add_sub_assoc; auto.
      rewrite Nat.add_sub_swap; auto.
      rewrite Nat.sub_diag; reflexivity.

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
     apply Hz, le_neq_lt; assumption.

   rewrite Nat.add_succ_r.
   apply null_coeff_range_length_iff in Hlen; simpl in Hlen.
   apply Hlen.

  exfalso; apply H₁.
  apply Nat.lt_sub_lt_add_l.
  rewrite Nat.sub_diag.
  apply Nat.lt_0_succ.
Qed.

Theorem series_nth_0_in_interval : ∀ s k,
  (∀ n, (Pos.to_nat k | nth_null_coeff_range_length r s n 0)%nat)
  → ∀ i,
    (i mod Pos.to_nat k ≠ 0)%nat
    → (s .[i] = 0)%K.
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

Theorem series_stretch_shrink : ∀ s k,
  (Pos.to_nat k | greatest_series_x_power r s 0)
  → (series_stretch k (series_shrink k s) = s)%ser.
Proof.
intros s k Hk.
constructor; intros i; simpl.
destruct (zerop (i mod Pos.to_nat k)) as [H₁| H₁].
 apply Nat.mod_divides in H₁; auto.
 destruct H₁ as (c, Hc); rewrite Nat.mul_comm in Hc; subst i.
 rewrite Nat.div_mul; auto; reflexivity.

 destruct Hk as (c, Hk).
 apply greatest_series_x_power_iff in Hk.
 unfold is_the_greatest_series_x_power in Hk.
 remember (null_coeff_range_length r s 1) as p eqn:Hp .
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
     rewrite Hd in H₁.
     rewrite Nat.mod_mul in H₁; auto.
     revert H₁; apply Nat.lt_irrefl.

     apply Nat.neq_mul_0.
     split; auto.

    remember (S c) as d eqn:Hd .
    rewrite <- Nat2Pos.id in Hd; auto; subst d.
    rewrite <- Pos2Nat.inj_mul in H.
    rewrite <- Pos2Nat.inj_mul in Hz.
    eapply series_nth_0_in_interval in H; eassumption.

  symmetry.
  apply null_coeff_range_length_iff in Hp.
  simpl in Hp.
  destruct i; [ idtac | apply Hp ].
  rewrite Nat.mod_0_l in H₁; auto.
  exfalso; revert H₁; apply Nat.lt_irrefl.
Qed.

Theorem nth_null_coeff_range_length_stretch : ∀ s b n k,
  nth_null_coeff_range_length r (series_stretch k s) n
    (b * Pos.to_nat k) =
  (Pos.to_nat k * nth_null_coeff_range_length r s n b)%nat.
Proof.
intros s b n k.
revert b.
induction n; intros.
 simpl.
 remember (null_coeff_range_length r s (S b)) as len eqn:Hlen .
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
 remember (null_coeff_range_length r s (S b)) as len eqn:Hlen .
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

Definition is_the_greatest_series_x_power₂ s b k :=
  match null_coeff_range_length r s (S b) with
  | fin _ =>
      is_a_series_in_x_power s b k ∧
      (∀ u, (1 < u)%nat → ∃ n, ¬(u * k | nth_null_coeff_range_length r s n b))
  | ∞ =>
      k = O
  end.

Theorem is_the_greatest_series_x_power_equiv : ∀ s b k,
  is_the_greatest_series_x_power s b k
  ↔ is_the_greatest_series_x_power₂ s b k.
Proof.
intros s b k.
split; intros H.
 unfold is_the_greatest_series_x_power in H.
 unfold is_the_greatest_series_x_power₂.
 remember (null_coeff_range_length r s (S b)) as p eqn:Hp₁ .
 symmetry in Hp₁.
 destruct p as [p| ]; [ idtac | assumption ].
 destruct H as (Hp, Hnp).
 split; [ assumption | idtac ].
 intros n Hn.
 destruct n; [ exfalso; revert Hn; apply Nat.nlt_0_r | idtac ].
 destruct n; [ exfalso; revert Hn; apply Nat.lt_irrefl | clear Hn ].
 destruct k.
  exfalso.
  unfold is_a_series_in_x_power in Hp.
  pose proof (Hnp 2%nat (Nat.lt_0_succ 1%nat)) as H.
  destruct H as (m, H).
  pose proof (Hp m) as Hm.
  destruct Hm as (q, Hq).
  rewrite Nat.mul_0_r in Hq.
  rewrite Hq in H.
  apply H.
  exists O; reflexivity.

  apply Hnp.
  simpl; rewrite <- Nat.add_succ_l.
  apply Nat.lt_add_pos_r, Nat.lt_0_succ.

 unfold is_the_greatest_series_x_power₂ in H.
 unfold is_the_greatest_series_x_power.
 remember (null_coeff_range_length r s (S b)) as p eqn:Hp₁ .
 symmetry in Hp₁.
 destruct p as [p| ]; [ idtac | assumption ].
 destruct H as (Hp, Hnp).
 split; [ assumption | idtac ].
 intros k₁ Hk₁.
 remember (Nat.lcm k k₁) as kk eqn:Hkk .
 remember Hkk as Hk; clear HeqHk.
 pose proof (Nat_divides_lcm_l k k₁) as Hdl.
 destruct Hdl as (u, Hu).
 rewrite <- Hkk in Hu.
 destruct u.
  simpl in Hu.
  rewrite Hu in Hk.
  symmetry in Hk.
  apply Nat.lcm_eq_0 in Hk.
  destruct Hk as [Hk| Hk].
   subst k.
   pose proof Nat.lt_1_2 as H.
   apply Hnp in H.
   destruct H as (n, Hn).
   rewrite Nat.mul_0_r in Hn.
   unfold is_a_series_in_x_power in Hp.
   exfalso; apply Hn, Hp.

   subst k₁.
   exfalso; revert Hk₁; apply Nat.nlt_0_r.

  destruct u.
   rewrite Nat.mul_1_l in Hu.
   move Hu at top; subst kk.
   rewrite Hk in Hk₁.
   apply Nat.nle_gt in Hk₁.
   exfalso; apply Hk₁.
   rewrite Nat.lcm_comm.
   destruct k.
    unfold is_a_series_in_x_power in Hp.
    pose proof (Hp O) as H.
    simpl in H.
    rewrite Hp₁ in H.
    destruct H as (c, Hc).
    rewrite Nat.mul_0_r in Hc.
    discriminate Hc.

    apply Nat_le_lcm_l; auto.

   destruct k.
    unfold is_a_series_in_x_power in Hp.
    pose proof (Hp O) as H.
    simpl in H.
    rewrite Hp₁ in H.
    destruct H as (c, Hc).
    rewrite Nat.mul_0_r in Hc.
    discriminate Hc.

    assert (1 < S (S u))%nat as H₁.
     apply lt_n_S, Nat.lt_0_succ.

     apply Hnp in H₁.
     destruct H₁ as (m, Hm).
     rewrite <- Hu, Hkk in Hm.
     exists m.
     intros H₁; apply Hm.
     unfold is_a_series_in_x_power in Hp.
     pose proof (Hp m) as H₂.
     apply Nat_lcm_divides; auto.
     intros H; rewrite H in Hk₁.
     exfalso; revert Hk₁; apply Nat.nlt_0_r.
Qed.

Theorem greatest_series_x_power_stretch : ∀ s b k,
  null_coeff_range_length r s (S b) ≠ ∞
  → greatest_series_x_power r (series_stretch k s) (b * Pos.to_nat k)%nat =
      (Pos.to_nat k * greatest_series_x_power r s b)%nat.
Proof.
(* à nettoyer *)
intros s b k Hinf.
remember (greatest_series_x_power r s b) as m eqn:Hm .
symmetry in Hm.
apply greatest_series_x_power_iff.
apply is_the_greatest_series_x_power_equiv.
unfold is_the_greatest_series_x_power₂.
apply greatest_series_x_power_iff in Hm.
unfold is_the_greatest_series_x_power in Hm.
remember (null_coeff_range_length r s (S b)) as p eqn:Hp .
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
  apply Nat.mod_divides.
   destruct m.
    assert (0 < 1)%nat as H by apply Nat.lt_0_1.
    apply Hnm in H.
    clear n.
    destruct H as (n, Hn).
    exfalso; apply Hn.
    exists (nth_null_coeff_range_length r s n b).
    rewrite Nat.mul_1_r; reflexivity.

    apply Nat.neq_mul_0; split; auto.

   pose proof (Hm n) as Hn.
   destruct Hn as (c, Hc).
   rewrite Hc.
   rewrite Nat.mul_assoc, Nat.mul_shuffle0.
   destruct m; [ rewrite Nat.mul_0_r; reflexivity | idtac ].
   rewrite Nat.mul_comm.
   rewrite Nat.mod_mul; [ reflexivity | idtac ].
   apply Nat.neq_mul_0; split; auto.

  intros u Hu.
  rewrite Nat.mul_comm, <- Nat.mul_assoc.
  destruct Hm as (Hm, Hmk).
  destruct m.
   exists O; simpl.
   rewrite Hp, Nat.mul_0_r.
   intros H.
   destruct H as (c, Hc).
   rewrite Nat.mul_0_r in Hc.
   discriminate Hc.

   assert (S m < S m * u)%nat as Hmu.
    apply mult_lt_compat_r with (p := S m) in Hu.
     rewrite Nat.mul_1_l, Nat.mul_comm in Hu.
     assumption.

     apply Nat.lt_0_succ.

    apply Hmk in Hmu.
    destruct Hmu as (n, Hn).
    exists n.
    intros H₁; apply Hn.
    rewrite nth_null_coeff_range_length_stretch in H₁.
    apply Nat.mod_divide in H₁.
     rewrite Nat.mul_mod_distr_l in H₁; auto.
      apply Nat.mul_eq_0_r in H₁; auto.
      apply Nat.mod_divide; auto.
      destruct u; [ exfalso; revert Hu; apply Nat.nlt_0_r | idtac ].
      apply Nat.neq_mul_0; auto.

      destruct u; [ exfalso; revert Hu; apply Nat.nlt_0_r | idtac ].
      apply Nat.neq_mul_0; auto.

     destruct u; [ exfalso; revert Hu; apply Nat.nlt_0_r | idtac ].
     apply Nat.neq_mul_0; simpl; auto.

 exfalso; apply Hinf; reflexivity.
Qed.

Theorem gcd_ps_is_pos : ∀ n k (ps : puiseux_series α), (0 < gcd_ps n k ps)%Z.
Proof.
intros n k ps.
unfold gcd_ps; simpl.
remember (ps_ordnum ps + Z.of_nat n)%Z as x.
rewrite <- Z.gcd_assoc.
remember (Z.gcd (' ps_polord ps) (Z.of_nat k))%Z as y eqn:Hy .
pose proof (Z.gcd_nonneg x y) as Hp.
unfold Z.le in Hp; unfold Z.lt.
remember (0 ?= Z.gcd x y)%Z as c eqn:Hc .
destruct c; [ idtac | auto | exfalso; apply Hp; reflexivity ].
symmetry in Hc; apply Z.compare_eq in Hc; symmetry in Hc.
apply Z.gcd_eq_0_r in Hc; subst y.
apply Z.gcd_eq_0_l in Hc.
exfalso; revert Hc; apply Pos2Z_ne_0.
Qed.

Theorem series_null_power : ∀ s b p,
  is_a_series_in_x_power s b p
  → ∀ i,
    ((i - b) mod p)%nat ≠ O
    → (s .[i] = 0)%K.
Proof.
intros s b p Hxp i Hip.
destruct p; [ exfalso; apply Hip; reflexivity | idtac ].
destruct (le_dec i b) as [H₁| H₁].
 apply Nat.sub_0_le in H₁.
 rewrite H₁, Nat.mod_0_l in Hip; auto.
 exfalso; apply Hip; reflexivity.

 apply Nat.nle_gt in H₁.
 remember (i - b)%nat as j eqn:Hj .
 symmetry in Hj.
 apply Nat.add_sub_eq_nz in Hj.
  subst i.
  remember (Pos.of_nat (S p)) as q eqn:Hq .
  apply series_nth_0_in_interval_from_any with (c := S j) (k := q).
   apply Nat.lt_succ_r; reflexivity.

   subst q; rewrite Nat2Pos.id; auto.

   unfold is_a_series_in_x_power in Hxp.
   subst q; rewrite Nat2Pos.id; auto.

   subst q; rewrite Nat2Pos.id; auto.

  intros H; apply Hip; rewrite H; clear H.
  apply Nat.mod_0_l; intros H; discriminate H.
Qed.

Theorem series_null_coeff_range_length_inf_iff : ∀ s,
  null_coeff_range_length r s 0 = ∞
  ↔ (s = 0)%ser.
Proof.
intros s.
split; intros H.
 apply null_coeff_range_length_iff in H.
 simpl in H.
 constructor; assumption.

 apply null_coeff_range_length_iff; simpl.
 inversion_clear H; assumption.
Qed.

Theorem ps_null_coeff_range_length_inf_iff : ∀ ps,
  null_coeff_range_length r (ps_terms ps) 0 = ∞
  ↔ (ps = 0)%ps.
Proof.
intros ps.
split; intros H.
 constructor.
 unfold normalise_ps; simpl.
 rewrite H.
 remember (null_coeff_range_length r 0%ser 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ]; [ idtac | reflexivity ].
 apply null_coeff_range_length_iff in Hn.
 simpl in Hn.
 destruct Hn as (_, Hn).
 exfalso; apply Hn; reflexivity.

 inversion H; subst.
 apply null_coeff_range_length_iff; simpl; intros i.
 unfold normalise_ps in H0; simpl in H0.
 remember (null_coeff_range_length r 0%ser 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ].
  exfalso; clear H0.
  apply null_coeff_range_length_iff in Hn.
  simpl in Hn.
  destruct Hn as (_, Hn).
  apply Hn; reflexivity.

  remember (null_coeff_range_length r (ps_terms ps) 0) as m eqn:Hm .
  symmetry in Hm.
  destruct m as [m| ].
   inversion_clear H0.
   simpl in H1, H2, H3.
   remember (greatest_series_x_power r (ps_terms ps) m) as p eqn:Hp .
   remember (gcd_ps m p ps) as g eqn:Hg .
   unfold normalise_series in H3.
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
    remember (null_coeff_range_length r (ps_terms ps) (S m)) as q eqn:Hq .
    symmetry in Hq.
    destruct q as [q| ].
     destruct Hp as (Hxp, Hnxp).
     eapply series_null_power; [ eassumption | idtac ].
     apply Nat.sub_gt in H₂; rewrite Nat.sub_0_r in H₂.
     intros H₃; apply H₂; clear H₂.
     pose proof (gcd_ps_is_pos m p ps) as Hgp.
     rewrite <- Hg in Hgp.
     unfold gcd_ps in Hg.
     remember (ps_ordnum ps + Z.of_nat m)%Z as x.
     remember (Z.gcd x (' ps_polord ps)) as z.
     pose proof (Z.gcd_divide_r z (Z.of_nat p)) as H₄.
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
       exists (Z.to_nat c).
       rewrite <- Z2Nat.inj_mul.
        rewrite <- Hc.
        rewrite Nat2Z.id; reflexivity.

        apply <- Z.mul_le_mono_pos_r; [ idtac | eassumption ].
        rewrite <- Hc; simpl.
        apply Nat2Z.is_nonneg.

        apply Z.lt_le_incl; assumption.

      destruct p; auto.
      unfold is_a_series_in_x_power in Hxp.
      pose proof (Hxp O) as H₅; simpl in H₅.
      rewrite Hq in H₅.
      destruct H₅ as (c, Hc).
      rewrite Nat.mul_0_r in Hc; discriminate Hc.

     destruct (eq_nat_dec i m) as [H₃| H₃].
      subst i.
      rewrite Nat.sub_diag in H₂; simpl in H₂.
      rewrite Nat.mod_0_l in H₂.
       exfalso; revert H₂; apply Nat.lt_irrefl.

       pose proof (gcd_ps_is_pos m p ps) as H₃.
       rewrite <- Hg in H₃.
       intros H₄.
       rewrite <- Z2Nat.inj_0 in H₄.
       apply Z2Nat.inj_iff in H₄.
        rewrite H₄ in H₃.
        exfalso; revert H₃; apply Z.lt_irrefl.

        apply Z.lt_le_incl; assumption.

        reflexivity.

      apply null_coeff_range_length_iff in Hq.
      simpl in Hq.
      pose proof (Hq (i - S m)%nat) as H₄.
      rewrite <- Nat.add_succ_r in H₄.
      rewrite <- Nat.sub_succ_l in H₄.
       rewrite Nat.sub_succ in H₄.
       rewrite Nat.add_sub_assoc in H₄; auto.
       rewrite Nat.add_comm, Nat.add_sub in H₄.
       assumption.

       apply Nat.neq_sym in H₃.
       apply le_neq_lt; assumption.

   apply null_coeff_range_length_iff in Hm.
   simpl in Hm.
   apply Hm.
Qed.

Theorem null_coeff_range_length_succ2 : ∀ s m,
  null_coeff_range_length r s (S m) =
  null_coeff_range_length r (series_left_shift m s) 1.
Proof.
intros s m.
remember (null_coeff_range_length r s (S m)) as n eqn:Hn .
symmetry in Hn |- *.
apply null_coeff_range_length_iff in Hn.
apply null_coeff_range_length_iff.
unfold null_coeff_range_length_prop in Hn |- *.
destruct n as [n| ].
 destruct Hn as (Hz, Hnz).
 split.
  intros i Hin; simpl.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l.
  apply Hz; assumption.

  simpl.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l.
  assumption.

 simpl; intros i.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 apply Hn.
Qed.

Theorem series_left_shift_left_shift : ∀ (s : power_series α) m n,
  (series_left_shift m (series_left_shift n s) =
   series_left_shift (m + n) s)%ser.
Proof.
intros s m n.
constructor; intros i; simpl.
rewrite Nat.add_comm, Nat.add_shuffle0; reflexivity.
Qed.

Theorem nth_null_coeff_range_length_left_shift : ∀ s m n p,
  nth_null_coeff_range_length r (series_left_shift m s) n p =
  nth_null_coeff_range_length r s n (m + p).
Proof.
intros s m n p.
revert m p.
induction n; intros; simpl.
 rewrite null_coeff_range_length_succ2; symmetry.
 rewrite null_coeff_range_length_succ2; symmetry.
 rewrite series_left_shift_left_shift.
 rewrite Nat.add_comm; reflexivity.

 rewrite null_coeff_range_length_succ2; symmetry.
 rewrite null_coeff_range_length_succ2; symmetry.
 rewrite series_left_shift_left_shift.
 rewrite Nat.add_comm.
 remember (null_coeff_range_length r (series_left_shift (m + p) s) 1) as q.
 symmetry in Heqq.
 destruct q as [q| ].
  symmetry.
  rewrite <- Nat.add_assoc, <- Nat.add_succ_r.
  symmetry.
  apply IHn.

  reflexivity.
Qed.

Theorem greatest_series_x_power_left_shift : ∀ s n p,
  greatest_series_x_power r (series_left_shift n s) p =
  greatest_series_x_power r s (n + p).
Proof.
intros s n p.
remember (greatest_series_x_power r s (n + p)) as k eqn:Hk .
symmetry in Hk.
apply greatest_series_x_power_iff in Hk.
apply greatest_series_x_power_iff.
unfold is_the_greatest_series_x_power in Hk |- *.
pose proof (nth_null_coeff_range_length_left_shift s n O p) as H.
simpl in H.
remember (null_coeff_range_length r s (S (n + p))) as n₁ eqn:Hn₁ .
remember (null_coeff_range_length r (series_left_shift n s) (S p)) as n₂
 eqn:Hn₂ .
symmetry in Hn₁, Hn₂.
destruct n₁ as [n₁| ].
 destruct n₂ as [n₂| ]; [ idtac | discriminate H ].
 destruct Hk as (Hxp, Hnxp).
 split.
  unfold is_a_series_in_x_power in Hxp |- *.
  rename n into m.
  intros n.
  rewrite nth_null_coeff_range_length_left_shift.
  apply Hxp.

  intros k₁ Hk₁.
  apply Hnxp in Hk₁.
  destruct Hk₁ as (m, Hm).
  exists m.
  rewrite nth_null_coeff_range_length_left_shift.
  assumption.

 destruct n₂; [ discriminate H | assumption ].
Qed.

(*
Definition cm ps₁ ps₂ := Plcm (ps_polord ps₁) (ps_polord ps₂).
Definition cm_factor α (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (ps_polord ps₁) (ps_polord ps₂) in
  Pos.of_nat (Pos.to_nat l / Pos.to_nat (ps_polord ps₁))%nat.
*)
Definition cm (ps₁ ps₂ : puiseux_series α) :=
  (ps_polord ps₁ * ps_polord ps₂)%positive.
Definition cm_factor α (ps₁ ps₂ : puiseux_series α) :=
  ps_polord ps₂.
(**)

End other_theorems.
