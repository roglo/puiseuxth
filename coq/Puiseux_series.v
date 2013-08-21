(* $Id: Puiseux_series.v,v 1.270 2013-08-21 17:35:55 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Misc.
Require Import Series.
Require Import Nbar.

Set Implicit Arguments.

Record nz_ps α := mkps
  { nz_terms : series α;
    nz_valnum : Z;
    nz_comden : positive }.

Inductive puiseux_series α :=
  | NonZero : nz_ps α → puiseux_series α
  | Zero : puiseux_series α.

(* [series_head is_zero n s] skip the possible terms (starting from the nth
   one) with null coefficients and return either the couple of the rank of
   the first non null coefficient and the value of this coefficient or
   None if the series is null. Allows to compute the real valuation of a
   series, skipping the heading zeroes. Cannot be implemented in Coq since
   can take an infinite amount of time. *)
Definition series_head : ∀ α, (α → Prop) → nat → series α → option (nat * α).
Proof. Admitted.

Section fld.

Variable α : Type.
Variable fld : field α.

Definition stretch_series k s :=
  {| terms i :=
       if zerop (i mod Pos.to_nat k) then
         series_nth_fld fld (i / Pos.to_nat k) s
       else zero fld;
     stop :=
       stop s * fin (Pos.to_nat k) |}.

Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).

Inductive eq_ps : puiseux_series α → puiseux_series α → Prop :=
  | eq_non_zero_ps : ∀ k₁ k₂ nz₁ nz₂,
      stretch_series k₁ (nz_terms nz₁) ≃
      stretch_series k₂ (nz_terms nz₂)
      → (nz_valnum nz₁ * 'k₁)%Z = (nz_valnum nz₂ * 'k₂)%Z
        → (nz_comden nz₁ * k₁ = nz_comden nz₂ * k₂)%positive
          → eq_ps (NonZero nz₁) (NonZero nz₂)
  | eq_zero_ps : eq_ps (Zero _) (Zero _).

Notation "a ≈ b" := (eq_ps a b) (at level 70).

Theorem eq_ps_refl : reflexive _ eq_ps.
Proof.
intros ps.
destruct ps as [nz |]; [ idtac | constructor ].
econstructor 1 with (k₁ := xH); try assumption; reflexivity.
Qed.

Theorem eq_ps_sym : symmetric _ eq_ps.
Proof.
intros ps₁ ps₂ H.
inversion H; subst; [ idtac | constructor 2; assumption ].
econstructor; symmetry; eassumption.
Qed.

Lemma stretch_stretch_series : ∀ a b s,
  stretch_series (a * b) s ≃ stretch_series a (stretch_series b s).
Proof.
intros ap bp s.
unfold stretch_series; simpl.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
rewrite Pos2Nat.inj_mul.
remember (Pos.to_nat ap) as a.
remember (Pos.to_nat bp) as b.
assert (a ≠ O) as Ha by (subst a; apply pos_to_nat_ne_0).
assert (b ≠ O) as Hb by (subst b; apply pos_to_nat_ne_0).
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

End fld.

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
assert (k ≠ O) as Hk by (subst k; apply pos_to_nat_ne_0).
destruct (zerop (i mod k)) as [Hz| Hnz].
 apply Nat.mod_divides in Hz; [ idtac | assumption ].
 destruct Hz as (c, Hi).
 subst i.
 pose proof (Heq c) as Hc.
 rewrite Nat.mul_comm.
 rewrite Nbar.fin_inj_mul.
 rewrite Nat.div_mul; [ idtac | assumption ].
 destruct (Nbar.lt_dec (fin c * fin k) (stop s₁ * fin k)) as [Hlt₁| Hge₁].
  destruct (Nbar.lt_dec (fin c) (stop s₂)) as [Hlt₄| Hge₄].
   destruct (Nbar.lt_dec (fin c * fin k) (stop s₂ * fin k)) as [Hlt₃| Hge₃].
    assumption.

    (* peut-être faire un lemme puisque utilisé deux fois *)
    exfalso; apply Hge₃; clear Hge₃.
    apply Nbar.mul_lt_mono_pos_r.
     rewrite Heqk; simpl; constructor; apply Pos2Nat.is_pos.

     intros H; discriminate H.

     intros H; discriminate H.

     assumption.

   destruct (Nbar.lt_dec (fin c * fin k) (stop s₂ * fin k)); assumption.

  destruct (Nbar.lt_dec (fin c * fin k) (stop s₂ * fin k)) as [Hlt₂| ].
   destruct (Nbar.lt_dec (fin c) (stop s₂)) as [Hlt₃| ].
    destruct (Nbar.lt_dec (fin c) (stop s₁)) as [Hlt₄| ].
     exfalso; apply Hge₁; clear Hge₁.
     apply Nbar.mul_lt_mono_pos_r.
      rewrite Heqk; simpl; constructor; apply Pos2Nat.is_pos.

      intros H; discriminate H.

      intros H; discriminate H.

      assumption.

     assumption.

    reflexivity.

   reflexivity.

 destruct (Nbar.lt_dec (fin i) (stop s₁ * fin k)).
  destruct (Nbar.lt_dec (fin i) (stop s₂ * fin k)); reflexivity.

  destruct (Nbar.lt_dec (fin i) (stop s₂ * fin k)); reflexivity.
Qed.

Section fld₁.

Variable α : Type.
Variable fld : field α.

Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≈ b" := (eq_ps fld a b) (at level 70).

Lemma stretch_series_1 : ∀ s, stretch_series fld 1 s ≃ s.
Proof.
intros s.
unfold stretch_series; simpl.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite divmod_div, Nbar.mul_1_r, Nat.div_1_r.
destruct (Nbar.lt_dec (fin i) (stop s)); reflexivity.
Qed.

Theorem eq_ps_trans : transitive _ (eq_ps fld).
Proof.
intros ps₁ ps₂ ps₃ H₁ H₂.
inversion H₁ as [k₁₁ k₁₂ nz₁₁ nz₁₂ Hss₁ Hvv₁ Hck₁| ]; subst.
 inversion H₂ as [k₂₁ k₂₂ nz₂₁ nz₂₂ Hss₂ Hvv₂ Hck₂| ]; subst.
 apply Z.mul_cancel_r with (p := Zpos k₂₁) in Hvv₁.
  apply Z.mul_cancel_r with (p := Zpos k₁₂) in Hvv₂.
   rewrite Z.mul_shuffle0 in Hvv₂.
   rewrite <- Hvv₁ in Hvv₂.
   do 2 rewrite <- Z.mul_assoc in Hvv₂.
   apply Pos.mul_cancel_r with (r := k₂₁) in Hck₁.
   apply Pos.mul_cancel_r with (r := k₁₂) in Hck₂.
   rewrite Pos_mul_shuffle0 in Hck₂.
   rewrite <- Hck₁ in Hck₂.
   do 2 rewrite <- Pos.mul_assoc in Hck₂.
   econstructor; try eassumption.
   do 2 rewrite Pos2Nat.inj_mul.
   symmetry; rewrite mult_comm.
   rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
   symmetry; rewrite mult_comm.
   rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
   rewrite Hss₁, <- Hss₂.
   rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
   rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
   rewrite Nat.mul_comm; reflexivity.

   apply Zpos_ne_0.

  apply Zpos_ne_0.

 assumption.
Qed.

End fld₁.

Add Parametric Relation α (fld : field α) : (puiseux_series α) (eq_ps fld)
 reflexivity proved by (eq_ps_refl fld)
 symmetry proved by (eq_ps_sym (fld := fld))
 transitivity proved by (eq_ps_trans (fld := fld))
 as eq_ps_rel.

Section fld₂.

Variable α : Type.
Variable fld : field α.

Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≈ b" := (eq_ps fld a b) (at level 70).

Definition valuation (ps : puiseux_series α) :=
  match ps with
  | NonZero nz =>
      match series_head (fld_eq fld (zero fld)) 0 (nz_terms nz) with
      | Some (n, c) => Some (nz_valnum nz + Z.of_nat n # nz_comden nz)
      | None => None
      end
  | Zero => None
  end.

Definition valuation_coeff (ps : puiseux_series α) :=
  match ps with
  | NonZero nz =>
      match series_head (fld_eq fld (zero fld)) 0 (nz_terms nz) with
      | Some (_, c) => c
      | None => zero fld
      end
  | Zero => zero fld
  end.

Definition adjust k nz :=
  {| nz_terms := stretch_series fld (Pos.to_nat k) (nz_terms nz);
     nz_valnum := nz_valnum nz * 'k;
     nz_comden := nz_comden nz * k |}.

(* ps_add *)

Definition series_pad_left n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n);
     stop := stop s + fin n |}.

(*
Definition lcm_div α (nz₁ nz₂ : nz_ps α) :=
  let l := Plcm (nz_comden nz₁) (nz_comden nz₂) in
  Pos.of_nat (Pos.to_nat l / Pos.to_nat (nz_comden nz₁))%nat.
*)
Definition lcm_div α (nz₁ nz₂ : nz_ps α) :=
  nz_comden nz₂.
(**)

Definition ps_add (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ =>
          let ms₁ := adjust (lcm_div nz₁ nz₂) nz₁ in
          let ms₂ := adjust (lcm_div nz₂ nz₁) nz₂ in
          let v₁ := nz_valnum ms₁ in
          let v₂ := nz_valnum ms₂ in
          NonZero
            {| nz_terms :=
                 series_add fld
                   (series_pad_left (Z.to_nat v₁ - Z.to_nat v₂)%nat
                      (nz_terms ms₁))
                   (series_pad_left (Z.to_nat v₂ - Z.to_nat v₁)%nat
                      (nz_terms ms₂));
               nz_valnum :=
                 Z.min v₁ v₂;
               nz_comden :=
                 nz_comden ms₁ |}
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

Definition ps_mul (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ =>
          let ms₁ := adjust (lcm_div nz₁ nz₂) nz₁ in
          let ms₂ := adjust (lcm_div nz₂ nz₁) nz₂ in
          NonZero
            {| nz_terms := series_mul_term (nz_terms ms₁) (nz_terms ms₂);
               nz_valnum := nz_valnum ms₁ + nz_valnum ms₂;
               nz_comden := nz_comden ms₁ |}
      | Zero => Zero _
      end
  | Zero => Zero _
  end.

End fld₂.

Add Parametric Morphism α (fld : field α) : (series_pad_left fld) with 
signature eq ==> eq_series fld ==> eq_series fld as series_pad_morph.
Proof.
intros n s₁ s₂ H.
constructor; simpl.
 intros i.
 destruct (lt_dec i n); [ reflexivity | idtac ].
 inversion H; apply H0.

 inversion H; rewrite H1; reflexivity.
Qed.

Section fld₃.

Variable α : Type.
Variable fld : field α.

Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≈ b" := (eq_ps fld a b) (at level 70).

Lemma stretch_series_add_distr : ∀ k s₁ s₂,
  stretch_series fld k (series_add fld s₁ s₂) ≃
  series_add fld (stretch_series fld k s₁) (stretch_series fld k s₂).
Proof.
intros k s₁ s₂.
unfold stretch_series; simpl.
unfold series_add; simpl.
constructor; simpl.
 intros i.
 destruct (zerop (i mod k)) as [| Hnz]; [ reflexivity | idtac ].
 rewrite fld_add_neutral; reflexivity.

 rewrite Nbar.mul_max_distr_r; reflexivity.
Qed.

Lemma stretch_pad_series_distr : ∀ k n s,
  k ≠ O
  → stretch_series fld k (series_pad_left fld n s) ≃
    series_pad_left fld (n * k) (stretch_series fld k s).
Proof.
intros k n s Hk.
constructor.
 intros i.
 unfold stretch_series; simpl.
 destruct (zerop (i mod k)) as [Hz| Hnz].
  apply Nat.mod_divides in Hz; [ idtac | assumption ].
  destruct Hz as (c, Hi).
  subst i.
  rewrite mult_comm.
  rewrite Nat.div_mul; [ idtac | assumption ].
  destruct (lt_dec c n) as [Hlt| Hge].
   destruct (lt_dec (c * k) (n * k)) as [| Hnok].
    reflexivity.

    exfalso; apply Hnok.
    apply Nat.mul_lt_mono_pos_r; try (intros H; discriminate H); auto.
    destruct k; [ exfalso; apply Hk; reflexivity | idtac ].
    apply Nat.lt_0_succ.

   destruct (lt_dec (c * k) (n * k)) as [Hnok| Hok].
    exfalso; apply Hge.
    eapply Nat.mul_lt_mono_pos_r; try eassumption.
    apply not_gt; unfold gt.
    intros H; apply Hk.
    apply le_S_n, le_n_0_eq in H; symmetry; assumption.

    rewrite <- mult_minus_distr_r.
    rewrite Nat.mod_mul; [ simpl | assumption ].
    rewrite Nat.div_mul; [ reflexivity | assumption ].

  destruct (lt_dec i (n * k)) as [| Hge]; try reflexivity.
  destruct (zerop ((i - n * k) mod k)) as [Hz| ].
   apply Nat.mod_divides in Hz; [ idtac | assumption ].
   destruct Hz as (c, Hi).
   apply Nat.add_sub_eq_nz in Hi.
    subst i.
    rewrite Nat.mul_comm in Hnz; simpl in Hnz.
    rewrite <- Nat.mul_add_distr_l, Nat.mul_comm in Hnz.
    rewrite Nat.mod_mul in Hnz; [ idtac | assumption ].
    exfalso; revert Hnz; apply lt_irrefl.

    intros H; rewrite H in Hi.
    apply Nat.sub_0_le in Hi.
    apply not_gt, Nat.le_antisymm in Hge; [ idtac | assumption ].
    subst i.
    rewrite Nat.mod_mul in Hnz; [ idtac | assumption ].
    revert Hnz; apply lt_irrefl.

   reflexivity.

 simpl; rewrite Nbar.mul_add_distr_r; reflexivity.
Qed.

(* *)

Lemma Plcm_div_mul : ∀ x y,
  (x * Pos.of_nat (Pos.to_nat (Plcm x y) / Pos.to_nat x))%positive = Plcm x y.
Proof.
intros x y.
pose proof (Pos_divides_lcm_l x y) as H.
destruct H as (k, H).
rewrite H.
rewrite Pos2Nat.inj_mul.
rewrite Nat.div_mul; [ idtac | apply pos_to_nat_ne_0 ].
rewrite Pos2Nat.id.
apply Pos.mul_comm.
Qed.

Theorem ps_add_comm : ∀ ps₁ ps₂, ps_add fld ps₁ ps₂ ≈ ps_add fld ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_add; simpl.
destruct ps₁ as [nz₁| ]; [ idtac | destruct ps₂; reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 do 2 rewrite stretch_series_1.
 apply series_add_comm.

 do 2 rewrite Z.mul_1_r.
 apply Z.min_comm.

 do 2 rewrite Pos.mul_1_r.
(*
 unfold lcm_div.
 rewrite Pos_div_mul_l; [ idtac | apply Pos_divides_lcm_l ].
 symmetry; rewrite Plcm_comm.
 rewrite Pos_div_mul_l; [ reflexivity | apply Pos_divides_lcm_r ].
*)
 apply Pos.mul_comm.
(**)
Qed.

Lemma series_pad_add_distr : ∀ s₁ s₂ n,
  series_pad_left fld n (series_add fld s₁ s₂)
  ≃ series_add fld (series_pad_left fld n s₁) (series_pad_left fld n s₂).
Proof.
intros s₁ s₂ n.
constructor.
 intros i.
 unfold series_add; simpl.
 destruct (lt_dec i n) as [Hlt| Hge]; [ idtac | reflexivity ].
 symmetry; apply fld_add_neutral.

 simpl; rewrite Nbar.add_max_distr_r; reflexivity.
Qed.

Lemma series_pad_pad : ∀ x y ps,
  series_pad_left fld x (series_pad_left fld y ps) ≃
  series_pad_left fld (x + y) ps.
Proof.
intros x y ps.
constructor; simpl.
 intros i.
 destruct (lt_dec i x) as [Hlt| Hge].
  destruct (lt_dec i (x + y)) as [| Hge]; [ reflexivity | idtac ].
  apply Nat.lt_lt_add_r with (p := y) in Hlt; contradiction.

  apply not_gt in Hge.
  destruct (lt_dec (i - x) y) as [Hlt| Hge₁].
   destruct (lt_dec i (x + y)) as [| Hge₁].
    reflexivity.

    rewrite Nat.add_comm in Hge₁.
    apply Nat.lt_sub_lt_add_r in Hlt.
    contradiction.

   destruct (lt_dec i (x + y)) as [Hlt| Hge₂].
    exfalso; apply Hge₁; clear Hge₁.
    eapply Nat.le_lt_add_lt; [ constructor | idtac ].
    rewrite Nat.sub_add; [ rewrite Nat.add_comm; assumption | assumption ].

    rewrite Nat.sub_add_distr; reflexivity.

 rewrite Nbar.fin_inj_add.
 rewrite Nbar.add_shuffle0, Nbar.add_assoc; reflexivity.
Qed.

Lemma ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  ps_add fld (ps_add fld ps₁ ps₂) ps₃ ≈ ps_add fld ps₁ (ps_add fld ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃.
destruct ps₁ as [nz₁| ]; [ idtac | destruct ps₂; reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
destruct ps₃ as [nz₃| ]; [ idtac | reflexivity ].
unfold ps_add, lcm_div; simpl.
(*
do 4 rewrite Plcm_div_mul.
*)
remember (nz_valnum nz₁) as v₁.
remember (nz_valnum nz₂) as v₂.
remember (nz_valnum nz₃) as v₃.
remember (nz_comden nz₃) as c₃.
remember (nz_comden nz₂) as c₂.
remember (nz_comden nz₁) as c₁.
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 do 2 rewrite stretch_series_1.
 do 2 rewrite stretch_series_add_distr.
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 do 2 rewrite Pos2Z.inj_mul.
 do 2 rewrite Z.mul_assoc.
 remember (v₁ * ' c₂ * ' c₃)%Z as vcc eqn:Hvcc .
 remember (v₂ * ' c₁ * ' c₃)%Z as cvc eqn:Hcvc .
 remember (v₃ * ' c₁ * ' c₂)%Z as ccv eqn:Hccv .
 rewrite Z.mul_comm, Z.mul_assoc, Z.mul_shuffle0 in Hcvc.
 rewrite <- Z.mul_comm, Z.mul_assoc in Hcvc.
 rewrite <- Hcvc.
 rewrite Z.mul_shuffle0 in Hccv; rewrite <- Hccv.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 remember (stretch_series fld (Pos.to_nat (c₂ * c₃)) (nz_terms nz₁)) as ccnz₁.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 remember (stretch_series fld (Pos.to_nat (c₃ * c₁)) (nz_terms nz₂)) as ccnz₂.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 remember (stretch_series fld (Pos.to_nat (c₂ * c₁)) (nz_terms nz₃)) as ccnz₃.
 do 2 rewrite series_pad_add_distr.
 rewrite series_add_assoc.
 rewrite Nat.mul_sub_distr_r.
 rewrite <- Z2Nat.inj_pos.
 do 4 rewrite series_pad_pad.
 do 3 rewrite Nat.mul_sub_distr_r; simpl.
 do 4 rewrite <- Z2Nat_inj_mul_pos_r.
 rewrite <- Hvcc, <- Hcvc, <- Hccv.
 rewrite Z.mul_shuffle0, <- Hcvc.
 do 2 rewrite Z2Nat.inj_min.
 do 2 rewrite min_sub_add_sub.
 rewrite series_add_comm, Nat.min_comm.
 rewrite min_sub_add_sub, Nat.min_comm, series_add_comm.
 symmetry.
 rewrite series_add_comm, series_add_assoc, series_add_comm.
 rewrite Nat.min_comm, min_sub_add_sub.
 rewrite series_add_comm, <- series_add_assoc, series_add_comm.
 reflexivity.

 do 2 rewrite Z.mul_1_r.
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Z.min_assoc.
 do 2 rewrite Pos2Z.inj_mul.
 do 2 rewrite Z.mul_assoc.
 f_equal; [ idtac | apply Z.mul_shuffle0 ].
 f_equal; apply Z.mul_shuffle0.

 rewrite Pos.mul_assoc; reflexivity.
Qed.

Definition ps_zero := Zero α.

Theorem ps_add_neutral : ∀ ps, ps_add fld ps_zero ps ≈ ps.
Proof. reflexivity. Qed.

Lemma ps_add_cancel_l : ∀ ps₁ ps₂ ps₃,
  ps₂ ≈ ps₃
  → ps_add fld ps₁ ps₂ ≈ ps_add fld ps₁ ps₃.
Proof.
intros ps₁ ps₃ ps₄ H.
inversion H as [k₂₁ k₂₂ nz₂₁ nz₂₂ Hss₂ Hvv₂ Hck₂| ]; subst.
 destruct ps₁ as [nz₁| ]; [ idtac | assumption ].
 constructor 1 with (k₁ := k₂₁) (k₂ := k₂₂); unfold lcm_div; simpl.
  do 4 rewrite Z2Nat_inj_mul_pos_r.
  remember (nz_valnum nz₁) as v₁.
  remember (nz_comden nz₁) as c₁.
  remember (nz_comden nz₂₁) as c₂₁.
  remember (nz_comden nz₂₂) as c₂₂.
  remember (nz_valnum nz₂₁) as v₂₁.
  remember (nz_valnum nz₂₂) as v₂₂.
  do 2 rewrite stretch_series_add_distr.
  rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
  rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
  rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
  rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
  rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
  rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
  rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
  rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
(* à nettoyer *)
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
  rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
  rewrite Hss₂.
  rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
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

Theorem ps_add_compat : ∀ ps₁ ps₂ ps₃ ps₄,
  ps₁ ≈ ps₂
  → ps₃ ≈ ps₄
    → ps_add fld ps₁ ps₃ ≈ ps_add fld ps₂ ps₄.
Proof.
intros ps₁ ps₂ ps₃ ps₄ H₁ H₂.
transitivity (ps_add fld ps₁ ps₄).
 apply ps_add_cancel_l; assumption.

 rewrite ps_add_comm; symmetry.
 rewrite ps_add_comm; symmetry.
 apply ps_add_cancel_l; assumption.
Qed.

Definition ps_monom (c : α) pow :=
  NonZero
    {| nz_terms := {| terms i := c; stop := 1 |};
       nz_valnum := Qnum pow;
       nz_comden := Qden pow |}.

Definition ps_const c : puiseux_series α :=
  NonZero
    {| nz_terms := {| terms i := c; stop := 1 |};
       nz_valnum := 0;
       nz_comden := 1 |}.

Definition ps_one := ps_const (one fld).

Theorem ps_mul_neutral : ∀ ps, ps_mul fld ps_one ps ≈ ps.
Proof.
intros ps.
unfold ps_mul; simpl.
destruct ps as [nz| ]; [ idtac | reflexivity ].
unfold lcm_div; simpl.
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
  destruct (lt_dec 0 (Pos.to_nat (nz_comden nz))) as [Hlt| Hge].
   rewrite Nbar.mul_1_r.
   remember (stop (nz_terms nz)) as st.
   destruct st as [st| ]; simpl.
    destruct (lt_dec 0 st) as [Hlt₁| Hge₁].
     rewrite Nat.mod_0_l; simpl.
      rewrite fld_mul_neutral; reflexivity.

      apply pos_to_nat_ne_0.

     apply not_gt in Hge₁.
     apply Nat.le_0_r in Hge₁.
     subst st.
Focus 1.
bbb.

intros ps.
unfold ps_mul; simpl.
destruct ps as [nz| ]; [ idtac | reflexivity ].
unfold lcm_div; simpl.
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
    destruct (lt_dec i st) as [Hlt| Hge].
     rewrite Nat.mod_0_l; [ simpl | apply pos_to_nat_ne_0 ].
     rewrite divmod_div.
     rewrite Nat.div_1_r.
     rewrite fld_mul_neutral.
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
     fld_add_neutral := ps_add_neutral;
     fld_add_compat := ps_add_compat;
     fld_mul_neutral := ps_mul_neutral |}.

End fld₃.
