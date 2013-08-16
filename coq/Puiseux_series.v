(* $Id: Puiseux_series.v,v 1.246 2013-08-16 19:26:04 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Misc.
Require Import Series.
Require Import Nbar.
Require Import Zbar.

Set Implicit Arguments.

Record nz_ps α := mkps
  { ps_terms : series α;
    ps_valnum : Z;
    ps_comden : positive }.

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
       if zerop (i mod k) then terms s (i / k) else zero fld;
     stop :=
       stop s * nfin k |}.

Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).

Inductive eq_ps : puiseux_series α → puiseux_series α → Prop :=
  | eq_non_zero_ps : ∀ k₁ k₂ nz₁ nz₂,
      stretch_series (Pos.to_nat k₁) (ps_terms nz₁) ≃
      stretch_series (Pos.to_nat k₂) (ps_terms nz₂)
      → (ps_valnum nz₁ * 'k₁)%Z = (ps_valnum nz₂ * 'k₂)%Z
        → (ps_comden nz₁ * k₁ = ps_comden nz₂ * k₂)%positive
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
  a ≠ O
  → b ≠ O
    → stretch_series (a * b) s ≃ stretch_series a (stretch_series b s).
Proof.
intros a b s Ha Hb.
unfold stretch_series.
f_equal; simpl.
constructor; simpl.
 intros i.
 destruct (zerop (i mod (a * b))) as [Hz| Hnz].
  destruct (zerop (i mod a)) as [Hz₁| Hnz].
   destruct (zerop ((i / a) mod b)) as [Hz₂| Hnz].
    rewrite Nat.div_div; [ reflexivity | assumption | assumption ].

    apply Nat.mod_divides in Hz.
     destruct Hz as (c, Hz).
     subst i.
     rewrite <- mult_assoc, mult_comm in Hnz.
     rewrite Nat.div_mul in Hnz; [ idtac | assumption ].
     rewrite mult_comm, Nat.mod_mul in Hnz; [ idtac | assumption ].
     exfalso; revert Hnz; apply lt_irrefl.

     apply Nat.neq_mul_0; split; assumption.

   apply Nat.mod_divides in Hz.
    destruct Hz as (c, Hz).
    subst i.
    rewrite <- mult_assoc, mult_comm in Hnz.
    rewrite Nat.mod_mul in Hnz; [ idtac | assumption ].
    exfalso; revert Hnz; apply lt_irrefl.

    apply Nat.neq_mul_0; split; assumption.

  destruct (zerop (i mod a)) as [Hz| ]; [ idtac | reflexivity ].
  destruct (zerop ((i / a) mod b)) as [Hz₁| ]; [ idtac | reflexivity ].
  apply Nat.mod_divides in Hz; [ idtac | assumption ].
  destruct Hz as (c, Hz).
  subst i.
  rewrite mult_comm, Nat.div_mul in Hz₁; [ idtac | assumption ].
  rewrite Nat.mul_mod_distr_l in Hnz; [ idtac | assumption | assumption ].
  rewrite Hz₁, mult_0_r in Hnz.
  exfalso; revert Hnz; apply lt_irrefl.

 rewrite Nbar.nfin_inj_mul.
 rewrite Nbar.mul_shuffle0, Nbar.mul_assoc; reflexivity.
Qed.

Add Parametric Morphism : stretch_series with 
signature eq ==> (eq_series fld) ==> (eq_series fld) as stretch_morph.
Proof.
intros k s₁ s₂ H.
inversion H; subst.
constructor; simpl.
 intros i.
 destruct (zerop (i mod k)); [ apply H0 | reflexivity ].

 destruct (stop s₁); rewrite <- H1; reflexivity.
Qed.

Lemma stretch_series_1 : ∀ s, stretch_series (Pos.to_nat 1) s ≃ s.
Proof.
intros s.
unfold stretch_series; simpl.
destruct s as (t, st); simpl.
constructor; simpl.
 intros i; rewrite divmod_div.
 rewrite Nat.div_1_r; reflexivity.

 rewrite Nbar.mul_1_r; reflexivity.
Qed.

Theorem eq_ps_trans : transitive _ eq_ps.
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

Add Parametric Relation : (puiseux_series α) eq_ps
 reflexivity proved by eq_ps_refl
 symmetry proved by eq_ps_sym
 transitivity proved by eq_ps_trans
 as eq_ps_rel.

Definition valuation (ps : puiseux_series α) :=
  match ps with
  | NonZero nz =>
      match series_head (fld_eq fld (zero fld)) 0 (ps_terms nz) with
      | Some (n, c) => Some (ps_valnum nz + Z.of_nat n # ps_comden nz)
      | None => None
      end
  | Zero => None
  end.

Definition valuation_coeff (ps : puiseux_series α) :=
  match ps with
  | NonZero nz =>
      match series_head (fld_eq fld (zero fld)) 0 (ps_terms nz) with
      | Some (_, c) => c
      | None => zero fld
      end
  | Zero => zero fld
  end.

Definition adjust k nz :=
  {| ps_terms := stretch_series (Pos.to_nat k) (ps_terms nz);
     ps_valnum := ps_valnum nz * 'k;
     ps_comden := ps_comden nz * k |}.

(* ps_add *)

Definition series_pad_left n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n);
     stop := stop s + nfin n |}.

(*
Definition lcm_div α (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (ps_comden ps₁) (ps_comden ps₂) in
  Pos.of_nat (Pos.to_nat l / Pos.to_nat (ps_comden ps₁))%nat.
*)
Definition lcm_div α (nz₁ nz₂ : nz_ps α) :=
  ps_comden nz₂.
(**)

Definition is_zero_sum (ps₁ ps₂ : puiseux_series α) : bool.
Proof. Admitted.

Axiom is_zero_sum_comm : ∀ ps₁ ps₂,
  is_zero_sum ps₁ ps₂ = true
  → is_zero_sum ps₂ ps₁ = true.

Definition ps_add (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ =>
          let ms₁ := adjust (lcm_div nz₁ nz₂) nz₁ in
          let ms₂ := adjust (lcm_div nz₂ nz₁) nz₂ in
          let v₁ := ps_valnum ms₁ in
          let v₂ := ps_valnum ms₂ in
          NonZero
            {| ps_terms :=
                 series_add fld
                   (series_pad_left (Z.to_nat v₁ - Z.to_nat v₂)%nat
                      (ps_terms ms₁))
                   (series_pad_left (Z.to_nat v₂ - Z.to_nat v₁)%nat
                      (ps_terms ms₂));
               ps_valnum :=
                 Z.min v₁ v₂;
               ps_comden :=
                 ps_comden ms₁ |}
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
          let l := Plcm (ps_comden nz₁) (ps_comden nz₂) in
          NonZero
            {| ps_terms := series_mul_term (ps_terms ms₁) (ps_terms ms₂);
               ps_valnum := ps_valnum ms₁ + ps_valnum ms₂;
               ps_comden := l |}
      | Zero => Zero _
      end
  | Zero => Zero _
  end.

(* *)

Add Parametric Morphism : series_pad_left with 
signature eq ==> eq_series fld ==> eq_series fld as series_pad_morph.
Proof.
intros n s₁ s₂ H.
constructor; simpl.
 intros i.
 destruct (lt_dec i n); [ reflexivity | idtac ].
 inversion H; apply H0.

 inversion H; rewrite H1; reflexivity.
Qed.

Lemma stretch_series_add_distr : ∀ k s₁ s₂,
  stretch_series k (series_add fld s₁ s₂) ≃
  series_add fld (stretch_series k s₁) (stretch_series k s₂).
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
  → stretch_series k (series_pad_left n s) ≃
    series_pad_left (n * k) (stretch_series k s).
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

Theorem ps_add_comm : ∀ ps₁ ps₂, ps_add ps₁ ps₂ ≈ ps_add ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_add; simpl.
remember (is_zero_sum ps₁ ps₂) as z.
symmetry in Heqz.
rewrite is_zero_sum_comm in Heqz.
rewrite Heqz.
destruct z; [ constructor 2; reflexivity | idtac ].
constructor 1 with (k₁ := xH) (k₂ := xH); try reflexivity; simpl.
 do 2 rewrite stretch_series_1.
 apply series_add_comm.

 do 2 rewrite Zbar.mul_1_r.
 apply Zbar.min_comm.

(*
 do 2 rewrite Pos.mul_1_r.
 unfold lcm_div.
 do 2 rewrite Plcm_div_mul.
 apply Plcm_comm.
*)
 do 2 rewrite Pos.mul_1_r.
 apply Pos.mul_comm.
(**)
Qed.

Lemma series_pad_add_distr : ∀ s₁ s₂ n,
  series_pad_left n (series_add fld s₁ s₂)
  ≃ series_add fld (series_pad_left n s₁) (series_pad_left n s₂).
Proof.
intros s₁ s₂ n.
constructor.
 intros i.
 unfold series_add; simpl.
 destruct (Nbar.lt_dec (nfin i) n) as [Hlt| Hge]; [ idtac | reflexivity ].
 symmetry; apply fld_add_neutral.

 simpl; rewrite Nbar.add_max_distr_r; reflexivity.
Qed.

Lemma series_pad_pad : ∀ x y ps,
  series_pad_left x (series_pad_left y ps) ≃ series_pad_left (x + y) ps.
Proof.
intros x y ps.
constructor; simpl.
 intros i.
 destruct (Nbar.lt_dec (nfin i) x) as [Hlt| Hge].
  destruct (Nbar.lt_dec (nfin i) (x + y)) as [| Hge]; [ reflexivity | idtac ].
  apply Nbar.lt_lt_add_r with (p := y) in Hlt; contradiction.

  apply Nbar.not_gt in Hge.
  destruct (Nbar.lt_dec (nfin (i - Nbar.to_nat x)) y) as [Hlt| Hge₁].
   destruct (Nbar.lt_dec (nfin i) (x + y)) as [| Hge₁].
    reflexivity.

    rewrite Nbar.add_comm in Hge₁.
    rewrite Nbar.nfin_inj_sub in Hlt.
    apply Nbar.lt_sub_lt_add_r in Hlt; [ idtac | intros H; discriminate H ].
    destruct x; [ contradiction | inversion Hge ].

   destruct (Nbar.lt_dec (nfin i) (x + y)) as [Hlt| Hge₂].
    exfalso; apply Hge₁; clear Hge₁.
    destruct x as [x| ]; [ simpl | inversion Hge ].
    destruct y as [y| ]; constructor.
    inversion Hlt...
    inversion Hlt; subst.
    inversion Hge; subst.
    omega.

    rewrite Nbar2Nat.inj_add.
     rewrite Nat.sub_add_distr; reflexivity.

     intros H; subst x; inversion Hge.

     intros H; subst y; apply Hge₂.
     rewrite Nbar.add_comm; constructor.

  rewrite Nbar.add_shuffle0, Nbar.add_assoc; reflexivity.
Qed.

Lemma ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  ps_add (ps_add ps₁ ps₂) ps₃ ≈ ps_add ps₁ (ps_add ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃.
unfold ps_add, lcm_div; simpl.
(*
do 4 rewrite Plcm_div_mul.
*)
remember (ps_valnum ps₁) as v₁.
remember (ps_valnum ps₂) as v₂.
remember (ps_valnum ps₃) as v₃.
remember (ps_comden ps₃) as c₃.
remember (ps_comden ps₂) as c₂.
remember (ps_comden ps₁) as c₁.
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 do 2 rewrite stretch_series_1.
 do 2 rewrite stretch_series_add_distr.
 rewrite <- Zbar.mul_min_distr_nonneg_r; [ idtac | apply Pos2Zbar.is_nonneg ].
 rewrite <- Zbar.mul_min_distr_nonneg_r; [ idtac | apply Pos2Zbar.is_nonneg ].
 do 2 rewrite Pos2Z.inj_mul.
 do 2 rewrite Zbar.zfin_inj_mul.
 do 2 rewrite Zbar.mul_assoc.
 remember (v₁ * '' c₂ * '' c₃)%Zbar as vcc eqn:Hvcc .
 remember (v₂ * '' c₁ * '' c₃)%Zbar as cvc eqn:Hcvc .
 remember (v₃ * '' c₁ * '' c₂)%Zbar as ccv eqn:Hccv .
 rewrite Zbar.mul_comm, Zbar.mul_assoc, Zbar.mul_shuffle0 in Hcvc.
 rewrite <- Zbar.mul_comm, Zbar.mul_assoc in Hcvc.
 rewrite <- Hcvc.
 rewrite Zbar.mul_shuffle0 in Hccv; rewrite <- Hccv.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 remember (stretch_series (Pos.to_nat (c₂ * c₃)) (ps_terms ps₁)) as ccps₁.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 remember (stretch_series (Pos.to_nat (c₃ * c₁)) (ps_terms ps₂)) as ccps₂.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 remember (stretch_series (Pos.to_nat (c₂ * c₁)) (ps_terms ps₃)) as ccps₃.
 do 2 rewrite series_pad_add_distr.
 rewrite series_add_assoc.
 rewrite Nbar.mul_sub_distr_r; [ idtac | intros H; discriminate H ].
 rewrite <- Z2Nat.inj_pos.
 do 4 rewrite series_pad_pad.
 rewrite Nbar.mul_sub_distr_r; [ idtac | intros H; discriminate H ].
 rewrite Nbar.mul_sub_distr_r; [ idtac | intros H; discriminate H ].
 rewrite Nbar.mul_sub_distr_r; [ simpl | intros H; discriminate H ].
 do 4 rewrite <- Zbar2Nbar_inj_mul_pos_r.
 rewrite <- Hvcc, <- Hcvc, <- Hccv.
 rewrite Zbar.mul_shuffle0, <- Hcvc.
 do 2 rewrite Zbar2Nbar.inj_min.
 do 2 rewrite Nbar_min_sub_add_sub.
 rewrite series_add_comm, Nbar.min_comm.
 rewrite Nbar_min_sub_add_sub, Nbar.min_comm, series_add_comm.
 symmetry.
 rewrite series_add_comm, series_add_assoc, series_add_comm.
 rewrite Nbar.min_comm, Nbar_min_sub_add_sub.
 rewrite series_add_comm, <- series_add_assoc, series_add_comm.
 reflexivity.

 do 2 rewrite Zbar.mul_1_r.
 rewrite <- Zbar.mul_min_distr_nonneg_r; [ idtac | apply Pos2Zbar.is_nonneg ].
 rewrite <- Zbar.mul_min_distr_nonneg_r; [ idtac | apply Pos2Zbar.is_nonneg ].
 rewrite Zbar.min_assoc.
 do 2 rewrite Pos2Z.inj_mul.
 do 2 rewrite Zbar.zfin_inj_mul.
 do 2 rewrite Zbar.mul_assoc.
 f_equal; [ idtac | apply Zbar.mul_shuffle0 ].
 f_equal; apply Zbar.mul_shuffle0.

 rewrite Pos.mul_assoc; reflexivity.
Qed.

End fld.
