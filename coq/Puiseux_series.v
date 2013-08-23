(* $Id: Puiseux_series.v,v 1.287 2013-08-23 08:42:04 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Misc.
Require Import Series.
Require Import Nbar.
Require Import Zbar.

Set Implicit Arguments.

Record puiseux_series α := mkps
  { ps_terms : series α;
    ps_valnum : Zbar;
    ps_comden : positive }.

(* [series_head fld s] return the position of the first non null
   coefficient in the series [s]. *)
Definition series_head : ∀ α, field α → series α → Nbar.
Admitted.

Add Parametric Morphism α (fld : field α) : (series_head fld)
with signature (eq_series fld) ==> eq as series_head_morph.
Admitted.

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
  eq_ps_base : ∀ k₁ k₂ nz₁ nz₂,
    stretch_series k₁ (ps_terms nz₁) ≃
    stretch_series k₂ (ps_terms nz₂)
    → (ps_valnum nz₁ * ''k₁)%Zbar = (ps_valnum nz₂ * ''k₂)%Zbar
      → (ps_comden nz₁ * k₁ = ps_comden nz₂ * k₂)%positive
        → eq_ps nz₁ nz₂.

Notation "a ≈ b" := (eq_ps a b) (at level 70).

Theorem eq_ps_refl : reflexive _ eq_ps.
Proof.
intros ps.
constructor 1 with (k₁ := xH) (k₂ := xH); reflexivity.
Qed.

Theorem eq_ps_sym : symmetric _ eq_ps.
Proof.
intros ps₁ ps₂ H.
inversion H; subst.
econstructor; symmetry; try eassumption.
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
inversion H₁ as [k₁₁ k₁₂ nz₁₁ nz₁₂ Hss₁ Hvv₁ Hck₁]; subst.
 inversion H₂ as [k₂₁ k₂₂ nz₂₁ nz₂₂ Hss₂ Hvv₂ Hck₂]; subst.
 apply Zbar.mul_cancel_r with (p := Zpos k₂₁) in Hvv₁.
  apply Zbar.mul_cancel_r with (p := Zpos k₁₂) in Hvv₂.
   rewrite Zbar.mul_shuffle0 in Hvv₂.
   rewrite <- Hvv₁ in Hvv₂.
   do 2 rewrite <- Z.mul_assoc in Hvv₂.
   apply Pos.mul_cancel_r with (r := k₂₁) in Hck₁.
   apply Pos.mul_cancel_r with (r := k₁₂) in Hck₂.
   rewrite Pos_mul_shuffle0 in Hck₂.
   rewrite <- Hck₁ in Hck₂.
   do 2 rewrite <- Pos.mul_assoc in Hck₂.
   econstructor; try eassumption.
   symmetry; rewrite Pos.mul_comm.
   rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
   symmetry; rewrite Pos.mul_comm.
   rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
   rewrite Hss₁, <- Hss₂.
   rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
   rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
   rewrite Pos.mul_comm; reflexivity.

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
      match series_head fld (ps_terms nz) with
      | fin n => Some (ps_valnum nz + Z.of_nat n # ps_comden nz)
      | ∞ => None
      end
  | Zero => None
  end.

Definition valuation_coeff (ps : puiseux_series α) :=
  match ps with
  | NonZero nz =>
      match series_head fld (ps_terms nz) with
      | fin n => series_nth_fld fld n (ps_terms nz)
      | ∞ => zero fld
      end
  | Zero => zero fld
  end.

Definition adjust k nz :=
  {| ps_terms := stretch_series fld k (ps_terms nz);
     ps_valnum := ps_valnum nz * 'k;
     ps_comden := ps_comden nz * k |}.

(* ps_add *)

Definition series_pad_left n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n);
     stop := stop s + fin n |}.

(*
Definition lcm_div α (nz₁ nz₂ : ps_ps α) :=
  let l := Plcm (ps_comden nz₁) (ps_comden nz₂) in
  Pos.of_nat (Pos.to_nat l / Pos.to_nat (ps_comden nz₁))%nat.
*)
Definition lcm_div α (nz₁ nz₂ : ps_ps α) :=
  ps_comden nz₂.
(**)

Definition ps_add₀ (ps₁ ps₂ : puiseux_series α) :=
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

Definition ps_norm (ps : puiseux_series α) :=
  match ps with
  | NonZero nz =>
      match series_head fld (ps_terms nz) with
     | fin _ => ps
     | ∞ => Zero _
     end
  | Zero => ps
  end.

Definition ps_add (ps₁ ps₂ : puiseux_series α) := ps_norm (ps_add₀ ps₁ ps₂).

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
            {| ps_terms := series_mul_term (ps_terms ms₁) (ps_terms ms₂);
               ps_valnum := ps_valnum ms₁ + ps_valnum ms₂;
               ps_comden := ps_comden ms₁ |}
      | Zero => Zero _
      end
  | Zero => Zero _
  end.

End fld₂.

Add Parametric Morphism α (fld : field α) : (series_pad_left fld) with 
signature eq ==> eq_series fld ==> eq_series fld as series_pad_morph.
Proof.
intros n s₁ s₂ Heq.
constructor; simpl.
intros i.
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
intros kp s₁ s₂.
unfold stretch_series; simpl.
unfold series_add; simpl.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
remember (Pos.to_nat kp) as k.
assert (k ≠ O) as Hk by (subst k; apply pos_to_nat_ne_0).
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

    destruct lt₄, lt₅; rewrite fld_add_neutral; reflexivity.

 remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂) * fin k)) as a.
 remember (Nbar.max (stop s₁ * fin k) (stop s₂ * fin k)) as n.
 remember (Nbar.lt_dec (fin i) n) as b.
 remember (Nbar.lt_dec (fin i) (stop s₁ * fin k)) as c.
 remember (Nbar.lt_dec (fin i) (stop s₂ * fin k)) as d.
 destruct a, b, c, d; try rewrite fld_add_neutral; reflexivity.
Qed.

Lemma stretch_pad_series_distr : ∀ kp n s,
  stretch_series fld kp (series_pad_left fld n s) ≃
  series_pad_left fld (n * Pos.to_nat kp) (stretch_series fld kp s).
Proof.
intros kp n s.
constructor.
intros i.
unfold stretch_series, series_nth_fld; simpl.
remember (Pos.to_nat kp) as k.
assert (k ≠ O) as Hk by (subst k; apply pos_to_nat_ne_0).
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
unfold ps_norm.
remember (ps_add₀ fld (NonZero nz₁) (NonZero nz₂)) as ps₁₂.
remember (ps_add₀ fld (NonZero nz₂) (NonZero nz₁)) as ps₂₁.
symmetry in Heqps₁₂, Heqps₂₁.
destruct ps₁₂ as [nz₁₂| ].
 remember (series_head fld (ps_terms nz₁₂)) as n₁₂.
 symmetry in Heqn₁₂.
 destruct n₁₂ as [n₁₂| ].
  destruct ps₂₁ as [nz₂₁| ].
   remember (series_head fld (ps_terms nz₂₁)) as n₂₁.
   symmetry in Heqn₂₁.
   destruct n₂₁ as [n₂₁| ].
    rewrite <- Heqps₁₂, <- Heqps₂₁.
    constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
     do 2 rewrite stretch_series_1.
     apply series_add_comm.

     do 2 rewrite Z.mul_1_r.
     apply Z.min_comm.

     do 2 rewrite Pos.mul_1_r.
     apply Pos.mul_comm.
bbb.

intros ps₁ ps₂.
unfold ps_add; simpl.
destruct ps₁ as [nz₁| ]; [ idtac | destruct ps₂; reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
rewrite series_raw_add_comm.
remember
 (series_head fld
    (series_raw_add fld (adjust fld (lcm_div nz₂ nz₁) nz₂)
       (adjust fld (lcm_div nz₁ nz₂) nz₁))) as x.
destruct x as [n| ]; [ idtac | reflexivity ].
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 rewrite series_raw_add_comm; reflexivity.

 do 2 rewrite Z.mul_1_r.
 unfold lcm_div.
 rewrite Z.min_comm; reflexivity.

 do 2 rewrite Pos.mul_1_r.
 apply Pos.mul_comm.
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
 destruct c₁, c₂, c₃; try rewrite fld_add_neutral; reflexivity.

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

Lemma ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  ps_add fld (ps_add fld ps₁ ps₂) ps₃ ≈ ps_add fld ps₁ (ps_add fld ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃.
destruct ps₁ as [nz₁| ]; [ idtac | destruct ps₂; reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
destruct ps₃ as [nz₃| ].
 unfold ps_add, lcm_div; simpl.
 remember
  (series_head fld
     (series_raw_add fld (adjust fld (ps_comden nz₂) nz₁)
        (adjust fld (ps_comden nz₁) nz₂))) as n₁.
 remember
  (series_head fld
     (series_raw_add fld (adjust fld (ps_comden nz₃) nz₂)
        (adjust fld (ps_comden nz₂) nz₃))) as n₂.
 destruct n₁ as [n₁| ].
  destruct n₂ as [n₂| ].
   remember
    (adjust fld (ps_comden nz₃)
       (build_nz fld (adjust fld (ps_comden nz₂) nz₁)
          (adjust fld (ps_comden nz₁) nz₂) n₁)) as a₁.
   remember
    (adjust fld
       (ps_comden
          (build_nz fld (adjust fld (ps_comden nz₂) nz₁)
             (adjust fld (ps_comden nz₁) nz₂) n₁)) nz₃) as a₂.
   remember
    (adjust fld
       (ps_comden
          (build_nz fld (adjust fld (ps_comden nz₃) nz₂)
             (adjust fld (ps_comden nz₂) nz₃) n₂)) nz₁) as a₃.
   remember
    (adjust fld (ps_comden nz₁)
       (build_nz fld (adjust fld (ps_comden nz₃) nz₂)
          (adjust fld (ps_comden nz₂) nz₃) n₂)) as a₄.
   remember (series_head fld (series_raw_add fld a₁ a₂)) as m₁.
   remember (series_head fld (series_raw_add fld a₃ a₄)) as m₂.
   destruct m₁ as [m₁| ].
    destruct m₂ as [m₂| ].
     constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
      do 2 rewrite stretch_series_1.
      unfold series_raw_add; simpl.
      Focus 1.
bbb.

intros ps₁ ps₂ ps₃.
destruct ps₁ as [nz₁| ]; [ idtac | destruct ps₂; reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
destruct ps₃ as [nz₃| ]; [ idtac | reflexivity ].
unfold ps_add, lcm_div; simpl.
(*
do 4 rewrite Plcm_div_mul.
*)
remember (ps_valnum nz₁) as v₁.
remember (ps_valnum nz₂) as v₂.
remember (ps_valnum nz₃) as v₃.
remember (ps_comden nz₃) as c₃.
remember (ps_comden nz₂) as c₂.
remember (ps_comden nz₁) as c₁.
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
 remember (stretch_series fld (Pos.to_nat (c₂ * c₃)) (ps_terms nz₁)) as ccnz₁.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 remember (stretch_series fld (Pos.to_nat (c₃ * c₁)) (ps_terms nz₂)) as ccnz₂.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 remember (stretch_series fld (Pos.to_nat (c₂ * c₁)) (ps_terms nz₃)) as ccnz₃.
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
  remember (ps_valnum nz₁) as v₁.
  remember (ps_comden nz₁) as c₁.
  remember (ps_comden nz₂₁) as c₂₁.
  remember (ps_comden nz₂₂) as c₂₂.
  remember (ps_valnum nz₂₁) as v₂₁.
  remember (ps_valnum nz₂₂) as v₂₂.
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
    {| ps_terms := {| terms i := c; stop := 1 |};
       ps_valnum := Qnum pow;
       ps_comden := Qden pow |}.

Definition ps_const c : puiseux_series α :=
  NonZero
    {| ps_terms := {| terms i := c; stop := 1 |};
       ps_valnum := 0;
       ps_comden := 1 |}.

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
  destruct (lt_dec 0 (Pos.to_nat (ps_comden nz))) as [Hlt| Hge].
   rewrite Nbar.mul_1_r.
   remember (stop (ps_terms nz)) as st.
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
     (stretch_series fld (Pos.to_nat (ps_comden nz))
        {| terms := λ _ : nat, one fld; stop := 1 |})
     (stretch_series fld (Pos.to_nat 1) (ps_terms nz))) as x.
 symmetry in Heqx.
 destruct x as [x| ].
  unfold series_nth; simpl.
  rewrite Nat.add_0_r.
  destruct (lt_dec 0 (Pos.to_nat (ps_comden nz))) as [| Bad].
   rewrite Nbar.mul_1_r.
   remember (stop (ps_terms nz)) as st.
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
