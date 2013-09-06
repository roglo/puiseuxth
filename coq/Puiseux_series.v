(* $Id: Puiseux_series.v,v 1.480 2013-09-06 01:26:56 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Misc.
Require Import Series.
Require Import Nbar.
Require Import Zbar.

Set Implicit Arguments.

(* [first_nonzero fld s] return the position of the first non null
   coefficient in the series [s]. *)
Definition first_nonzero : ∀ α, field α → series α → Nbar.
Admitted.

Add Parametric Morphism α (fld : field α) : (first_nonzero fld)
with signature (eq_series fld) ==> eq as first_nonzero_morph.
Admitted.

Section fld.

Variable α : Type.
Variable fld : field α.
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).
Notation "a ≃ b" := (eq_series fld a b) (at level 70).

Axiom lt_first_nonzero : ∀ s n,
  (fin n < first_nonzero fld s)%Nbar → series_nth_fld fld n s ≍ zero fld.

Axiom eq_first_nonzero : ∀ s n,
  first_nonzero fld s = fin n → ¬ (series_nth_fld fld n s ≍ zero fld).

Definition stretch_series k s :=
  {| terms i :=
       if zerop (i mod Pos.to_nat k) then
         series_nth_fld fld (i / Pos.to_nat k) s
       else zero fld;
     stop :=
       stop s * fin (Pos.to_nat k) |}.

Record nz_ps α := mknz
  { nz_terms : series α;
    nz_valnum : Z;
    nz_comden : positive }.

Inductive puiseux_series α :=
  | NonZero : nz_ps α → puiseux_series α
  | Zero : puiseux_series α.

Inductive eq_ps : puiseux_series α → puiseux_series α → Prop :=
  | eq_ps_base : ∀ k₁ k₂ nz₁ nz₂,
      stretch_series k₁ (nz_terms nz₁) ≃
      stretch_series k₂ (nz_terms nz₂)
      → (nz_valnum nz₁ * 'k₁)%Z =
        (nz_valnum nz₂ * 'k₂)%Z
        → (nz_comden nz₁ * k₁)%positive =
          (nz_comden nz₂ * k₂)%positive
          → eq_ps (NonZero nz₁) (NonZero nz₂)
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

(*
Lemma first_nonzero_fin : ∀ s v,
  first_nonzero fld s = fin v
  → not (∀ i : nat, series_nth_fld fld i s ≍ zero fld).
Proof.
intros s v Hf H.
apply first_nonzero_inf in H.
rewrite Hf in H; discriminate H.
Qed.
*)

Theorem eq_ps_refl : reflexive _ eq_ps.
Proof.
intros ps.
destruct ps as [nz| ]; [ idtac | constructor ].
constructor 1 with (k₁ := xH) (k₂ := xH); reflexivity.
Qed.

Theorem eq_ps_sym : symmetric _ eq_ps.
Proof.
intros ps₁ ps₂ H.
inversion H; subst.
 econstructor; symmetry; try eassumption.

 constructor 2; assumption.
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

Section fld₁.

Variable α : Type.
Variable fld : field α.
Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).
Notation "a ≈ b" := (eq_ps fld a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).

Lemma stretch_series_1 : ∀ s, stretch_series fld 1 s ≃ s.
Proof.
intros s.
unfold stretch_series; simpl.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite divmod_div, Nbar.mul_1_r, Nat.div_1_r.
destruct (Nbar.lt_dec (fin i) (stop s)); reflexivity.
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

Theorem eq_ps_trans : transitive _ (eq_ps fld).
Proof.
intros ps₁ ps₂ ps₃ H₁ H₂.
inversion H₁ as [k₁₁ k₁₂ nz₁₁ nz₁₂ Hss₁ Hvv₁ Hck₁| ]; subst.
 inversion H₂ as [k₂₁ k₂₂ nz₂₁ nz₂₂ Hss₂ Hvv₂ Hck₂| ]; subst.
 remember (k₁₁ * k₂₁)%positive as k₁ eqn:Hk₁ .
 remember (k₁₂ * k₂₂)%positive as k₂ eqn:Hk₂ .
 constructor 1 with (k₁ := k₁) (k₂ := k₂); subst k₁ k₂.
  rewrite Pos.mul_comm.
  rewrite stretch_stretch_series, Hss₁, <- stretch_stretch_series.
  rewrite Pos.mul_comm.
  rewrite stretch_stretch_series, Hss₂, <- stretch_stretch_series.
  reflexivity.

  rewrite Pos2Z.inj_mul, Z.mul_assoc, Hvv₁.
  rewrite Z.mul_shuffle0, Hvv₂, Z.mul_shuffle0.
  rewrite <- Z.mul_assoc, <- Pos2Z.inj_mul.
  reflexivity.

  rewrite Pos.mul_assoc, Hck₁.
  rewrite Pos_mul_shuffle0, Hck₂, Pos_mul_shuffle0.
  rewrite <- Pos.mul_assoc.
  reflexivity.

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
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).

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

Definition adjust k ps :=
  match ps with
  | NonZero nz =>
      NonZero
         {| nz_terms := stretch_series fld k (nz_terms nz);
            nz_valnum := nz_valnum nz * Zpos k;
            nz_comden := nz_comden nz * k |}
  | Zero =>
      Zero _
  end.

(* ps_add *)

Definition series_pad_left n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n);
     stop := stop s + fin n |}.

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

Definition nz_terms_add nz₁ nz₂ :=
  let s₁ := stretch_series fld (cm_factor nz₁ nz₂) (nz_terms nz₁) in
  let s₂ := stretch_series fld (cm_factor nz₂ nz₁) (nz_terms nz₂) in
  let v₁ := (nz_valnum nz₁ * 'cm_factor nz₁ nz₂)%Z in
  let v₂ := (nz_valnum nz₂ * 'cm_factor nz₂ nz₁)%Z in
  series_add fld
    (series_pad_left (Z.to_nat (v₁ - v₂)) s₁)
    (series_pad_left (Z.to_nat (v₂ - v₁)) s₂).

Definition build_nz_add v (nz₁ nz₂ : nz_ps α) :=
  let v₁ := (nz_valnum nz₁ * 'cm_factor nz₁ nz₂)%Z in
  let v₂ := (nz_valnum nz₂ * 'cm_factor nz₂ nz₁)%Z in
  {| nz_terms := nz_terms_add nz₁ nz₂;
     nz_valnum := Z.min v₁ v₂ + Z.of_nat v;
     nz_comden := cm nz₁ nz₂ |}.

Definition nz_add nz₁ nz₂ :=
  match first_nonzero fld (nz_terms_add nz₁ nz₂) with
  | fin v => NonZero (build_nz_add v nz₁ nz₂)
  | inf => Zero _
  end.

Definition ps_add (ps₁ ps₂ : puiseux_series α) :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => nz_add nz₁ nz₂
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
Notation "a ≭ b" := (not (fld_eq fld a b)) (at level 70).

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

    destruct lt₄, lt₅; rewrite fld_add_ident; reflexivity.

 remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂) * fin k)) as a.
 remember (Nbar.max (stop s₁ * fin k) (stop s₂ * fin k)) as n.
 remember (Nbar.lt_dec (fin i) n) as b.
 remember (Nbar.lt_dec (fin i) (stop s₁ * fin k)) as c.
 remember (Nbar.lt_dec (fin i) (stop s₂ * fin k)) as d.
 destruct a, b, c, d; try rewrite fld_add_ident; reflexivity.
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
  nz_terms_add fld ps₁ ps₂ ≃ nz_terms_add fld ps₂ ps₁.
Proof.
intros ps₁ ps₂.
apply series_add_comm.
Qed.

Lemma nz_add_comm : ∀ nz₁ nz₂, nz_add fld nz₁ nz₂ ≈ nz_add fld nz₂ nz₁.
Proof.
intros nz₁ nz₂.
unfold nz_add.
rewrite nz_terms_add_comm.
remember (first_nonzero fld (nz_terms_add fld nz₂ nz₁)) as v.
symmetry in Heqv.
destruct v as [v| ]; [ idtac | reflexivity ].
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 rewrite nz_terms_add_comm; reflexivity.

 rewrite Z.min_comm; reflexivity.

 unfold cm.
 do 2 rewrite Pos.mul_1_r; apply Pos.mul_comm.
Qed.

Theorem ps_add_comm : ∀ ps₁ ps₂, ps_add fld ps₁ ps₂ ≈ ps_add fld ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_add; simpl.
destruct ps₁ as [nz₁| ]; [ idtac | destruct ps₂; reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
apply nz_add_comm.
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
 destruct c₁, c₂, c₃; try rewrite fld_add_ident; reflexivity.

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

(*
Lemma nz_comden_adjust : ∀ c ps,
  nz_comden (adjust fld c ps) = (nz_comden ps * c)%positive.
Proof. intros; reflexivity. Qed.
*)

(*
Lemma nz_valnum_ps_add_nz : ∀ ps₁ ps₂,
  nz_valnum (nz_add fld ps₁ ps₂)
  = (Zbar.of_Nbar (first_nonzero fld (nz_terms_add fld ps₁ ps₂)) +
     Zbar.min (nz_valnum ps₁ * '' cm_factor ps₁ ps₂)
        (nz_valnum ps₂ * '' cm_factor ps₂ ps₁))%Zbar.
Proof.
intros ps₁ ps₂.
unfold ps_add_nz.
remember (first_nonzero fld (nz_terms_add fld ps₁ ps₂)) as v.
destruct v as [v| ]; [ simpl | reflexivity ].
remember (nz_valnum ps₁ * '' cm_factor ps₁ ps₂)%Zbar as v₁.
remember (nz_valnum ps₂ * '' cm_factor ps₂ ps₁)%Zbar as v₂.
destruct (Zbar.min v₁ v₂) as [v₁₂| ]; [ simpl | reflexivity ].
rewrite Z.add_comm; reflexivity.
Qed.
*)

Lemma first_nonzero_nonzero_fin : ∀ s n,
  first_nonzero fld s = fin (S n)
  → series_nth_fld fld 0 s ≍ zero fld.
Proof.
intros s n Hn.
apply lt_first_nonzero.
rewrite Hn.
constructor; apply lt_0_Sn.
Qed.

Lemma nz_terms_add_assoc : ∀ nz₁ nz₂ nz₃,
  nz_terms_add fld (build_nz_add fld 0 nz₁ nz₂) nz₃ ≃
  nz_terms_add fld nz₁ (build_nz_add fld 0 nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃.
constructor; intros i.
unfold build_nz_add; simpl.
do 2 rewrite Z.add_0_r.
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

Lemma series_pad_left_0 : ∀ s, series_pad_left fld 0 s ≃ s.
Proof.
intros s.
constructor; intros i.
unfold series_pad_left, series_nth_fld; simpl.
rewrite Nbar.add_0_r, Nat.sub_0_r; reflexivity.
Qed.

Definition terms_add ps₁ ps₂ :=
  match ps₁ with
  | NonZero nz₁ =>
      match ps₂ with
      | NonZero nz₂ => nz_terms_add fld nz₁ nz₂
      | Zero => nz_terms nz₁
      end
  | Zero =>
      match ps₂ with
      | NonZero nz₂ => nz_terms nz₂
      | Zero => series_0 fld
      end
  end.

Lemma nz_add_assoc_base : ∀ nz₁ nz₂ nz₃,
  nz_add fld (build_nz_add fld 0 nz₁ nz₂) nz₃ ≈
  nz_add fld nz₁ (build_nz_add fld 0 nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃.
unfold nz_add.
rewrite nz_terms_add_assoc.
remember (nz_terms_add fld nz₁ (build_nz_add fld 0 nz₂ nz₃)) as nz.
remember (first_nonzero fld nz) as n eqn:Hn ; subst nz.
destruct n as [n| ]; [ idtac | reflexivity ].
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 rewrite nz_terms_add_assoc; reflexivity.

 do 2 rewrite Z.add_0_r, Z.mul_1_r.
 unfold cm_factor, cm; simpl.
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
 rewrite Z.min_assoc.
 do 2 rewrite Pos2Z.inj_mul.
 do 2 rewrite Z.mul_assoc.
 do 2 f_equal; [ f_equal; apply Z.mul_shuffle0 | apply Z.mul_shuffle0 ].

 do 2 rewrite Pos.mul_1_r.
 unfold cm; simpl.
 unfold cm; simpl.
 rewrite Pos.mul_assoc; reflexivity.
Qed.

Delimit Scope ps_scope with ps.
Bind Scope ps_scope with puiseux_series.
Notation "a + b" := (ps_add fld a b) : ps_scope.

Lemma ps_add_assoc_base : ∀ ps₁ ps₂ ps₃,
  first_nonzero fld (terms_add ps₁ ps₂) = fin 0
  → first_nonzero fld (terms_add ps₂ ps₃) = fin 0
    → ps_add fld (ps_add fld ps₁ ps₂) ps₃ ≈
      ps_add fld ps₁ (ps_add fld ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃ Hn₁ Hn₂.
destruct ps₁ as [nz₁| ]; [ idtac | reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
destruct ps₃ as [nz₃| ]; [ idtac | rewrite ps_add_comm; reflexivity ].
simpl in Hn₁, Hn₂.
remember (ps_add fld (NonZero nz₁) (NonZero nz₂)) as x.
remember (ps_add fld (NonZero nz₂) (NonZero nz₃)) as y.
simpl in Heqx, Heqy; subst x y.
unfold nz_add.
rewrite Hn₁, Hn₂; simpl.
apply nz_add_assoc_base.
Qed.

Definition series_head (s : series α) :=
  match stop s with
  | fin 0 => s
  | _ => {| terms := terms s; stop := 1 |}
  end.

Definition series_tail (s : series α) :=
  match stop s with
  | fin 0 => s
  | _ => {| terms i := terms s (S i); stop := stop s - 1 |}
  end.

Definition nz_head nz :=
  {| nz_terms := series_head (nz_terms nz);
     nz_valnum := nz_valnum nz;
     nz_comden := nz_comden nz |}.

Definition nz_tail nz :=
  {| nz_terms := series_tail (nz_terms nz);
     nz_valnum := nz_valnum nz + 1;
     nz_comden := nz_comden nz |}.

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

Lemma stop_head_tail : ∀ nz,
  stop (nz_terms nz) ≠ fin 0
  → stop (nz_terms_add fld (nz_head nz) (nz_tail nz)) =
    stop (stretch_series fld (nz_comden nz) (nz_terms nz)).
Proof.
intros nz Hst.
unfold nz_terms_add; simpl.
rewrite Z.mul_add_distr_r, Z.mul_1_l.
rewrite Z.sub_add_distr, Z.sub_diag; simpl.
rewrite Z.add_simpl_l.
rewrite Nbar.add_0_r.
simpl.
remember (Pos.to_nat (nz_comden nz)) as c.
unfold series_head, series_tail; simpl.
remember (stop (nz_terms nz)) as st.
destruct st as [st| ]; [ simpl | reflexivity ].
destruct st as [| st]; simpl.
 exfalso; apply Hst; reflexivity.

 rewrite Nat.add_0_r, Nat.sub_0_r.
 rewrite Nat.max_r; [ idtac | apply le_plus_r ].
 rewrite Nat.mul_comm, Nat.add_comm; reflexivity.
Qed.

Lemma stop_0_series_nth_fld_0 : ∀ s n i,
  stop s = 0%Nbar
  → series_nth_fld fld i (stretch_series fld n s) = zero fld.
Proof.
intros s n i Hs.
unfold series_nth_fld; simpl.
rewrite Hs; simpl.
destruct (Nbar.lt_dec (fin i) 0) as [Hlt₁| Hge₁]; [ idtac | reflexivity ].
apply Nbar.nlt_ge in Hlt₁.
 exfalso; apply Hlt₁; constructor; apply lt_0_Sn.

 intros H; discriminate H.
Qed.

Lemma ps_cons : ∀ nz,
  first_nonzero fld (nz_terms_add fld (nz_head nz) (nz_tail nz)) = fin 0
  → nz_add fld (nz_head nz) (nz_tail nz) ≈ NonZero nz.
Proof.
intros nz Hn.
destruct (Nbar.eq_dec (stop (nz_terms nz)) (fin 0)) as [Hst| Hst].
 unfold nz_add; simpl.
 rewrite Hn.
 constructor 1 with (k₁ := xH) (k₂ := nz_comden nz); simpl.
  rewrite stretch_series_1.
  constructor; intros i.
  rewrite stop_0_series_nth_fld_0; [ idtac | assumption ].
  unfold series_nth_fld.
  simpl.
  unfold series_head, series_tail.
  simpl.
  rewrite Hst; simpl.
  rewrite Hst; simpl.
  rewrite Z.mul_add_distr_r, Z.mul_1_l.
  rewrite Z.sub_add_distr, Z.sub_diag; simpl.
  rewrite Z.add_simpl_l.
  simpl.
  destruct (Nbar.lt_dec (fin i) (fin (Pos.to_nat (nz_comden nz))))
   as [Hlt₁| Hge₁].
   rewrite series_pad_left_0.
   rewrite <- stretch_pad_1_series_distr.
   rewrite stop_0_series_nth_fld_0; [ idtac | assumption ].
   rewrite fld_add_ident.
   unfold series_nth_fld; simpl.
   rewrite Hst; simpl.
   rewrite Nat.add_0_r.
   destruct (Nbar.lt_dec (fin i) (fin (Pos.to_nat (nz_comden nz))))
    as [Hlt₂| Hge₂].
    destruct (zerop (i mod Pos.to_nat (nz_comden nz))) as [Hz| Hnz].
     apply Nat.mod_divides in Hz.
      destruct Hz as (k, Hi).
      subst i.
      rewrite Nat.mul_comm.
      rewrite Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
      unfold series_nth_fld; simpl.
      rewrite Hst; simpl.
      destruct k.
       simpl.
       destruct (Nbar.lt_dec 0 1); reflexivity.

       exfalso.
       apply Nbar.nlt_ge in Hlt₁.
        apply Hlt₁; simpl.
        constructor.
        rewrite Nat.mul_comm; simpl.
        rewrite <- plus_Sn_m.
        apply le_plus_l.

        intros H; discriminate H.

      apply Pos2Nat_ne_0.

     reflexivity.

    reflexivity.

   reflexivity.

  rewrite Z.min_l; [ ring | idtac ].
  rewrite Z.mul_add_distr_r, Z.mul_1_l.
  eapply Z.sub_le_mono_r.
  rewrite Z.sub_diag.
  rewrite Z.add_simpl_l.
  apply Pos2Z.is_nonneg.

  unfold cm.
  simpl.
  rewrite Pos.mul_1_r; reflexivity.

 unfold nz_add.
 rewrite Hn.
 constructor 1 with (k₁ := xH) (k₂ := nz_comden nz); simpl.
  rewrite stretch_series_1.
  constructor; intros i.
  remember (nz_terms_add fld (nz_head nz) (nz_tail nz)) as s₁ eqn:Hs₁ .
  remember (stretch_series fld (nz_comden nz) (nz_terms nz)) as s₂ eqn:Hs₂ .
  unfold series_nth_fld; simpl.
  destruct (Nbar.lt_dec (fin i) (stop s₁)) as [Hlt₁| Hge₁].
   destruct (Nbar.lt_dec (fin i) (stop s₂)) as [Hlt₂| Hge₂].
    subst s₁ s₂; simpl.
    rewrite Z.mul_add_distr_r, Z.mul_1_l.
    rewrite Z.sub_add_distr, Z.sub_diag; simpl.
    rewrite Z.add_simpl_l.
    rewrite series_pad_left_0; simpl.
    destruct (zerop (i mod Pos.to_nat (nz_comden nz))) as [Hz| Hnz].
     simpl in Hlt₁, Hlt₂.
     unfold series_head, series_tail in Hlt₁ |- *.
     simpl in Hlt₁ |- *.
     remember (stop (nz_terms nz)) as st.
     symmetry in Heqst.
     destruct st as [st| ]; simpl in Hlt₁, Hlt₂.
      destruct st as [| st]; [ idtac | simpl in Hlt₁ |- * ].
       exfalso; revert Hlt₂; apply Nbar.nlt_0_r.

       rewrite Nat.add_0_r, Nat.sub_0_r in Hlt₁.
       rewrite Z.mul_add_distr_r, Z.mul_1_l in Hlt₁.
       rewrite Z.sub_add_distr, Z.sub_diag in Hlt₁.
       rewrite Z.add_simpl_l in Hlt₁.
       simpl in Hlt₁.
       rewrite Nat.add_0_r in Hlt₁.
       rewrite <- Nat.mul_succ_l in Hlt₁.
       apply Nat.mod_divides in Hz; [ idtac | apply Pos2Nat_ne_0 ].
       destruct Hz as (k, Hi).
       subst i.
       rewrite Nat.mul_comm, Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
       rewrite Nat.sub_0_r.
       remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
       unfold series_nth_fld; simpl.
       rewrite Nat.add_0_r.
       rewrite <- Hc.
       rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
       rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
       rewrite Nat.mul_comm, <- Nat.mul_pred_r.
       destruct (Nbar.lt_dec (fin (c * k)) (fin c)) as [Hlt₃| Hge₃].
        remember (c * k)%nat as x.
        rewrite Nat.mul_comm, <- Nat.mul_succ_r; subst x.
        destruct (Nbar.lt_dec (fin (c * k)) (fin (c * S st))) as [Hlt₄| Hge₄].
         destruct (lt_dec (c * k) c) as [Hlt₅| Hge₅].
          unfold series_nth_fld; simpl.
          rewrite Heqst.
          rewrite fld_add_comm, fld_add_ident.
          destruct (Nbar.lt_dec (fin k) 1) as [Hlt₆| Hge₆].
           destruct (Nbar.lt_dec (fin k) (fin (S st))) as [| Hge₇].
            reflexivity.

            exfalso; apply Hge₇; clear Hge₇.
            do 2 rewrite Nbar.fin_inj_mul in Hlt₂.
            apply <- Nbar.mul_lt_mono_pos_r.
             rewrite Nbar.mul_comm; eassumption.

             intros H; discriminate H.

             intros H; discriminate H.

             destruct k; [ rewrite Nat.mul_0_r in Hlt₃; assumption | idtac ].
             apply Nbar.nlt_ge in Hlt₆.
              exfalso; apply Hlt₆.
              constructor; apply le_n_S, le_n_S, le_0_n.

              intros H; discriminate H.

           apply Nbar.nlt_ge in Hge₆; [ idtac | intros H; discriminate H ].
           destruct k.
            apply Nbar.nlt_ge in Hge₆; [ idtac | intros H; discriminate H ].
            exfalso; apply Hge₆; constructor; apply Nat.lt_0_1.

            apply Nbar.nlt_ge in Hlt₃; [ idtac | intros H; discriminate H ].
            exfalso; apply Hlt₃.
            constructor.
            apply le_n_S; rewrite Nat.mul_comm; simpl.
            apply le_plus_l.

          destruct k.
           exfalso; apply Hge₅; rewrite Nat.mul_0_r; subst c.
           apply Pos2Nat.is_pos.

           unfold series_nth_fld; simpl.
           rewrite Nat.mul_comm.
           rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
           rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
           destruct (Nbar.lt_dec (fin (S k)) 1) as [Hlt₆| Hge₆].
            apply Nbar.nlt_ge in Hlt₆.
             exfalso; apply Hlt₆.
             constructor; apply le_n_S, le_n_S, le_0_n.

             intros H; discriminate H.

            rewrite fld_add_ident.
            rewrite Heqst.
            destruct (Nbar.lt_dec (fin k) (fin st)) as [Hlt₇| Hge₇].
             destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [Hlt₈| Hge₈].
              reflexivity.

              exfalso; apply Hge₈.
              constructor; apply lt_n_S.
              inversion Hlt₇; assumption.

             destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [Hlt₈| Hge₈].
              exfalso; apply Hge₇.
              constructor; apply lt_S_n.
              inversion Hlt₈; assumption.

              reflexivity.

         replace (c * S st)%nat with (S st * c)%nat in Hge₄ .
          contradiction.

          apply Nat.mul_comm.

        rewrite fld_add_ident.
        rewrite <- Nat.mul_succ_l.
        destruct (Nbar.lt_dec (fin (c * k)) (fin (S st * c))) as [Hlt₄| Hge₄].
         destruct (lt_dec (c * k) c) as [Hlt₅| Hge₅].
          exfalso; apply Hge₃.
          constructor; assumption.

          rewrite Nat.mul_comm.
          rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
          rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
          unfold series_nth_fld; simpl.
          rewrite Heqst.
          destruct k.
           rewrite Nat.mul_0_r in Hge₅.
           exfalso; apply Hge₅; subst c; apply Pos2Nat.is_pos.

           simpl.
           destruct (Nbar.lt_dec (fin k) (fin st)) as [Hlt₆| Hge₆].
            destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [Hlt₇| Hge₇].
             reflexivity.

             exfalso; apply Hge₇; constructor; apply lt_n_S.
             inversion Hlt₆; assumption.

            destruct (Nbar.lt_dec (fin (S k)) (fin (S st))) as [Hlt₇| Hge₇].
             exfalso; apply Hge₆; constructor; apply lt_S_n.
             inversion Hlt₇; assumption.

             reflexivity.

         contradiction.

      simpl.
      apply Nat.mod_divides in Hz; [ idtac | apply Pos2Nat_ne_0 ].
      destruct Hz as (k, Hi).
      subst i.
      rewrite Nat.mul_comm, Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
      remember (Pos.to_nat (nz_comden nz)) as c eqn:Hc .
      unfold series_nth_fld; simpl.
      rewrite Nat.add_0_r.
      rewrite <- Hc.
      rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
      rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
      rewrite Nat.mul_comm, <- Nat.mul_pred_r.
      destruct (Nbar.lt_dec (fin (c * k)) (fin c)) as [Hlt₃| Hge₃].
       destruct (Nbar.lt_dec (fin (c * k)) inf) as [Hlt₄| Hge₄].
        destruct (lt_dec (c * k) c) as [Hlt₅| Hge₅].
         rewrite fld_add_comm, fld_add_ident.
         rewrite Heqst.
         destruct (Nbar.lt_dec (fin k) inf) as [Hlt₆| Hge₆].
          unfold series_nth_fld; simpl.
          destruct (Nbar.lt_dec (fin k) 1) as [Hlt₇| Hge₇].
           reflexivity.

           destruct k.
            exfalso; apply Hge₇; constructor; apply Nat.lt_0_1.

            apply Nat.nlt_ge in Hlt₅.
            exfalso; apply Hlt₅, le_n_S; rewrite Nat.mul_comm; simpl.
            apply le_plus_l.

          exfalso; apply Hge₆; constructor.

         exfalso; apply Hge₅.
         inversion Hlt₃; assumption.

        exfalso; apply Hge₄; constructor.

       rewrite fld_add_ident.
       destruct (Nbar.lt_dec (fin (c * k)) inf) as [Hlt₄| Hge₄].
        destruct (lt_dec (c * k) c) as [Hlt₅| Hge₅].
         exfalso; apply Hge₃; constructor; assumption.

         rewrite Nat.mul_comm.
         rewrite Nat.mod_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
         rewrite Nat.div_mul; [ simpl | subst c; apply Pos2Nat_ne_0 ].
         rewrite Heqst.
         unfold series_nth_fld; simpl.
         destruct (Nbar.lt_dec (fin (pred k)) inf) as [Hlt₆| Hge₆].
          destruct (Nbar.lt_dec (fin k) inf) as [Hlt₇| Hge₇].
           destruct k; [ simpl | reflexivity ].
           rewrite Nat.mul_0_r in Hge₅.
           exfalso; apply Hge₅; subst c; apply Pos2Nat.is_pos.

           exfalso; apply Hge₇; constructor.

          exfalso; apply Hge₆; constructor.

        exfalso; apply Hge₄; constructor.

     rewrite <- stretch_pad_1_series_distr.
     rewrite padded_in_stretched; [ rewrite fld_add_ident | assumption ].
     rewrite padded_in_stretched; [ reflexivity | assumption ].

    remember (stop (nz_terms nz)) as st.
    symmetry in Heqst.
    destruct st as [st| ].
     destruct st as [| st]; [ exfalso; apply Hst; reflexivity | idtac ].
     subst s₁ s₂.
     rewrite stop_head_tail in Hlt₁; [ contradiction | idtac ].
     intros H; rewrite Heqst in H; discriminate H.

     subst s₁ s₂.
     rewrite stop_head_tail in Hlt₁; [ contradiction | idtac ].
     intros H; rewrite Heqst in H; discriminate H.

   destruct (Nbar.eq_dec (stop (nz_terms nz)) 0) as [Heq| Hne].
    destruct (Nbar.lt_dec (fin i) (stop s₂)) as [Hlt₂| Hge₂].
     subst s₂.
     simpl in Hlt₂.
     rewrite Heq in Hlt₂; simpl in Hlt₂.
     exfalso; revert Hlt₂; apply Nbar.nlt_0_r.

     reflexivity.

    subst s₁ s₂.
    rewrite stop_head_tail in Hge₁; [ idtac | assumption ].
    remember (stretch_series fld (nz_comden nz) (nz_terms nz)) as s₂ eqn:Hs₂ .
    destruct (Nbar.lt_dec (fin i) (stop s₂)); [ contradiction | reflexivity ].

  rewrite Z.mul_1_r.
  rewrite Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
  rewrite Z.min_l.
   rewrite Z.add_0_r; reflexivity.

   rewrite Z.add_1_r; apply Z.le_succ_diag_r.

  rewrite Pos.mul_1_r; reflexivity.
Qed.

Lemma yyy : ∀ nz₁ nz₂ nz₃ n₁,
  first_nonzero fld (nz_terms_add fld nz₁ nz₂) = fin n₁
  → first_nonzero fld (nz_terms_add fld nz₂ nz₃) = fin 0
    → nz_add fld (build_nz_add fld n₁ nz₁ nz₂) nz₃ ≈
      nz_add fld nz₁ (build_nz_add fld 0 nz₂ nz₃).
Proof.
intros nz₁ nz₂ nz₃ n₁ Hn₁ Hn₂.
revert nz₁ nz₂ nz₃ Hn₁ Hn₂.
induction n₁ as [| n₁]; intros.
 apply nz_add_assoc_base.

 remember (nz_head nz₁) as pm₁.
 remember (nz_tail nz₁) as nz'₁.
 remember (nz_add fld pm₁ nz'₁) as ps₁ eqn:Hps₁ .
 symmetry in Hps₁.
 destruct ps₁ as [nz| ].
  assert (NonZero nz ≈ NonZero nz₁) as H.
   rewrite <- Hps₁, Heqpm₁, Heqnz'₁.
   apply ps_cons.
bbb.
   constructor 1 with (k₁ := xH) (k₂ := nz_comden nz₁).
    rewrite stretch_series_1.
    constructor; intros i.
    unfold series_nth_fld.
    unfold nz_add in Hps₁.
    rewrite Heqpm₁ in Hps₁.
    remember (nz_terms_add fld (nz_head nz₁) nz'₁) as nz₁₂.
    remember (first_nonzero fld nz₁₂) as n₁₂ eqn:Hn₁₂ .
    subst nz₁₂; symmetry in Hn₁₂.
    destruct n₁₂ as [n₁₂| ]; [ idtac | discriminate Hps₁ ].
    injection Hps₁; clear Hps₁; intros Hps₁.
    rewrite <- Heqpm₁ in Hn₁₂.
    remember (stop (nz_terms nz)) as st eqn:Hst .
    rewrite <- Hps₁ in Hst; simpl in Hst.
    rewrite Heqnz'₁ in Hst; simpl in Hst.
    rewrite Nat.add_0_r in Hst.
    remember (stop (nz_terms nz₁)) as st₁ eqn:Hst₁ .
    symmetry in Hst, Hst₁.
    destruct st₁ as [st₁| ].
     simpl in Hst.
     destruct (Nbar.lt_dec (fin i) st) as [Hlt₁| Hge₁].
      remember (stretch_series fld (nz_comden nz₁) (nz_terms nz₁)) as s.
      remember (stop s) as st₂ eqn:Hst₂ ; subst s.
      symmetry in Hst₂.
      simpl in Hst₂.
      rewrite Hst₁ in Hst₂.
      simpl in Hst₂.
      destruct (Nbar.lt_dec (fin i) st₂) as [Hlt₂| Hge₂].
       Focus 1.
       rewrite <- Hps₁; simpl.
       unfold cm_factor; simpl.
       rewrite Heqnz'₁; simpl.
       unfold stretch_series; simpl.
bbb.

Lemma zzz : ∀ ps₁ ps₂ ps₃ n₁,
  first_nonzero fld (terms_add ps₁ ps₂) = fin n₁
  → first_nonzero fld (terms_add ps₂ ps₃) = fin 0
    → ps_add fld (ps_add fld ps₁ ps₂) ps₃ ≈
      ps_add fld ps₁ (ps_add fld ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃ n₁ Hn₁ Hn₂.
destruct ps₁ as [nz₁| ]; [ idtac | reflexivity ].
destruct ps₂ as [nz₂| ]; [ idtac | reflexivity ].
destruct ps₃ as [nz₃| ]; [ idtac | rewrite ps_add_comm; reflexivity ].
simpl in Hn₁, Hn₂.
remember (ps_add fld (NonZero nz₁) (NonZero nz₂)) as x.
remember (ps_add fld (NonZero nz₂) (NonZero nz₃)) as y.
simpl in Heqx, Heqy; subst x y.
unfold nz_add.
rewrite Hn₁, Hn₂; simpl.

bbb.
 remember (nz_valnum ps₁) as v₁ eqn:Hv₁ .
 symmetry in Hv₁.
 destruct v₁ as [v₁| ].
  Focus 2.
bbb.
 remember Hn₁ as Hn₀; clear HeqHn₀.
 apply first_nonzero_nonzero_fin in Hn₀.
 remember (ps_head ps₁) as pm₁.
 remember (ps_head ps₂) as pm₂.
 remember (ps_tail ps₁) as ps'₁.
 remember (ps_tail ps₂) as ps'₂.
 assert (ps_add fld pm₁ ps'₁ ≈ ps₁) as Heq₁.
  constructor 1 with (k₁ := xH) (k₂ := xH).
   do 2 rewrite stretch_series_1.
   constructor; intros i.
   unfold series_nth_fld; simpl.
   remember (stop (nz_terms (pm₁ + ps'₁)%ps)) as st.
   destruct (Nbar.lt_dec (fin i) st) as [Hlt₁| Hge₁].
    subst st.
    destruct (Nbar.lt_dec (fin i) (stop (nz_terms ps₁))) as [Hlt₂| Hge₂].
     unfold ps_add; simpl.
     subst pm₁; simpl.
     subst ps'₁; simpl.
     remember (nz_valnum ps₁) as v₁ eqn:Hv₁ .
     symmetry in Hv₁.
     destruct v₁ as [v₁| ]; simpl.
      Focus 2.
bbb.
 assert (ps_add fld ps'₁ ps'₂ ≈ ps_add fld ps₁ ps₂) as Heq₁₂.
  constructor 1 with (k₁ := xH) (k₂ := xH).
   do 2 rewrite stretch_series_1.
   constructor; intros i.
   unfold ps_add; simpl.
   rewrite Heqps'₁; simpl.
   rewrite Heqps'₂; simpl.
   remember (nz_valnum ps₁) as v₁ eqn:Hv₁ .
   symmetry in Hv₁.
   destruct v₁ as [v₁| ]; simpl.
    remember (nz_valnum ps₂) as v₂ eqn:Hv₂ .
    symmetry in Hv₂.
    destruct v₂ as [v₂| ]; simpl.
     Focus 1.
     unfold ps_add_nz; simpl.
     unfold nz_terms_add; simpl.
     rewrite Hv₁, Hv₂; simpl.
     unfold cm_factor; simpl.
bbb.

(* peut-être inutile *)
Lemma ps_add_nz_assoc : ∀ ps₁ ps₂ ps₃ v₁ v₂ v₃ v₁₂ v₂₃,
  nz_valnum ps₁ = zfin v₁
  → nz_valnum ps₂ = zfin v₂
    → nz_valnum ps₃ = zfin v₃
      → nz_valnum (ps_add_nz fld ps₁ ps₂) = zfin v₁₂
        → nz_valnum (ps_add_nz fld ps₂ ps₃) = zfin v₂₃
          → ps_add_nz fld (ps_add_nz fld ps₁ ps₂) ps₃
            ≈ ps_add_nz fld ps₁ (ps_add_nz fld ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃ v₁ v₂ v₃ v₁₂ v₂₃ Hv₁ Hv₂ Hv₃ Hv₁₂ Hv₂₃.
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 do 2 rewrite stretch_series_1.
 unfold ps_add_nz; simpl.
 remember (first_nonzero fld (nz_terms_add fld ps₁ ps₂)) as sh₁₂.
 remember (first_nonzero fld (nz_terms_add fld ps₂ ps₃)) as sh₂₃.
 symmetry in Heqsh₁₂, Heqsh₂₃.
 destruct sh₁₂ as [sh₁₂| ].
  destruct sh₂₃ as [sh₂₃| ].
   remember (build_ps_add fld sh₁₂ ps₁ ps₂) as ps₁₂.
   remember (build_ps_add fld sh₂₃ ps₂ ps₃) as ps₂₃.
   remember (first_nonzero fld (nz_terms_add fld ps₁₂ ps₃)) as v₁₂_₃.
   remember (first_nonzero fld (nz_terms_add fld ps₁ ps₂₃)) as v₁_₂₃.
   symmetry in Heqv₁₂_₃, Heqv₁_₂₃.
   destruct v₁₂_₃ as [v₁₂_₃| ]; simpl.
    destruct v₁_₂₃ as [v₁_₂₃| ]; simpl.
     constructor; intros i.
     subst ps₁₂ ps₂₃.
     unfold build_ps_add, nz_terms_add, cm_factor, cm; simpl.
     rewrite Hv₁, Hv₂, Hv₃; simpl.
     remember (nz_comden ps₁) as c₁.
     remember (nz_comden ps₂) as c₂.
     remember (nz_comden ps₃) as c₃.
     do 2 rewrite Pos2Z.inj_mul.
     do 2 rewrite Z.mul_assoc.
     do 2 rewrite Z.mul_add_distr_r.
     rewrite <- Z.mul_min_distr_nonneg_r.
      2: apply Pos2Z.is_nonneg.

      rewrite <- Z.mul_min_distr_nonneg_r.
       2: apply Pos2Z.is_nonneg.

       remember (v₁ * ' c₂ * ' c₃)%Z as vcc eqn:Hvcc .
       remember (v₂ * ' c₁ * ' c₃)%Z as cvc eqn:Hcvc .
       remember (v₃ * ' c₁ * ' c₂)%Z as ccv eqn:Hccv .
       rewrite Z.mul_comm, Z.mul_assoc, Z.mul_shuffle0 in Hcvc.
       rewrite <- Z.mul_comm, Z.mul_assoc in Hcvc.
       rewrite <- Hcvc.
       rewrite Z.mul_shuffle0 in Hccv; rewrite <- Hccv.
       do 2 rewrite stretch_series_add_distr.
       do 2 rewrite series_pad_add_distr.
       rewrite series_add_assoc.
       do 4 rewrite stretch_pad_series_distr.
       do 4 rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
       do 4 rewrite series_pad_pad.
       do 4 rewrite Nat.mul_sub_distr_r.
       do 4 rewrite <- Z2Nat_inj_mul_pos_r.
       rewrite <- Hvcc.
       rewrite Z.mul_shuffle0, <- Hcvc.
       rewrite <- Hccv.
       do 2 rewrite <- Z.add_min_distr_r.
       do 2 rewrite Z2Nat.inj_min.
       remember
        (min (Z.to_nat (vcc + Z.of_nat sh₁₂ * ' c₃))
           (Z.to_nat (cvc + Z.of_nat sh₁₂ * ' c₃))) as toto.
       remember
        (min (Z.to_nat (cvc + Z.of_nat sh₂₃ * ' c₁))
           (Z.to_nat (ccv + Z.of_nat sh₂₃ * ' c₁))) as titi.
       Focus 1.
bbb.
       Unfocus.
       Focus 2.
bbb.
       rewrite Heqps₁₂ in Heqv₁₂_₃.
       rewrite Heqps₂₃ in Heqv₁_₂₃.
       apply eq_first_nonzero in Heqv₁₂_₃.
       assert (fin v₁₂_₃ < inf)%Nbar as H by constructor.
       rewrite <- Heqv₁_₂₃ in H.
       apply lt_first_nonzero in H.
bbb.
       rewrite <- zzz in H; try eassumption.
       contradiction.
bbb.
*)

(* peut-être inutile *)
Theorem ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  ps_add fld (ps_add fld ps₁ ps₂) ps₃ ≈ ps_add fld ps₁ (ps_add fld ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃.
unfold ps_add.
remember (nz_valnum ps₁) as v₁.
remember (nz_valnum ps₂) as v₂.
remember (nz_valnum ps₃) as v₃.
symmetry in Heqv₁, Heqv₂, Heqv₃.
destruct v₁ as [v₁| ]; simpl.
 destruct v₂ as [v₂| ]; [ idtac | rewrite Heqv₁, Heqv₃; reflexivity ].
 destruct v₃ as [v₃| ]; simpl.
  remember (nz_valnum (ps_add_nz fld ps₁ ps₂)) as v₁₂.
  symmetry in Heqv₁₂.
  remember (nz_valnum (ps_add_nz fld ps₂ ps₃)) as v₂₃.
  symmetry in Heqv₂₃.
  destruct v₁₂ as [v₁₂| ].
   destruct v₂₃ as [v₂₃| ].
   Focus 1.
bbb.

intros ps₁ ps₂ ps₃.
unfold ps_add, cm_factor; simpl.
remember (nz_valnum ps₁) as v₁.
remember (nz_valnum ps₂) as v₂.
remember (nz_valnum ps₃) as v₃.
remember (nz_comden ps₁) as c₁.
remember (nz_comden ps₂) as c₂.
remember (nz_comden ps₃) as c₃.
symmetry in Heqv₁, Heqv₂, Heqv₃, Heqc₁, Heqc₂, Heqc₃.
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 destruct v₁ as [v₁| ]; simpl.
  destruct v₂ as [v₂| ]; simpl.
   destruct v₃ as [v₃| ]; simpl.
    unfold ps_add_nz, nz_terms_add; simpl.
    rewrite Heqv₁, Heqv₂, Heqv₃, Heqc₁, Heqc₂.
    do 2 rewrite stretch_series_1.
    remember (Zbar.min (zfin v₁ * '' c₂) (zfin v₂ * '' c₁)) as m₁.
    remember (Zbar.min (zfin v₂ * '' c₃) (zfin v₃ * '' c₂)) as m₂.
    remember (m₁ * '' c₃)%Zbar as m₁c₃ eqn:Hm₁c₃ .
    remember (m₂ * '' c₁)%Zbar as m₂c₁ eqn:Hm₂c₁ .
    rewrite Heqm₁ in Hm₁c₃.
    rewrite Heqm₂ in Hm₂c₁.
    symmetry in Heqm₁, Heqm₂.
    destruct m₁ as [m₁| ]; simpl.
     destruct m₂ as [m₂| ]; simpl.
      subst m₁c₃ m₂c₁; simpl.
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
      do 2 rewrite stretch_series_add_distr.
      do 2 rewrite series_pad_add_distr.
      rewrite series_add_assoc.
      do 4 rewrite stretch_pad_series_distr.
      do 4 rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
      do 4 rewrite series_pad_pad.
      do 4 rewrite Nat.mul_sub_distr_r.
      do 4 rewrite <- Z2Nat_inj_mul_pos_r.
      rewrite <- Hvcc.
      rewrite Z.mul_shuffle0, <- Hcvc.
      rewrite <- Hccv.
      do 2 rewrite Z2Nat.inj_min.
      do 2 rewrite min_sub_add_sub.
      rewrite Nat.min_comm, min_sub_add_sub, series_add_comm.
      rewrite Nat.min_comm, min_sub_add_sub, series_add_comm.
      rewrite Pos.mul_comm, series_add_comm, Nat.min_comm.
      rewrite Pos.mul_comm, series_add_comm.
      reflexivity.

      exfalso.
      rewrite <- Zbar.zfin_inj_mul in Heqm₂.
      rewrite <- Zbar.zfin_inj_mul in Heqm₂.
      unfold Zbar.min, Zbar.binop in Heqm₂.
      discriminate Heqm₂.

     exfalso.
     rewrite <- Zbar.zfin_inj_mul in Heqm₁.
     rewrite <- Zbar.zfin_inj_mul in Heqm₁.
     unfold Zbar.min, Zbar.binop in Heqm₁.
     discriminate Heqm₁.

    rewrite Heqv₁, Heqv₂, Heqc₂; reflexivity.

   destruct v₃ as [v₃| ]; simpl.
    rewrite Heqv₁, Heqv₃, Heqc₁, Heqc₃; reflexivity.

    rewrite Heqv₁, Heqv₃; reflexivity.

  rewrite Heqv₂, Heqc₂; reflexivity.

 destruct v₁ as [v₁| ]; [ simpl | subst; reflexivity ].
 destruct v₂ as [v₂| ]; [ simpl | rewrite Heqv₁; subst; reflexivity ].
 destruct v₃ as [v₃| ]; [ simpl | rewrite Heqv₁, Heqv₂, Heqc₂; reflexivity ].
 unfold build_ps; simpl.
 rewrite Heqv₁, Heqv₂, Heqv₃, Heqc₁, Heqc₂.
 remember (Zbar.min (zfin v₁ * '' c₂) (zfin v₂ * '' c₁)) as m₁.
 remember (Zbar.min (zfin v₂ * '' c₃) (zfin v₃ * '' c₂)) as m₂.
 remember (m₁ * '' c₃)%Zbar as m₁c₃ eqn:Hm₁c₃ .
 remember (m₂ * '' c₁)%Zbar as m₂c₁ eqn:Hm₂c₁ .
 rewrite Heqm₁ in Hm₁c₃.
 rewrite Heqm₂ in Hm₂c₁.
 symmetry in Heqm₁, Heqm₂.
 destruct m₁ as [m₁| ]; simpl.
  destruct m₂ as [m₂| ]; simpl.
   do 2 rewrite Zbar.mul_1_r.
   subst m₁c₃.
   symmetry in Hm₂c₁.
   destruct m₂c₁ as [m₂c₁| ].
    rewrite <- Zbar.mul_min_distr_nonneg_r.
     simpl.
     do 2 rewrite Pos2Z.inj_mul.
     do 2 rewrite Z.mul_assoc.
     rewrite <- Z.min_assoc.
     do 2 f_equal.
     rewrite Z.mul_shuffle0, Z.min_comm, Z.mul_shuffle0.
     rewrite Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
     rewrite Z.min_comm.
     simpl in Hm₂c₁.
     injection Hm₂c₁; intros; assumption.

     apply Pos2Zbar.is_nonneg.

    exfalso.
    rewrite <- Zbar.zfin_inj_mul in Hm₂c₁.
    rewrite <- Zbar.zfin_inj_mul in Hm₂c₁.
    unfold Zbar.min, Zbar.binop in Hm₂c₁.
    discriminate Hm₂c₁.

   exfalso.
   rewrite <- Zbar.zfin_inj_mul in Heqm₂.
   rewrite <- Zbar.zfin_inj_mul in Heqm₂.
   unfold Zbar.min, Zbar.binop in Heqm₂.
   discriminate Heqm₂.

  exfalso.
  rewrite <- Zbar.zfin_inj_mul in Heqm₁.
  rewrite <- Zbar.zfin_inj_mul in Heqm₁.
  unfold Zbar.min, Zbar.binop in Heqm₁.
  discriminate Heqm₁.

 destruct v₁ as [v₁| ]; [ simpl | subst; reflexivity ].
 destruct v₂ as [v₂| ]; [ simpl | rewrite Heqv₁; subst; reflexivity ].
 destruct v₃ as [v₃| ]; [ simpl | rewrite Heqv₁, Heqv₂, Heqc₂; reflexivity ].
 rewrite Heqv₁, Heqv₂, Heqv₃, Heqc₁, Heqc₂; simpl.
 rewrite Pos.mul_assoc; reflexivity.
Qed.
*)

Theorem ps_add_ident : ∀ ps, ps_add fld (ps_zero fld) ps ≈ ps.
Proof. reflexivity. Qed.

Definition series_neg s :=
  {| terms i := neg fld (terms s i); stop := stop s |}.

Definition ps_neg ps :=
  {| nz_terms := series_neg (nz_terms ps);
     nz_valnum := nz_valnum ps;
     nz_comden := nz_comden ps |}.

Lemma add_neg_nth : ∀ s i,
  add fld (series_nth_fld fld i s) (series_nth_fld fld i (series_neg s)) ≍
  zero fld.
Proof.
intros s i.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin i) (stop s)).
 apply fld_add_neg.

 apply fld_add_ident.
Qed.

Theorem ps_add_neg : ∀ ps, ps_add fld ps (ps_neg ps) ≈ ps_zero fld.
Proof.
intros ps.
constructor 2; [ idtac | reflexivity ].
unfold ps_add; simpl.
remember (nz_valnum ps) as v.
symmetry in Heqv.
destruct v as [v| ]; [ simpl | assumption ].
unfold ps_add_nz; simpl.
remember (adjust fld (nz_comden ps) ps) as ps₁.
remember (adjust fld (cm_factor (ps_neg ps) ps) (ps_neg ps)) as ps₂.
remember (first_nonzero fld (nz_terms_add fld ps₁ ps₂)) as w.
symmetry in Heqw.
destruct w; [ simpl | reflexivity ].
apply first_nonzero_fin in Heqw.
exfalso; apply Heqw; clear Heqw; intros i.
rewrite Heqps₁, Heqps₂.
unfold nz_terms_add, ps_neg, cm_factor; simpl.
rewrite Nat.sub_diag.
unfold series_add, series_nth_fld; simpl.
rewrite Nbar.add_0_r, Nat.sub_0_r, Nbar.max_id.
remember (stop (nz_terms ps) * fin (Pos.to_nat (nz_comden ps)))%Nbar as y.
destruct (Nbar.lt_dec (fin i) y); [ idtac | reflexivity ].
destruct (zerop (i mod Pos.to_nat (nz_comden ps))) as [Hz| Hnz].
 unfold series_neg; simpl.
 unfold series_nth_fld; simpl.
 remember (fin (i / Pos.to_nat (nz_comden ps))) as z.
 destruct (Nbar.lt_dec z (stop (nz_terms ps))) as [Hlt| Hge].
  apply fld_add_neg.

  apply fld_add_ident.

 apply fld_add_ident.
Qed.

Lemma ps_add_cancel_l : ∀ ps₁ ps₂ ps₃,
  ps₂ ≈ ps₃
  → ps_add fld ps₁ ps₂ ≈ ps_add fld ps₁ ps₃.
Proof.
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
  destruct (lt_dec 0 (Pos.to_nat (nz_comden nz))) as [Hlt| Hge].
   rewrite Nbar.mul_1_r.
   remember (stop (nz_terms nz)) as st.
   destruct st as [st| ]; simpl.
    destruct (lt_dec 0 st) as [Hlt₁| Hge₁].
     rewrite Nat.mod_0_l; simpl.
      rewrite fld_mul_ident; reflexivity.

      apply Pos2Nat_ne_0.

     apply not_gt in Hge₁.
     apply Nat.le_0_r in Hge₁.
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
    destruct (lt_dec i st) as [Hlt| Hge].
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
     fld_add_ident := ps_add_ident;
     fld_add_compat := ps_add_compat;
     fld_mul_ident := ps_mul_ident |}.

End fld₃.
