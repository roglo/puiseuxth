(* $Id: Puiseux_series.v,v 1.376 2013-08-30 02:40:33 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Misc.
Require Import Series.
Require Import Nbar.
Require Import Zbar.

Set Implicit Arguments.

(* [series_head fld s] return the position of the first non null
   coefficient in the series [s]. *)
Definition series_head : ∀ α, field α → series α → Nbar.
Admitted.

Axiom series_head_inf : ∀ α (fld : field α) s,
  (∀ i, fld_eq fld (series_nth_fld fld i s) (zero fld))
  → series_head fld s = inf.

Add Parametric Morphism α (fld : field α) : (series_head fld)
with signature (eq_series fld) ==> eq as series_head_morph.
Admitted.

Section fld.

Variable α : Type.
Variable fld : field α.
Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).

Definition stretch_series k s :=
  {| terms i :=
       if zerop (i mod Pos.to_nat k) then
         series_nth_fld fld (i / Pos.to_nat k) s
       else zero fld;
     stop :=
       stop s * fin (Pos.to_nat k) |}.

Record puiseux_series α := mkps
  { ps_terms : series α;
    ps_valnum : Zbar;
    ps_comden : positive;
    ps_prop : series_nth 0 ps_terms = None → ps_valnum = ∞ }.

Inductive eq_ps : puiseux_series α → puiseux_series α → Prop :=
  | eq_ps_base : ∀ k₁ k₂ ps₁ ps₂,
      stretch_series k₁ (ps_terms ps₁) ≃
      stretch_series k₂ (ps_terms ps₂)
      → (ps_valnum ps₁ * ''k₁)%Zbar =
        (ps_valnum ps₂ * ''k₂)%Zbar
        → (ps_comden ps₁ * k₁)%positive =
          (ps_comden ps₂ * k₂)%positive
          → eq_ps ps₁ ps₂
  | eq_ps_zero : ∀ ps₁ ps₂,
      ps_valnum ps₁ = ∞
      → ps_valnum ps₂ = ∞
        → eq_ps ps₁ ps₂.

Notation "a ≈ b" := (eq_ps a b) (at level 70).

Definition ps_zero : puiseux_series α :=
  {| ps_terms := series_0 fld;
     ps_valnum := ∞;
     ps_comden := 1;
     ps_prop := λ _, eq_refl |}.

Lemma ps_monom_prop : ∀ (c : α) pow,
  series_nth 0 {| terms i := c; stop := 1 |} = None → zfin (Qnum pow) = ∞.
Proof.
intros c pow Hs.
unfold series_nth in Hs; simpl in Hs.
discriminate Hs.
Qed.

Definition ps_monom (c : α) pow :=
  {| ps_terms := {| terms i := c; stop := 1 |};
     ps_valnum := zfin (Qnum pow);
     ps_comden := Qden pow;
     ps_prop := ps_monom_prop pow |}.

Definition ps_const c : puiseux_series α := ps_monom c 0.
Definition ps_one := ps_const (one fld).

Lemma series_head_fin : ∀ s v,
  series_head fld s = fin v
  → not (∀ i : nat, series_nth_fld fld i s ≍ zero fld).
Proof.
intros s v Hf H.
apply series_head_inf in H.
rewrite Hf in H; discriminate H.
Qed.

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
inversion H₁ as [k₁₁ k₁₂ a b Hss₁ Hvv₁ Hck₁| a b Hvv₁ Hvv₂]; subst.
 inversion H₂ as [k₂₁ k₂₂ a b Hss₂ Hvv₂ Hck₂| a b Hvv₂ Hvv₃]; subst.
  apply Zbar.mul_cancel_r with (p := '' k₂₁) in Hvv₁.
   apply Zbar.mul_cancel_r with (p := '' k₁₂) in Hvv₂.
    rewrite Zbar.mul_shuffle0 in Hvv₂.
    rewrite <- Hvv₁ in Hvv₂.
    do 2 rewrite <- Zbar.mul_assoc in Hvv₂.
    apply Pos.mul_cancel_r with (r := k₂₁) in Hck₁.
    apply Pos.mul_cancel_r with (r := k₁₂) in Hck₂.
    rewrite Pos_mul_shuffle0 in Hck₂.
    rewrite <- Hck₁ in Hck₂.
    do 2 rewrite <- Pos.mul_assoc in Hck₂.
    econstructor; try eassumption.
    symmetry; rewrite Pos.mul_comm.
    rewrite stretch_stretch_series; try apply Pos2Nat_ne_0.
    symmetry; rewrite Pos.mul_comm.
    rewrite stretch_stretch_series; try apply Pos2Nat_ne_0.
    rewrite Hss₁, <- Hss₂.
    rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
    rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
    rewrite Pos.mul_comm; reflexivity.

    apply Zbar.pos_ne_0.

   apply Zbar.pos_ne_0.

  rewrite Hvv₂ in Hvv₁; simpl in Hvv₁.
  constructor 2; [ idtac | assumption ].
  remember (ps_valnum ps₁) as v.
  destruct v; [ discriminate Hvv₁ | reflexivity ].

 constructor 2; [ assumption | idtac ].
 inversion H₂ as [k₂₁ k₂₂ a b Hss₂ Hvv₂'| ]; [ subst | assumption ].
 rewrite Hvv₂ in Hvv₂'; simpl in Hvv₂'.
 remember (ps_valnum ps₃) as v.
 symmetry in Hvv₂'.
 destruct v; [ discriminate Hvv₂' | assumption ].
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
  match ps_valnum ps with
  | zfin v =>
      match series_head fld (ps_terms ps) with
      | fin n => Some (v + Z.of_nat n # ps_comden ps)
      | inf => None
      end
  | ∞ => None
  end.

Definition valuation_coeff (ps : puiseux_series α) :=
  match series_head fld (ps_terms ps) with
  | fin n => series_nth_fld fld n (ps_terms ps)
  | inf => zero fld
  end.

Lemma adjust_prop : ∀ k ps,
  series_nth 0 (stretch_series fld k (ps_terms ps)) = None
  → (ps_valnum ps * ''k)%Zbar = ∞.
Proof.
intros k ps Hs.
remember (ps_valnum ps) as v.
symmetry in Heqv.
destruct v; [ idtac | reflexivity ].
apply zfin_not_zinf in Heqv.
exfalso; apply Heqv; clear Heqv.
apply (ps_prop ps).
unfold series_nth in Hs |-*; simpl in Hs.
destruct (stop (ps_terms ps)) as [st| ]; [ simpl in Hs | discriminate Hs ].
remember (st * Pos.to_nat k)%nat as n.
destruct (lt_dec 0 n) as [| Hge]; [ discriminate Hs | subst n ].
destruct (lt_dec 0 st) as [Hlt₁| ]; [ exfalso | reflexivity ].
apply Hge; clear Hge.
apply Nat.mul_pos_pos; [ assumption | idtac ].
apply Pos2Nat.is_pos.
Qed.

Definition adjust k ps :=
  {| ps_terms := stretch_series fld k (ps_terms ps);
     ps_valnum := ps_valnum ps * ''k;
     ps_comden := ps_comden ps * k;
     ps_prop := adjust_prop k ps |}.

(* ps_add *)

Definition series_pad_left n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n);
     stop := stop s + fin n |}.

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

Definition ps_terms_add ps₁ ps₂ :=
  let aps₁ := adjust (cm_factor ps₁ ps₂) ps₁ in
  let aps₂ := adjust (cm_factor ps₂ ps₁) ps₂ in
  let v₁ := ps_valnum aps₁ in
  let v₂ := ps_valnum aps₂ in
  series_add fld
    (series_pad_left (Zbar.to_nat v₁ - Zbar.to_nat v₂)%nat
       (ps_terms aps₁))
    (series_pad_left (Zbar.to_nat v₂ - Zbar.to_nat v₁)%nat
       (ps_terms aps₂)).

Lemma build_ps_add_prop : ∀ (s : series α) v (ps₁ ps₂ : puiseux_series α),
  series_nth 0 s = None
  → (Zbar.min
       (ps_valnum (adjust (cm_factor ps₁ ps₂) ps₁))
       (ps_valnum (adjust (cm_factor ps₂ ps₁) ps₂))
     + Zbar.of_nat v)%Zbar = ∞.
Proof.
intros s v ps₁ ps₂ Hs.
remember (adjust (cm_factor ps₁ ps₂) ps₁) as aps₁ eqn:Haps₁ .
remember (adjust (cm_factor ps₂ ps₁) ps₂) as aps₂ eqn:Haps₂ .
remember (ps_valnum aps₁) as v₁ eqn:Hv₁ .
remember (ps_valnum aps₂) as v₂ eqn:Hv₂ .
symmetry in Hv₁, Hv₂.
destruct (Zbar.min_dec v₁ v₂) as [Hv| Hv]; rewrite Hv.
 rewrite <- Hv₁.
 apply Zbar.eq_add_inf_l.
 apply (ps_prop aps₁).
bbb.
*)

Definition build_ps_add (s : series α) v (ps₁ ps₂ : puiseux_series α) :=
  let aps₁ := adjust (cm_factor ps₁ ps₂) ps₁ in
  let aps₂ := adjust (cm_factor ps₂ ps₁) ps₂ in
  let v₁ := ps_valnum aps₁ in
  let v₂ := ps_valnum aps₂ in
  {| ps_terms := s;
     ps_valnum := Zbar.min v₁ v₂ + Zbar.of_nat v;
     ps_comden := cm ps₁ ps₂;
     ps_prop := build_ps_add_prop s v ps₁ ps₂ |}.

Definition ps_add_nz ps₁ ps₂ :=
  let s := ps_terms_add ps₁ ps₂ in
  match series_head fld s with
  | fin v => build_ps_add s v ps₁ ps₂
  | inf => ps_zero fld
  end.

Definition ps_add (ps₁ ps₂ : puiseux_series α) :=
  match ps_valnum ps₁ with
  | zfin _ =>
      match ps_valnum ps₂ with
      | zfin _ => ps_add_nz ps₁ ps₂
      | ∞ => ps₁
      end
  | ∞ => ps₂
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
  match ps_valnum ps₁ with
  | zfin _ =>
      match ps_valnum ps₂ with
      | zfin _ =>
          let aps₁ := adjust (cm_factor ps₁ ps₂) ps₁ in
          let aps₂ := adjust (cm_factor ps₂ ps₁) ps₂ in
          {| ps_terms := series_mul_term (ps_terms aps₁) (ps_terms aps₂);
             ps_valnum := ps_valnum aps₁ + ps_valnum aps₂;
             ps_comden := ps_comden aps₁ |}
      | ∞ => ps_zero fld
      end
  | ∞ => ps_zero fld
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

Lemma ps_terms_add_comm : ∀ ps₁ ps₂,
  ps_terms_add fld ps₁ ps₂ ≃ ps_terms_add fld ps₂ ps₁.
Proof.
intros ps₁ ps₂.
apply series_add_comm.
Qed.

Lemma ps_add_nz_comm : ∀ ps₁ ps₂,
  ps_add_nz fld ps₁ ps₂ ≈ ps_add_nz fld ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_add_nz.
rewrite ps_terms_add_comm.
remember (series_head fld (ps_terms_add fld ps₂ ps₁)) as v.
symmetry in Heqv.
destruct v as [v| ]; [ idtac | reflexivity ].
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 rewrite ps_terms_add_comm; reflexivity.

 rewrite Zbar.min_comm; reflexivity.

 unfold cm.
 do 2 rewrite Pos.mul_1_r; apply Pos.mul_comm.
Qed.

Theorem ps_add_comm : ∀ ps₁ ps₂, ps_add fld ps₁ ps₂ ≈ ps_add fld ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_add; simpl.
remember (ps_valnum ps₁) as v₁.
remember (ps_valnum ps₂) as v₂.
symmetry in Heqv₁, Heqv₂.
destruct v₁ as [v₁| ].
 destruct v₂ as [v₂| ]; [ idtac | reflexivity ].
 apply ps_add_nz_comm.

 destruct v₂ as [n₂| ]; [ reflexivity | idtac ].
 constructor 2; assumption.
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

Lemma ps_comden_adjust : ∀ c ps,
  ps_comden (adjust fld c ps) = (ps_comden ps * c)%positive.
Proof. intros; reflexivity. Qed.

Lemma ps_valnum_ps_add_nz : ∀ ps₁ ps₂,
  ps_valnum (ps_add_nz fld ps₁ ps₂)
  = (Zbar.of_Nbar (series_head fld (ps_terms_add fld ps₁ ps₂)) +
     Zbar.min (ps_valnum ps₁ * '' cm_factor ps₁ ps₂)
        (ps_valnum ps₂ * '' cm_factor ps₂ ps₁))%Zbar.
Proof.
intros ps₁ ps₂.
unfold ps_add_nz.
remember (series_head fld (ps_terms_add fld ps₁ ps₂)) as v.
destruct v as [v| ]; [ simpl | reflexivity ].
remember (ps_valnum ps₁ * '' cm_factor ps₁ ps₂)%Zbar as v₁.
remember (ps_valnum ps₂ * '' cm_factor ps₂ ps₁)%Zbar as v₂.
destruct (Zbar.min v₁ v₂) as [v₁₂| ]; [ simpl | reflexivity ].
rewrite Z.add_comm; reflexivity.
Qed.

Lemma zzz : ∀ ps₁ ps₂ ps₃ v₁ v₂ v₃ n₁₂ n₂₃,
  ps_valnum ps₁ = zfin v₁
  → ps_valnum ps₂ = zfin v₂
    → ps_valnum ps₃ = zfin v₃
      → series_head fld (ps_terms_add fld ps₁ ps₂) = fin n₁₂
        → series_head fld (ps_terms_add fld ps₂ ps₃) = fin n₂₃
          → ps_terms_add fld
              (build_ps_add fld (ps_terms_add fld ps₁ ps₂) n₁₂ ps₁ ps₂) ps₃ ≃
            ps_terms_add fld
              ps₁ (build_ps_add fld (ps_terms_add fld ps₂ ps₃) n₂₃ ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃ v₁ v₂ v₃ n₁₂ n₂₃ Hv₁ Hv₂ Hv₃ Hn₁ Hn₂.
destruct n₁₂ as [n₁₂| ].
 destruct n₂₃ as [n₂₃| ].
  constructor; intros i.
  unfold build_ps_add; simpl.
  unfold cm_factor, cm.
  unfold ps_terms_add; simpl.
  unfold cm_factor, cm.
  rewrite Hv₁, Hv₂, Hv₃; simpl.
  remember (ps_comden ps₁) as c₁.
  remember (ps_comden ps₂) as c₂.
  remember (ps_comden ps₃) as c₃.
  do 2 rewrite stretch_series_add_distr.
  do 2 rewrite series_pad_add_distr.
  rewrite series_add_assoc.
  do 4 rewrite stretch_pad_series_distr.
  do 4 rewrite <- stretch_stretch_series; try apply Pos2Nat_ne_0.
  do 4 rewrite series_pad_pad.
  do 4 rewrite Nat.mul_sub_distr_r.
  do 4 rewrite <- Z2Nat_inj_mul_pos_r.
  remember (v₁ * ' c₂ * ' c₃)%Z as vcc eqn:Hvcc .
  remember (v₂ * ' c₁ * ' c₃)%Z as cvc eqn:Hcvc .
  remember (v₃ * ' c₂ * ' c₁)%Z as ccv eqn:Hccv .
  rewrite Z.mul_shuffle0, <- Hcvc.
  do 2 rewrite <- Z.add_min_distr_r.
  rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
  rewrite <- Z.mul_min_distr_nonneg_r; [ idtac | apply Pos2Z.is_nonneg ].
  do 4 rewrite Z.mul_add_distr_r.
  do 2 rewrite Pos2Z.inj_mul.
  do 2 rewrite Z.mul_assoc.
  rewrite <- Hvcc, <- Hcvc, <- Hccv.
  rewrite Z.mul_shuffle0, <- Hccv.
  rewrite Z.mul_shuffle0, <- Hcvc.
  do 2 rewrite Z2Nat.inj_min.
  simpl.
  do 3 rewrite Z.add_0_r.
  do 2 rewrite min_sub_add_sub.
  rewrite Nat.min_comm.
  rewrite min_sub_add_sub.
  replace (min (Z.to_nat vcc) (Z.to_nat cvc)) with
   (min (Z.to_nat cvc) (Z.to_nat vcc)) by apply Nat.min_comm.
  rewrite min_sub_add_sub.
  replace (min (Z.to_nat vcc) (Z.to_nat ccv)) with
   (min (Z.to_nat ccv) (Z.to_nat vcc)) by apply Nat.min_comm.
  rewrite Pos.mul_comm.
  replace (c₃ * c₁)%positive with (c₁ * c₃)%positive by apply Pos.mul_comm.
  reflexivity.

bbb.
  unfold ps_terms_add in Hn₂.
  simpl in Hn₂.
  unfold cm_factor in Hn₂.
  rewrite Hv₂, Hv₃ in Hn₂.
  rewrite Zbar2Nat.inj_mul_pos_r in Hn₂; simpl in Hn₂.
  rewrite Z2Nat_inj_mul_pos_r in Hn₂; simpl in Hn₂.
bbb.

Lemma ps_add_nz_assoc : ∀ ps₁ ps₂ ps₃ v₁ v₂ v₃ v₁₂ v₂₃,
  ps_valnum ps₁ = zfin v₁
  → ps_valnum ps₂ = zfin v₂
    → ps_valnum ps₃ = zfin v₃
      → ps_valnum (ps_add_nz fld ps₁ ps₂) = zfin v₁₂
        → ps_valnum (ps_add_nz fld ps₂ ps₃) = zfin v₂₃
          → ps_add_nz fld (ps_add_nz fld ps₁ ps₂) ps₃
            ≈ ps_add_nz fld ps₁ (ps_add_nz fld ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃ v₁ v₂ v₃ v₁₂ v₂₃ Hv₁ Hv₂ Hv₃ Hv₁₂ Hv₂₃.
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 do 2 rewrite stretch_series_1.
 unfold ps_add_nz; simpl.
 remember (series_head fld (ps_terms_add fld ps₁ ps₂)) as sh₁₂.
 remember (series_head fld (ps_terms_add fld ps₂ ps₃)) as sh₂₃.
 symmetry in Heqsh₁₂, Heqsh₂₃.
 destruct sh₁₂ as [sh₁₂| ].
  destruct sh₂₃ as [sh₂₃| ].
   remember (ps_terms_add fld ps₁ ps₂) as s₁₂.
   remember (ps_terms_add fld ps₂ ps₃) as s₂₃.
   remember (build_ps_add fld s₁₂ sh₁₂ ps₁ ps₂) as ps₁₂.
   remember (build_ps_add fld s₂₃ sh₂₃ ps₂ ps₃) as ps₂₃.
   remember (series_head fld (ps_terms_add fld ps₁₂ ps₃)) as v₁₂_₃.
   remember (series_head fld (ps_terms_add fld ps₁ ps₂₃)) as v₁_₂₃.
   symmetry in Heqv₁₂_₃, Heqv₁_₂₃.
   destruct v₁₂_₃ as [v₁₂_₃| ]; simpl.
    destruct v₁_₂₃ as [v₁_₂₃| ]; simpl.
     constructor; intros i.
     subst ps₁₂ ps₂₃ s₁₂ s₂₃.
     unfold build_ps_add, ps_terms_add, cm_factor, cm; simpl.
     rewrite Hv₁, Hv₂, Hv₃; simpl.
     remember (ps_comden ps₁) as c₁.
     remember (ps_comden ps₂) as c₂.
     remember (ps_comden ps₃) as c₃.
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
       Unfocus.
       Focus 2.
       unfold ps_add_nz in Hv₂₃.
       rewrite <- Heqs₂₃ in Hv₂₃.
       rewrite Heqsh₂₃ in Hv₂₃.
       rewrite <- Heqps₂₃ in Hv₂₃.
       unfold ps_add_nz in Hv₁₂.
       rewrite <- Heqs₁₂, Heqsh₁₂, <- Heqps₁₂ in Hv₁₂.
bbb.
*)

Theorem ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  ps_add fld (ps_add fld ps₁ ps₂) ps₃ ≈ ps_add fld ps₁ (ps_add fld ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃.
unfold ps_add.
remember (ps_valnum ps₁) as v₁.
remember (ps_valnum ps₂) as v₂.
remember (ps_valnum ps₃) as v₃.
symmetry in Heqv₁, Heqv₂, Heqv₃.
destruct v₁ as [v₁| ]; simpl.
 destruct v₂ as [v₂| ]; [ idtac | rewrite Heqv₁, Heqv₃; reflexivity ].
 destruct v₃ as [v₃| ]; simpl.
  remember (ps_valnum (ps_add_nz fld ps₁ ps₂)) as v₁₂.
  symmetry in Heqv₁₂.
  remember (ps_valnum (ps_add_nz fld ps₂ ps₃)) as v₂₃.
  symmetry in Heqv₂₃.
  destruct v₁₂ as [v₁₂| ].
   destruct v₂₃ as [v₂₃| ].
   Focus 1.
bbb.

intros ps₁ ps₂ ps₃.
unfold ps_add, cm_factor; simpl.
remember (ps_valnum ps₁) as v₁.
remember (ps_valnum ps₂) as v₂.
remember (ps_valnum ps₃) as v₃.
remember (ps_comden ps₁) as c₁.
remember (ps_comden ps₂) as c₂.
remember (ps_comden ps₃) as c₃.
symmetry in Heqv₁, Heqv₂, Heqv₃, Heqc₁, Heqc₂, Heqc₃.
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 destruct v₁ as [v₁| ]; simpl.
  destruct v₂ as [v₂| ]; simpl.
   destruct v₃ as [v₃| ]; simpl.
    unfold ps_add_nz, ps_terms_add; simpl.
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
  {| ps_terms := series_neg (ps_terms ps);
     ps_valnum := ps_valnum ps;
     ps_comden := ps_comden ps |}.

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
remember (ps_valnum ps) as v.
symmetry in Heqv.
destruct v as [v| ]; [ simpl | assumption ].
unfold ps_add_nz; simpl.
remember (adjust fld (ps_comden ps) ps) as ps₁.
remember (adjust fld (cm_factor (ps_neg ps) ps) (ps_neg ps)) as ps₂.
remember (series_head fld (ps_terms_add fld ps₁ ps₂)) as w.
symmetry in Heqw.
destruct w; [ simpl | reflexivity ].
apply series_head_fin in Heqw.
exfalso; apply Heqw; clear Heqw; intros i.
rewrite Heqps₁, Heqps₂.
unfold ps_terms_add, ps_neg, cm_factor; simpl.
rewrite Nat.sub_diag.
unfold series_add, series_nth_fld; simpl.
rewrite Nbar.add_0_r, Nat.sub_0_r, Nbar.max_id.
remember (stop (ps_terms ps) * fin (Pos.to_nat (ps_comden ps)))%Nbar as y.
destruct (Nbar.lt_dec (fin i) y); [ idtac | reflexivity ].
destruct (zerop (i mod Pos.to_nat (ps_comden ps))) as [Hz| Hnz].
 unfold series_neg; simpl.
 unfold series_nth_fld; simpl.
 remember (fin (i / Pos.to_nat (ps_comden ps))) as z.
 destruct (Nbar.lt_dec z (stop (ps_terms ps))) as [Hlt| Hge].
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
 remember (ps_valnum ps₁) as v₁.
 remember (ps_valnum ps₂) as v₂.
 remember (ps_valnum ps₃) as v₃.
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
   replace (k₂₁ * ps_comden ps₁)%positive with
    (ps_comden ps₁ * k₂₁)%positive by apply Pos.mul_comm.
   do 2 rewrite stretch_stretch_series.
   rewrite Hss₂.
   do 2 rewrite <- stretch_stretch_series.
   replace (ps_comden ps₁ * k₂₂)%positive with
    (k₂₂ * ps_comden ps₁)%positive by apply Pos.mul_comm.
   replace (v₂ * ' (ps_comden ps₁ * k₂₁))%Z with
    (v₃ * ' (k₂₂ * ps_comden ps₁))%Z .
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

 remember (ps_valnum ps₁) as v₁.
 remember (ps_valnum ps₂) as v₂.
 remember (ps_valnum ps₃) as v₃.
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
  remember (ps_valnum nz₁) as v₁.
  remember (ps_comden nz₁) as c₁.
  remember (ps_comden nz₂₁) as c₂₁.
  remember (ps_comden nz₂₂) as c₂₂.
  remember (ps_valnum nz₂₁) as v₂₁.
  remember (ps_valnum nz₂₂) as v₂₂.
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
  destruct (lt_dec 0 (Pos.to_nat (ps_comden nz))) as [Hlt| Hge].
   rewrite Nbar.mul_1_r.
   remember (stop (ps_terms nz)) as st.
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
