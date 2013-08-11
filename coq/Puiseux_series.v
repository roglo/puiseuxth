(* $Id: Puiseux_series.v,v 1.186 2013-08-11 18:10:17 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Misc.
Require Import Series.

Set Implicit Arguments.

(*
Axiom functional_extensionality : ∀ α β (f g : α → β),
  (∀ x, f x = g x) → f = g.
*)

Record puiseux_series α := mkps
  { ps_terms : series α;
    ps_valnum : Z;
    ps_comden : positive }.

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
       match stop s with
       | Some st => Some (st * k)%nat
       | None => None
       end |}.

Notation "a ≃ b" := (eq_series fld a b) (at level 70).
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).

Inductive eq_ps : puiseux_series α → puiseux_series α → Prop :=
  | eq_ps_base : ∀ k₁ k₂ ps₁ ps₂,
      stretch_series (Pos.to_nat k₁) (ps_terms ps₁) ≃
      stretch_series (Pos.to_nat k₂) (ps_terms ps₂)
      → (ps_valnum ps₁ * 'k₁ = ps_valnum ps₂ * 'k₂)%Z
        → (ps_comden ps₁ * k₁ = ps_comden ps₂ * k₂)%positive
          → eq_ps ps₁ ps₂.

Notation "a ≈ b" := (eq_ps a b) (at level 70).

(*
Lemma PQmul_comm : ∀ p₁ p₂ q,
  PQmul p₁ (PQmul p₂ q) = PQmul p₂ (PQmul p₁ q).
Proof.
intros p₁ p₂ (qn, dn).
unfold PQmul; simpl.
destruct qn; [ reflexivity | idtac | idtac ].
 do 2 rewrite Pos.mul_assoc.
 do 3 f_equal.
 apply Pos.mul_comm.

 do 2 rewrite Pos.mul_assoc.
 do 3 f_equal.
 apply Pos.mul_comm.
Qed.

Lemma PQmul_mul_distr : ∀ p₁ p₂ q, PQmul (p₁ * p₂) q = PQmul p₁ (PQmul p₂ q).
Proof.
intros p₁ p₂ q.
unfold PQmul; simpl.
destruct (Qnum q).
 reflexivity.

 rewrite Pos.mul_assoc; reflexivity.

 rewrite Pos.mul_assoc; reflexivity.
Qed.
*)

(*
Lemma Qmul₁_mul_cancel_l : ∀ k k₁ q₁ k₂ q₂,
  Qmul₁ (k * k₁) q₁ = Qmul₁ (k * k₂) q₂
  ↔ Qmul₁ k₁ q₁ = Qmul₁ k₂ q₂.
Proof.
intros k k₁ q₁ k₂ q₂.
destruct q₁ as (qn₁, qd₁).
destruct q₂ as (qn₂, qd₂).
unfold Qmul₁; simpl.
split; intros H.
 injection H; clear H; intros.
 do 2 rewrite <- Pos.mul_assoc in H.
 apply Pos.mul_cancel_l in H.
 rewrite H; f_equal.
 destruct qn₁.
  destruct qn₂; try discriminate H0; reflexivity.

  destruct qn₂; try discriminate H0.
  injection H0; clear H0; intros.
  do 2 rewrite <- Pos.mul_assoc in H0.
  apply Pos.mul_cancel_l in H0.
  rewrite H0; reflexivity.

  destruct qn₂; try discriminate H0.
  injection H0; clear H0; intros.
  do 2 rewrite <- Pos.mul_assoc in H0.
  apply Pos.mul_cancel_l in H0.
  rewrite H0; reflexivity.

 injection H; clear H; intros.
 do 2 rewrite <- Pos.mul_assoc.
 rewrite H; f_equal.
 destruct qn₁.
  destruct qn₂; try discriminate H0; reflexivity.

  destruct qn₂; try discriminate H0.
  injection H0; clear H0; intros.
  do 2 rewrite <- Pos.mul_assoc.
  rewrite H0; reflexivity.

  destruct qn₂; try discriminate H0.
  injection H0; clear H0; intros.
  do 2 rewrite <- Pos.mul_assoc.
  rewrite H0; reflexivity.
Qed.
*)

(*
Lemma PQmul_1_l : ∀ q, PQmul 1 q = q.
Proof.
intros q.
unfold PQmul.
rewrite Z.mul_1_l.
destruct q; reflexivity.
Qed.
*)

Theorem eq_ps_refl : reflexive _ eq_ps.
Proof.
intros ps.
econstructor 1 with (k₁ := xH); reflexivity.
Qed.

Theorem eq_ps_sym : symmetric _ eq_ps.
Proof.
intros ps₁ ps₂ H.
inversion H; subst.
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

 destruct (stop s) as [st| ]; [ idtac | reflexivity ].
 rewrite Nat.mul_shuffle0, mult_assoc; reflexivity.
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

Lemma stretch_series_eq : ∀ n s₁ s₂,
  n ≠ O
  → stretch_series n s₁ ≃ stretch_series n s₂
    → s₁ ≃ s₂.
Proof.
intros n s₁ s₂ Hn H.
inversion H; subst.
constructor.
 intros i.
 pose proof (H0 (n * i)%nat) as Hi.
 simpl in Hi.
 rewrite mult_comm, Nat.mod_mul in Hi; simpl in Hi; [ idtac | assumption ].
 rewrite Nat.div_mul in Hi; assumption.

 simpl in H1.
 destruct (stop s₁) as [st₁| ].
  destruct (stop s₂) as [st₂| ]; [ idtac | discriminate H1 ].
  injection H1; clear H1; intros.
  f_equal.
  apply Nat.mul_cancel_r in H1; assumption.

  destruct (stop s₂); [ discriminate H1 | reflexivity ].
Qed.

Lemma stretch_series_1 : ∀ s, stretch_series (Pos.to_nat 1) s ≃ s.
Proof.
intros s.
unfold stretch_series; simpl.
destruct s as (t, st); simpl.
constructor; simpl.
 intros i; rewrite divmod_div.
 rewrite Nat.div_1_r; reflexivity.

 destruct st as [| st]; [ idtac | reflexivity ].
 rewrite mult_1_r; reflexivity.
Qed.

Theorem eq_ps_trans : transitive _ eq_ps.
Proof.
intros ps₁ ps₂ ps₃ H₁ H₂.
inversion_clear H₁ as (k₁₁, k₁₂).
inversion_clear H₂ as (k₂₁, k₂₂).
apply Z.mul_cancel_r with (p := Zpos k₂₁) in H0; [ idtac | apply Zpos_ne_0 ].
apply Z.mul_cancel_r with (p := Zpos k₁₂) in H3; [ idtac | apply Zpos_ne_0 ].
rewrite Z.mul_shuffle0 in H3.
rewrite <- H0 in H3.
do 2 rewrite <- Z.mul_assoc in H3.
apply Pos.mul_cancel_r with (r := k₂₁) in H1.
apply Pos.mul_cancel_r with (r := k₁₂) in H4.
rewrite Pos_mul_shuffle0 in H4.
rewrite <- H1 in H4.
do 2 rewrite <- Pos.mul_assoc in H4.
econstructor; [ idtac | eassumption | eassumption ].
do 2 rewrite Pos2Nat.inj_mul.
symmetry; rewrite mult_comm.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
symmetry; rewrite mult_comm.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite H, <- H2.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite mult_comm; reflexivity.
Qed.

Add Parametric Relation : (puiseux_series α) eq_ps
 reflexivity proved by eq_ps_refl
 symmetry proved by eq_ps_sym
 transitivity proved by eq_ps_trans
 as eq_ps_rel.

Definition valuation (ps : puiseux_series α) :=
  match series_head (fld_eq fld (zero fld)) 0 (ps_terms ps) with
  | Some (n, c) => Some (ps_valnum ps + Z.of_nat n # ps_comden ps)
  | None => None
  end.

Definition valuation_coeff (ps : puiseux_series α) :=
  match series_head (fld_eq fld (zero fld)) 0 (ps_terms ps) with
  | Some (_, c) => c
  | None => zero fld
  end.

Definition adjust k ps :=
  {| ps_terms := stretch_series (Pos.to_nat k) (ps_terms ps);
     ps_valnum := ps_valnum ps * 'k;
     ps_comden := ps_comden ps * k |}.

(*
Lemma Qmul₁_mul_distr_r : ∀ p q k, Qmul₁ (k * p) q = Qmul₁ p (Qmul₁ k q).
Proof.
intros p q k.
unfold Qmul₁; simpl.
f_equal; [ idtac | rewrite Pos_mul_shuffle0, Pos.mul_comm; reflexivity ].
destruct (Qnum q); [ reflexivity | idtac | idtac ].
 rewrite Pos_mul_shuffle0, Pos.mul_comm; reflexivity.

 rewrite Pos_mul_shuffle0, Pos.mul_comm; reflexivity.
Qed.
*)

Theorem adjust_eq : ∀ k ps, adjust k ps ≈ ps.
Proof.
intros k ps.
unfold adjust.
remember (ps_comden ps) as c.
econstructor 1 with (k₁ := c) (k₂ := (k * c)%positive); simpl.
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite Pos2Nat.inj_mul, Nat.mul_comm; reflexivity.

 rewrite Pos2Z.inj_mul, Z.mul_assoc; reflexivity.

 subst c; rewrite Pos.mul_assoc; reflexivity.
Qed.

(* ps_add *)

Definition series_pad_left n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n)%nat;
     stop :=
       match stop s with
       | Some st => Some (st + n)%nat
       | None => None
       end |}.

(*
Definition lcm_div α (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (ps_comden ps₁) (ps_comden ps₂) in
  Pos.of_nat (Pos.to_nat l / Pos.to_nat (ps_comden ps₁))%nat.
*)
Definition lcm_div α (ps₁ ps₂ : puiseux_series α) :=
  ps_comden ps₂.
(**)

Definition ps_add (ps₁ ps₂ : puiseux_series α) :=
  let ms₁ := adjust (lcm_div ps₁ ps₂) ps₁ in
  let ms₂ := adjust (lcm_div ps₂ ps₁) ps₂ in
  let v₁ := ps_valnum ms₁ in
  let v₂ := ps_valnum ms₂ in
  {| ps_terms :=
       series_add fld
         (series_pad_left (Z.to_nat v₁ - Z.to_nat v₂) (ps_terms ms₁))
         (series_pad_left (Z.to_nat v₂ - Z.to_nat v₁) (ps_terms ms₂));
     ps_valnum :=
       Z.min v₁ v₂;
     ps_comden :=
       ps_comden ms₁ |}.

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
     stop :=
       match stop s₁ with
       | Some st₁ =>
           match stop s₂ with
           | Some st₂ => Some (max st₁ st₂)
           | None => None
           end
       | None => None
       end |}.

Definition ps_mul (ps₁ ps₂ : puiseux_series α) :=
  let ms₁ := adjust (lcm_div ps₁ ps₂) ps₁ in
  let ms₂ := adjust (lcm_div ps₂ ps₁) ps₂ in
  let l := Plcm (ps_comden ps₁) (ps_comden ps₂) in
  {| ps_terms := series_mul_term (ps_terms ms₁) (ps_terms ms₂);
     ps_valnum := ps_valnum ms₁ + ps_valnum ms₂;
     ps_comden := l |}.

(* *)

Lemma Zmatch_minus : ∀ x y (a : α) f g,
  match (x - y)%Z with
  | 0%Z => a
  | Zpos n => f n
  | Zneg n => g n
  end =
  match (y - x)%Z with
  | 0%Z => a
  | Zpos n => g n
  | Zneg n => f n
  end.
Proof.
intros x y a f g.
remember (x - y)%Z as xy.
symmetry in Heqxy.
destruct xy.
 apply Zminus_eq in Heqxy.
 subst x; rewrite Zminus_diag; reflexivity.

 do 3 (apply Z.sub_move_l in Heqxy; symmetry in Heqxy).
 rewrite Z.sub_opp_l in Heqxy.
 rewrite Z.opp_involutive in Heqxy.
 rewrite Heqxy; reflexivity.

 do 3 (apply Z.sub_move_l in Heqxy; symmetry in Heqxy).
 rewrite Z.sub_opp_l in Heqxy.
 rewrite Z.opp_involutive in Heqxy.
 rewrite Heqxy; reflexivity.
Qed.

Lemma Zmatch_split : ∀ x (a₁ a₂ : α) f₁ f₂ g₁ g₂,
  a₁ = a₂
  → (∀ n, f₁ n = f₂ n)
    → (∀ n, g₁ n = g₂ n)
      → match x with
        | 0%Z => a₁
        | Zpos n => f₁ n
        | Zneg n => g₁ n
        end =
        match x with
        | 0%Z => a₂
        | Zpos n => f₂ n
        | Zneg n => g₂ n
        end.
Proof.
intros x a₁ a₂ f₁ f₂ g₁ g₂ Ha Hf Hg.
destruct x; [ assumption | apply Hf | apply Hg ].
Qed.

Add Parametric Morphism : (@mkps α) with 
signature (eq_series fld) ==> eq ==> eq ==> eq_ps as mkps_morph.
Proof.
intros s₁ s₂ Heq v.
inversion_clear Heq; subst.
constructor 1 with (k₁ := xH) (k₂ := xH).
 do 2 rewrite stretch_series_1; simpl.
 constructor; assumption.

 reflexivity.

 reflexivity.
Qed.

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

Add Parametric Morphism : (@terms α) with
signature eq_series fld ==> @eq nat ==> fld_eq fld as terms_morph.
Proof.
intros s₁ s₂ Heq i.
inversion Heq; subst.
apply H.
Qed.

Add Parametric Morphism k : (adjust k) with
signature eq_ps ==> eq_ps as adjust_morph.
Proof.
intros ps₁ ps₂ H.
unfold adjust.
inversion_clear H.
constructor 1 with (k₁ := k₁) (k₂ := k₂); simpl.
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite Nat.mul_comm.
 rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
 symmetry.
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite Nat.mul_comm.
 rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite H0; reflexivity.

 rewrite Z.mul_shuffle0; symmetry.
 rewrite Z.mul_shuffle0; symmetry.
 apply Z.mul_cancel_r; [ apply Zpos_ne_0 | assumption ].

 rewrite Pos_mul_shuffle0; symmetry.
 rewrite Pos_mul_shuffle0; symmetry.
 apply Pos.mul_cancel_r; assumption.
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
 destruct (zerop (i mod k)) as [Hz| Hnz].
  reflexivity.

  rewrite fld_add_neutral; reflexivity.

 destruct (stop s₁) as [st₁| ]; [ idtac | reflexivity ].
 destruct (stop s₂) as [st₂| ]; [ idtac | reflexivity ].
 rewrite Nat.mul_max_distr_r; reflexivity.
Qed.

(*
Add Parametric Morphism : ps_add_pad with 
signature eq_ps ==> eq_ps ==> eq ==> eq_ps as ps_add_pad_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂ d.
inversion_clear Heq₁ as (k₁, k₃, a, b, Hss₁, Hm₁); subst.
inversion_clear Heq₂ as (k₂, k₄, a, b, Hss₂, Hm₂); subst.
unfold ps_add_pad.
unfold ps_add_no_pad.
unfold ps_add_pad_r.
unfold ps_add_pad_l.
destruct d; simpl.
 econstructor 1; simpl; [ idtac | eassumption ].
 rewrite stretch_series_add_distr.
 rewrite stretch_series_add_distr.
 rewrite Hss₁.
bbb.

intros ps₁ ps₂ Heq₁ ps₃ ps₄ Heq₂ d.
inversion Heq₁.
inversion Heq₂.
unfold ps_add_pad.
destruct d; simpl.
 constructor; [ simpl | assumption | assumption ].
 rewrite H, H2; reflexivity.

 unfold ps_add_pad_r; simpl.
 rewrite H, H0, H1, H2; reflexivity.

 unfold ps_add_pad_l; simpl.
 rewrite H, H2, H3, H4; reflexivity.
Qed.
*)

(*
Lemma ps_add_pad_0_morph : ∀ ps₁ ps₂ ps₃ ps₄,
  ps₁ ≈ ps₃
  → ps₂ ≈ ps₄
    → ps_add_pad
        (adjust (lcm_div ps₁ ps₂) ps₁)
        (adjust (lcm_div ps₂ ps₁) ps₂) 0
      ≈ ps_add_pad
          (adjust (lcm_div ps₃ ps₄) ps₃)
          (adjust (lcm_div ps₄ ps₃) ps₄) 0.
Proof.
intros ps₁ ps₂ ps₃ ps₄ Heq₁ Heq₂.
inversion_clear Heq₁ as (k₁, k₃, c, d, Hss₁, Hv₁, Hc₁); subst.
inversion_clear Heq₂ as (k₂, k₄, c, d, Hss₂, Hv₂, Hc₂); subst.
unfold adjust; simpl.
unfold ps_add_no_pad; simpl.
erewrite <- adjust_eq with (k := k₁); unfold adjust; simpl.
rewrite stretch_series_add_distr.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite mult_comm.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite Hss₁.
rewrite series_add_comm.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite mult_comm.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
erewrite <- adjust_eq with (k := k₂); unfold adjust; simpl.
rewrite stretch_series_add_distr.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite <- Pos2Nat.inj_mul.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite Pos2Nat.inj_mul.
rewrite <- mult_assoc, mult_comm.
rewrite <- Pos2Nat.inj_mul.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite Hss₂.
rewrite series_add_comm.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite <- Pos2Nat.inj_mul.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
do 2 rewrite <- Pos2Nat.inj_mul.
unfold lcm_div.
rewrite Pos.mul_comm in Hc₂.
rewrite Hc₁, Hc₂.
rewrite Pos_mul_shuffle0.
do 2 rewrite <- Pos.mul_assoc.
rewrite Pos2Nat.inj_mul, mult_comm.
rewrite series_add_comm.
rewrite Pos2Nat.inj_mul, mult_comm.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite <- stretch_series_add_distr.
rewrite <- Z.mul_assoc, <- Z.mul_shuffle1.
rewrite <- Pos2Z.inj_mul.
rewrite Pos.mul_comm in Hc₂.
rewrite Hv₁, Hc₂.
rewrite <- Pos.mul_assoc, <- Pos_mul_shuffle1.
rewrite Hc₁, Hc₂.
constructor 1 with (k₁ := xH) (k₂ := (k₃ * k₄)%positive); simpl.
 rewrite stretch_series_1, series_add_comm.
 reflexivity.

 do 2 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_1_r, Z.mul_shuffle1; reflexivity.

 rewrite Pos.mul_1_r, Pos_mul_shuffle1; reflexivity.
Qed.
*)

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
   destruct (lt_dec (c * k) (n * k)) as [| Hnok]; [ reflexivity | idtac ].
   exfalso; apply Hnok.
   apply mult_lt_compat_r; [ assumption | idtac ].
   destruct k; [ exfalso; apply Hk; reflexivity | apply lt_0_Sn ].

   apply not_gt in Hge.
   destruct (lt_dec (c * k) (n * k)) as [Hnok| Hok].
    apply gt_not_le in Hnok.
    exfalso; apply Hnok.
    apply mult_le_compat_r; assumption.

    rewrite <- mult_minus_distr_r.
    rewrite Nat.mod_mul; [ simpl | assumption ].
    rewrite Nat.div_mul; [ reflexivity | assumption ].

  destruct (lt_dec i (n * k)) as [| Hge]; [ reflexivity | idtac ].
  apply not_gt in Hge.
  destruct (zerop ((i - n * k) mod k)) as [Hz| ]; [ idtac | reflexivity ].
  apply Nat.mod_divides in Hz; [ idtac | assumption ].
  destruct Hz as (c, Hi).
  apply Nat.add_sub_eq_nz in Hi.
   subst i.
   rewrite mult_comm, <- mult_plus_distr_l in Hnz.
   rewrite mult_comm, Nat.mod_mul in Hnz; [ idtac | assumption ].
   exfalso; revert Hnz; apply lt_irrefl.

   intros H; rewrite H in Hi.
   apply Nat.sub_0_le in Hi.
   eapply le_antisym in Hge; [ idtac | eassumption ].
   subst i.
   rewrite Nat.mod_mul in Hnz; [ idtac | assumption ].
   revert Hnz; apply lt_irrefl.

 simpl.
 destruct (stop s) as [st| ]; [ idtac | reflexivity ].
 rewrite mult_plus_distr_r; reflexivity.
Qed.

(*
Lemma ps_add_pad_pos_morph : ∀ ps₁ ps₂ ps₃ ps₄ p e,
  ps₁ ≈ ps₃
  → ps₂ ≈ ps₄
    → ps_add_pad
        (adjust (lcm_div ps₁ ps₂) ps₁)
        (adjust (lcm_div ps₂ ps₁) ps₂) ('p)
      ≈ ps_add_pad
          (adjust (lcm_div ps₃ ps₄) ps₃)
          (adjust (lcm_div ps₄ ps₃) ps₄) e.
Proof.
intros ps₁ ps₂ ps₃ ps₄ p e Heq₁ Heq₂.
inversion_clear Heq₁ as (k₁, k₃, c, d, Hss₁, Hv₁, Hc₁); subst.
inversion_clear Heq₂ as (k₂, k₄, c, d, Hss₂, Hv₂, Hc₂); subst.
assert (e * ' k₃ * ' k₄ = ' p * ' k₁ * ' k₂)%Z as Hep. Focus 2.
destruct e as [| e| ]; [ discriminate Hep | simpl | discriminate Hep ].
unfold adjust; simpl.
unfold ps_add_pad_r; simpl.
erewrite <- adjust_eq with (k := k₁); unfold adjust; simpl.
rewrite stretch_series_add_distr.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite mult_comm.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite Hss₁.
rewrite series_add_comm.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite mult_comm.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
erewrite <- adjust_eq with (k := k₂); unfold adjust; simpl.
rewrite stretch_series_add_distr.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite <- Pos2Nat.inj_mul.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite stretch_pad_series_distr; try apply pos_to_nat_ne_0.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite Pos2Nat.inj_mul.
do 2 rewrite <- Pos2Nat.inj_mul.
remember (Pos.to_nat (p * (k₂ * k₁))) as pkk.
rewrite Pos2Nat.inj_mul.
rewrite <- mult_assoc, mult_comm.
rewrite <- Pos2Nat.inj_mul.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite Hss₂.
rewrite series_add_comm.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite <- Pos2Nat.inj_mul.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
bbb.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
do 2 rewrite <- Pos2Nat.inj_mul.
unfold lcm_div.
rewrite Pos.mul_comm in Hc₂.
rewrite Hc₁, Hc₂.
rewrite Pos_mul_shuffle0.
do 2 rewrite <- Pos.mul_assoc.
rewrite Pos2Nat.inj_mul, mult_comm.
rewrite series_add_comm.
rewrite Pos2Nat.inj_mul, mult_comm.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite <- stretch_series_add_distr.
rewrite <- Z.mul_assoc, <- Z.mul_shuffle1.
rewrite <- Pos2Z.inj_mul.
rewrite Pos.mul_comm in Hc₂.
rewrite Hv₁, Hc₂.
rewrite <- Pos.mul_assoc, <- Pos_mul_shuffle1.
rewrite Hc₁, Hc₂.
constructor 1 with (k₁ := xH) (k₂ := (k₃ * k₄)%positive); simpl.
 rewrite stretch_series_1, series_add_comm.
 reflexivity.

 do 2 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_1_r, Z.mul_shuffle1; reflexivity.

 rewrite Pos.mul_1_r, Pos_mul_shuffle1; reflexivity.
bbb.
*)

Open Scope Z_scope.

Lemma weird_formula : ∀ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄,
  a₁ * c₁ = a₃ * c₃
  → a₂ * c₂ = a₄ * c₄
    → b₁ * c₁ = b₃ * c₃
      → b₂ * c₂ = b₄ * c₄
        → (a₂ * b₁ - a₁ * b₂) * c₁ * c₂ =
          (a₄ * b₃ - a₃ * b₄) * c₃ * c₄.
Proof.
intros a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ Ha₁ Ha₂ Hb₁ Hb₂.
rewrite Z.mul_sub_distr_r.
rewrite <- Z.mul_assoc, Hb₁.
rewrite Z.mul_shuffle0, Ha₁.
rewrite Z.mul_comm.
rewrite Z.mul_sub_distr_l.
rewrite Z.mul_assoc.
rewrite Z.mul_comm in Ha₂; rewrite Ha₂.
do 2 rewrite <- Z.mul_assoc.
do 3 rewrite Z.mul_assoc.
rewrite Z.mul_shuffle2.
rewrite Z.mul_comm in Hb₂; rewrite Hb₂.
ring.
Qed.

Lemma valnum_comden : ∀ (ps₁ ps₂ ps₃ ps₄ : puiseux_series α) k₁ k₂ k₃ k₄,
  ps_valnum ps₁ * ' k₁ = ps_valnum ps₃ * ' k₃
  → (ps_comden ps₁ * k₁)%positive = (ps_comden ps₃ * k₃)%positive
    → ps_valnum ps₂ * ' k₂ = ps_valnum ps₄ * ' k₄
      → (ps_comden ps₂ * k₂)%positive = (ps_comden ps₄ * k₄)%positive
        → (ps_valnum ps₂ * ' ps_comden ps₁ -
           ps_valnum ps₁ * ' ps_comden ps₂) * 'k₁ * 'k₂
          = (ps_valnum ps₄ * ' ps_comden ps₃ -
             ps_valnum ps₃ * ' ps_comden ps₄) * 'k₃ * 'k₄.
Proof.
intros ps₁ ps₂ ps₃ ps₄ k₁ k₂ k₃ k₄ Hv₁ Hc₁ Hv₂ Hc₂.
apply Z.mul_reg_r with (p := Zpos k₁); [ apply Zpos_ne_0 | idtac ].
apply Z.mul_reg_r with (p := Zpos k₂); [ apply Zpos_ne_0 | idtac ].
erewrite weird_formula.
 2: eassumption.

 2: eassumption.

 2: rewrite <- Pos2Z.inj_mul.
 2: rewrite Hc₁.
 2: rewrite Pos2Z.inj_mul.
 2: reflexivity.

 2: rewrite <- Pos2Z.inj_mul.
 2: rewrite Hc₂.
 2: rewrite Pos2Z.inj_mul.
 2: reflexivity.

 ring.
Qed.

Close Scope Z_scope.

(*
Add Parametric Morphism : ps_add with 
signature eq_ps ==> eq_ps ==> eq_ps as ps_add_morph.
Proof.
intros ps₁ ps₃ Heq₁ ps₂ ps₄ Heq₂.
unfold ps_add; simpl.
remember (lcm_div ps₁ ps₂) as l₁₂.
remember (lcm_div ps₂ ps₁) as l₂₁.
remember (val_num_sub (adjust l₁₂ ps₁) (adjust l₂₁ ps₂)) as d.
subst l₁₂ l₂₁.
remember (lcm_div ps₃ ps₄) as l₃₄.
remember (lcm_div ps₄ ps₃) as l₄₃.
remember (val_num_sub (adjust l₃₄ ps₃) (adjust l₄₃ ps₄)) as e.
subst l₃₄ l₄₃.
unfold val_num_sub, adjust, lcm_div in Heqd.
simpl in Heqd.
unfold val_num_sub, adjust, lcm_div in Heqe.
simpl in Heqe.
remember Heq₁ as Hp₁; clear HeqHp₁.
remember Heq₂ as Hp₂; clear HeqHp₂.
inversion_clear Heq₁ as (k₁, k₃, a, b, Hss₁, Hv₁, Hc₁).
inversion_clear Heq₂ as (k₂, k₄, a, b, Hss₂, Hv₂, Hc₂).
eapply Z.mul_cancel_r with (p := (Zpos k₁ * Zpos k₂)%Z) in Heqd.
 do 2 rewrite Z.mul_assoc in Heqd.
 erewrite valnum_comden in Heqd; try eassumption.
 simpl in Heqd.
 symmetry in Heqd.
 rewrite <- Z.mul_assoc in Heqd.
 rewrite <- Heqe in Heqd.
 destruct d.
  apply Z.eq_mul_0_l in Heqd.
   rewrite Heqd; apply ps_add_pad_0_morph; assumption.

   rewrite <- Pos2Z.inj_mul; apply Zpos_ne_0.
bbb.

intros ps₁ ps₂ Heq₁ ps₃ ps₄ Heq₂.
inversion Heq₁; subst.
inversion Heq₂; subst.
inversion H; subst.
inversion H2; subst.
unfold ps_add; simpl.
rewrite H0, H1, H3, H4.
remember (Plcm (ps_comden ps₂) (ps_comden ps₄)) as l.
unfold lcm_div.
rewrite H1, H4.
rewrite <- Heql.
remember (Pos.to_nat l / Pos.to_nat (ps_comden ps₂))%nat as m.
rewrite Plcm_comm.
rewrite <- Heql.
remember (Pos.to_nat l / Pos.to_nat (ps_comden ps₄))%nat as n.
remember (ps_valnum ps₄ * Z.of_nat n - ps_valnum ps₂ * Z.of_nat m)%Z as j.
unfold ps_add_pad.
destruct j as [| j| j].
 unfold ps_add_no_pad; simpl.
 constructor; simpl; [ idtac | idtac | reflexivity ].
  constructor.
   intros i; simpl.
   destruct (zerop (i mod m)).
    rewrite H5.
    destruct (zerop (i mod n)); [ idtac | reflexivity ].
    rewrite H7; reflexivity.

    destruct (zerop (i mod n)); [ idtac | reflexivity ].
    rewrite H7; reflexivity.

   simpl; rewrite H6, H8; reflexivity.

  rewrite H0; reflexivity.

 unfold ps_add_pad_r; simpl.
 constructor; simpl; [ idtac | idtac | reflexivity ].
  constructor.
   intros i; simpl.
   destruct (i mod m); simpl.
    rewrite H5.
    destruct (lt_dec i (Pos.to_nat j)); [ reflexivity | idtac ].
    destruct (zerop ((i - Pos.to_nat j) mod n)); [ idtac | reflexivity ].
    rewrite H7; reflexivity.

    destruct (lt_dec i (Pos.to_nat j)); [ reflexivity | idtac ].
    destruct (zerop ((i - Pos.to_nat j) mod n)); [ idtac | reflexivity ].
    rewrite H7; reflexivity.

   simpl; rewrite H6, H8; reflexivity.

  rewrite H0; reflexivity.

 unfold ps_add_pad_l; simpl.
 constructor; simpl; [ idtac | idtac | reflexivity ].
  constructor.
   intros i; simpl.
   destruct (lt_dec i (Pos.to_nat j)).
    destruct (zerop (i mod n)); [ idtac | reflexivity ].
    rewrite H7; reflexivity.

    destruct (zerop ((i - Pos.to_nat j) mod m)).
     rewrite H5.
     destruct (zerop (i mod n)); [ idtac | reflexivity ].
     rewrite H7; reflexivity.

     destruct (zerop (i mod n)); [ idtac | reflexivity ].
     rewrite H7; reflexivity.

   simpl; rewrite H6, H8; reflexivity.

  rewrite H3; reflexivity.
Qed.
*)

(* *)

Lemma ps_add_comm : ∀ ps₁ ps₂, ps_add ps₁ ps₂ ≈ ps_add ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_add; simpl.
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 do 2 rewrite stretch_series_1.
 apply series_add_comm.

 do 2 rewrite Z.mul_1_r.
 apply Z.min_comm.

 do 2 rewrite Pos.mul_1_r.
 apply Pos.mul_comm.
Qed.

(*
Lemma same_comden_ps_add_pad : ∀ ps₁ ps₂ d,
  ps_comden ps₁ = ps_comden ps₂
  → ps_comden (ps_add_pad ps₁ ps₂ d) = ps_comden ps₁.
Proof.
intros ps₁ ps₂ d H.
unfold ps_add_pad; simpl.
destruct d; reflexivity.
Qed.
*)

Lemma adjust_1 : ∀ ps, adjust xH ps ≈ ps.
Proof.
intros ps.
unfold adjust; simpl.
rewrite stretch_series_1.
rewrite Z.mul_1_r, Pos.mul_1_r.
destruct ps as (t, v); destruct v; reflexivity.
Qed.

Lemma series_pad_add_distr : ∀ s₁ s₂ n,
  series_pad_left n (series_add fld s₁ s₂)
  ≃ series_add fld (series_pad_left n s₁) (series_pad_left n s₂).
Proof.
intros s₁ s₂ n.
constructor.
 intros i.
 unfold series_add; simpl.
 destruct (lt_dec i n) as [Hlt| Hge]; [ idtac | reflexivity ].
 symmetry; apply fld_add_neutral.

 simpl.
 destruct (stop s₁) as [n₁| ]; [ idtac | reflexivity ].
 destruct (stop s₂) as [n₂| ]; [ idtac | reflexivity ].
 f_equal.
 rewrite Nat.add_max_distr_r; reflexivity.
Qed.

Lemma series_pad_plus : ∀ m n t,
  series_pad_left m (series_pad_left n t) ≃
  series_pad_left (m + n) t.
Proof.
intros m n t.
unfold series_pad_left; simpl.
constructor; simpl.
 intros i.
 destruct (lt_dec i m) as [Hlt| Hge].
  destruct (lt_dec i (m + n)) as [| Hge]; [ reflexivity | idtac ].
  exfalso; apply Hge.
  apply lt_plus_trans; assumption.

  apply not_gt in Hge.
  destruct (lt_dec (i - m) n) as [Hlt| Hge₂].
   destruct (lt_dec i (m + n)) as [| Hge₂]; [ reflexivity | idtac ].
   exfalso; apply Hge₂.
   apply Nat.lt_sub_lt_add_l; assumption.

   apply not_gt in Hge₂.
   destruct (lt_dec i (m + n)) as [Hlt| Hge₃].
    apply plus_le_compat_l with (p := m) in Hge₂.
    rewrite le_plus_minus_r in Hge₂; [ idtac | assumption ].
    apply le_not_lt in Hge₂; contradiction.

    rewrite Nat.sub_add_distr; reflexivity.

 destruct (stop t); [ idtac | reflexivity ].
 rewrite Nat.add_shuffle0, Nat.add_assoc; reflexivity.
Qed.

(*
Lemma ps_add_assoc_same_comden : ∀ ps₁ ps₂ ps₃ l,
  l = Qden (ps_valuation ps₁)
  → l = Qden (ps_valuation ps₂)
    → l = Qden (ps_valuation ps₃)
      → ps_add (ps_add ps₁ ps₂) ps₃ ≈ ps_add ps₁ (ps_add ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃ l H₁ H₂ H₃.
unfold ps_add, lcm_div; simpl.
rewrite <- H₁, <- H₂, <- H₃.
rewrite Plcm_diag.
rewrite Nat.div_same; [ idtac | apply pos_to_nat_ne_0 ].
do 3 rewrite Z.mul_1_r.
do 3 rewrite adjust_1.
remember (Qnum (ps_valuation ps₂) - Qnum (ps_valuation ps₁))%Z as v₂₁.
symmetry in Heqv₂₁.
remember (Qnum (ps_valuation ps₃) - Qnum (ps_valuation ps₂))%Z as v₃₂.
symmetry in Heqv₃₂.
destruct v₂₁ as [| v₂₁| v₂₁]; simpl.
 rewrite <- H₁.
 destruct v₃₂ as [| v₃₂| v₃₂]; simpl.
  rewrite <- H₂.
  rewrite Plcm_diag.
  rewrite Nat.div_same; [ idtac | apply pos_to_nat_ne_0 ].
  do 4 rewrite adjust_1.
  do 3 rewrite Z.mul_1_r.
  apply Zminus_eq in Heqv₃₂; rewrite Heqv₃₂, Heqv₂₁; simpl.
  constructor 1 with (k₁ := xH) (k₂ := xH).
   do 2 rewrite stretch_series_1.
   constructor.
    intros i; simpl.
    rewrite fld_add_assoc; reflexivity.

    simpl.
    destruct (stop (ps_terms ps₁)) as [st₁| ]; [ idtac | reflexivity ].
    destruct (stop (ps_terms ps₂)) as [st₂| ]; [ idtac | reflexivity ].
    destruct (stop (ps_terms ps₃)) as [st₃| ]; [ idtac | reflexivity ].
    rewrite Nat.max_assoc; reflexivity.

   Focus 1.
bbb.

intros ps₁ ps₂ ps₃ l H₁ H₂ H₃.
unfold ps_add; simpl.
rewrite <- H₁, <- H₂, <- H₃.
rewrite Plcm_diag.
unfold lcm_div.
rewrite <- H₁, <- H₂, <- H₃.
rewrite Plcm_diag.
rewrite Nat.div_same.
 simpl.
 unfold adjust; simpl.
 do 3 rewrite Zmult_1_r.
 rewrite same_comden_ps_add_pad; [ idtac | reflexivity ].
 rewrite same_comden_ps_add_pad; [ idtac | reflexivity ].
 simpl.
 rewrite Plcm_diag.
 rewrite Nat.div_same.
  simpl.
  do 4 rewrite Zmult_1_r.
  do 5 rewrite adjust_terms_1.
  remember (ps_valnum ps₂ - ps_valnum ps₁)%Z as v₂₁.
  symmetry in Heqv₂₁.
  destruct v₂₁ as [| v₂₁| v₂₁]; simpl.
   remember (ps_valnum ps₃ - ps_valnum ps₂)%Z as v₃₂.
   symmetry in Heqv₃₂.
   destruct v₃₂ as [| v₃₂| v₃₂]; simpl.
    rewrite Heqv₂₁; simpl.
    apply Zminus_eq in Heqv₃₂; rewrite Heqv₃₂, Heqv₂₁; simpl.
    constructor; [ apply series_add_assoc | reflexivity | reflexivity ].

    rewrite Heqv₂₁; simpl.
    apply Zminus_eq in Heqv₂₁; rewrite <- Heqv₂₁, Heqv₃₂; simpl.
    constructor; [ apply series_add_assoc | reflexivity | reflexivity ].

    apply Zminus_eq in Heqv₂₁; rewrite <- Heqv₂₁, Heqv₃₂; simpl.
    constructor; [ simpl | reflexivity | reflexivity ].
    rewrite series_pad_add_distr.
    apply series_add_assoc.

   remember (ps_valnum ps₃ - ps_valnum ps₂)%Z as v₃₂.
   symmetry in Heqv₃₂.
   destruct v₃₂ as [| v₃₂| v₃₂]; simpl.
    rewrite Heqv₂₁; simpl.
    apply Zminus_eq in Heqv₃₂; rewrite Heqv₃₂, Heqv₂₁; simpl.
    constructor; [ simpl | reflexivity | reflexivity ].
    rewrite series_pad_add_distr.
    apply series_add_assoc.

    rewrite Heqv₂₁; simpl.
    eapply Zplus_eq_compat in Heqv₂₁; [ idtac | eassumption ].
    rewrite Z.add_sub_assoc, Z.sub_simpl_r in Heqv₂₁.
    rewrite Heqv₂₁; simpl.
    constructor; [ simpl | reflexivity | reflexivity ].
    rewrite series_pad_add_distr, series_pad_plus.
    rewrite plus_comm, <- Pos2Nat.inj_add.
    apply series_add_assoc.

    eapply Zplus_eq_compat in Heqv₂₁; [ idtac | eassumption ].
    rewrite Z.add_sub_assoc, Z.sub_simpl_r in Heqv₂₁.
    rewrite Heqv₂₁; simpl.
    remember (Z.pos_sub v₂₁ v₃₂) as v₃₁.
    symmetry in Heqv₃₁.
    pose proof (Z.pos_sub_discr v₂₁ v₃₂) as H.
    rewrite Heqv₃₁ in H.
    destruct v₃₁ as [| v₃₁| v₃₁]; rewrite H; simpl.
     constructor; [ apply series_add_assoc | reflexivity | reflexivity ].

     constructor; [ simpl | reflexivity | reflexivity ].
     rewrite series_pad_add_distr, series_pad_plus.
     rewrite plus_comm, <- Pos2Nat.inj_add.
     apply series_add_assoc.

     constructor; [ simpl | reflexivity | reflexivity ].
     rewrite series_pad_add_distr, series_pad_plus.
     rewrite plus_comm, <- Pos2Nat.inj_add.
     apply series_add_assoc.

   remember (ps_valnum ps₃ - ps_valnum ps₂)%Z as v₃₂.
   symmetry in Heqv₃₂.
   destruct v₃₂ as [| v₃₂| v₃₂]; simpl.
    rewrite Heqv₂₁; simpl.
    constructor; [ apply series_add_assoc | reflexivity | reflexivity ].

    rewrite Heqv₂₁; simpl.
    constructor; [ apply series_add_assoc | reflexivity | reflexivity ].

    eapply Zplus_eq_compat in Heqv₂₁; [ idtac | eassumption ].
    rewrite Z.add_sub_assoc, Z.sub_simpl_r in Heqv₂₁.
    rewrite Heqv₂₁; simpl.
    constructor; [ simpl | reflexivity | reflexivity ].
    rewrite series_pad_add_distr, series_pad_plus.
    rewrite <- Pos2Nat.inj_add.
    apply series_add_assoc.

  apply pos_to_nat_ne_0.

 apply pos_to_nat_ne_0.
Qed.
*)

(*
Lemma adjust_1_r : ∀ l ps,
  adjust l 1 ps =
    {| ps_terms := ps_terms ps;
       ps_valnum := ps_valnum ps;
       ps_comden := l |}.
Proof.
intros l ps.
unfold adjust; simpl.
rewrite Zmult_1_r.
unfold adjust_terms; simpl.
f_equal.
remember (ps_terms ps) as t.
destruct t.
simpl.
f_equal.
 apply functional_extensionality.
 intros i.
 rewrite divmod_div, Nat.div_1_r; reflexivity.

 destruct stop; [ rewrite mult_1_r; reflexivity | reflexivity ].
Qed.
*)

(*
Lemma ps_add_adjust : ∀ ps₁ ps₂ ms₁ ms₂,
  ms₁ = adjust (lcm_div ps₁ ps₂) ps₁
  → ms₂ = adjust (lcm_div ps₂ ps₁) ps₂
    → ps_add ps₁ ps₂ ≈ ps_add ms₁ ms₂.
Proof.
intros ps₁ ps₂ ms₁ ms₂ Hms₁ Hms₂.
unfold ps_add.
subst ms₁ ms₂; simpl.
bbb.
unfold lcm_div; simpl.

bbb.
unfold ps_add.
subst ms₁ ms₂; simpl.
rewrite Plcm_diag.
unfold lcm_div; simpl.
rewrite Plcm_diag.
rewrite Nat.div_same.
 simpl.
 do 2 rewrite Zmult_1_r.
 rewrite <- Hl, Plcm_comm, <- Hl.
 do 2 rewrite adjust_1_r.
 unfold adjust; simpl.
 reflexivity.

 apply pos_to_nat_ne_0.
Qed.
*)

Lemma eq_eq_ps : ∀ ps₁ ps₂, ps₁ = ps₂ → ps₁ ≈ ps₂.
Proof. intros; subst; reflexivity. Qed.

(*
Lemma ps_comden_adjust : ∀ l m ps, ps_comden (adjust l m ps) = l.
Proof. reflexivity. Qed.
*)

(*
Lemma lcm_div_adjust : ∀ l₁ m₁ ps₁ l₂ m₂ ps₂,
  lcm_div (adjust l₁ m₁ ps₁) (adjust l₂ m₂ ps₂) =
  (Pos.to_nat (Plcm l₁ l₂) / Pos.to_nat l₁)%nat.
Proof. reflexivity. Qed.
*)

Lemma Plcm_Zlcm_div : ∀ a b,
  Z.of_nat (Pos.to_nat (Plcm a b) / Pos.to_nat a) =
  (Z.lcm (Zpos a) (Zpos b) / Zpos a)%Z.
Proof.
intros a b.
unfold Plcm; simpl.
unfold Z.to_pos; simpl.
remember (Z.lcm (' a) (' b)) as l.
symmetry in Heql.
destruct l as [| l| l].
 exfalso.
 apply Z.lcm_eq_0 in Heql.
 destruct Heql.
  revert H; apply Zpos_ne_0.

  revert H; apply Zpos_ne_0.

 pose proof (Z.divide_lcm_l (' a) (' b)) as H.
 rewrite Heql in H.
 destruct H as (k, H).
 rewrite H.
 rewrite Z.div_mul.
  destruct k.
   exfalso.
   simpl in H.
   revert H; apply Zpos_ne_0.

   simpl in H.
   injection H; clear H; intros; subst.
   rewrite Pos2Nat.inj_mul.
   rewrite Nat.div_mul.
    apply positive_nat_Z.

    apply pos_to_nat_ne_0.

   simpl in H.
   discriminate H.

  intros HH; discriminate HH.

 exfalso.
 unfold Z.lcm in Heql.
 pose proof (Zlt_neg_0 l) as H.
 rewrite <- Heql in H.
 apply Zlt_not_le in H.
 apply H, Z.abs_nonneg.
Qed.

(*
Lemma ps_add_adjust_adjust : ∀ ps₁ ps₂,
  ps_add
    (adjust (Plcm (ps_comden ps₁) (ps_comden ps₂)) (lcm_div ps₁ ps₂) ps₁)
    (adjust (Plcm (ps_comden ps₁) (ps_comden ps₂)) (lcm_div ps₂ ps₁) ps₂) =
  ps_add ps₁ ps₂.
Proof.
intros ps₁ ps₂.
unfold ps_add; simpl.
rewrite Plcm_diag.
rewrite lcm_div_adjust.
rewrite lcm_div_adjust.
rewrite Plcm_diag.
rewrite Nat.div_same.
 simpl.
 rewrite Zmult_1_r.
 rewrite Zmult_1_r.
 unfold adjust; simpl.
 rewrite adjust_terms_1.
 rewrite adjust_terms_1.
 rewrite Zmult_1_r.
 rewrite Zmult_1_r.
 reflexivity.

 apply pos_to_nat_ne_0.
Qed.

Lemma add_adjust_comden : ∀ c l m₁ m₂ ps₁ ps₂,
  c ≈ ps_add (adjust l m₁ ps₁) (adjust l m₂ ps₂)
  → ps_comden c = l.
Proof.
intros c l m₁ m₂ ps₁ ps₂ Hc.
inversion Hc.
rewrite H1; simpl.
unfold ps_add; simpl.
rewrite Plcm_diag.
rewrite same_comden_ps_add_pad; reflexivity.
Qed.

Lemma adjust_adjust : ∀ ps l m₁ m₂,
  m₁ ≠ 0%nat
  → m₂ ≠ 0%nat
    → adjust l m₁ (adjust l m₂ ps) = adjust l (m₁ * m₂)%nat ps.
Proof.
intros ps l m₁ m₂ Hm₁ Hm₂.
unfold adjust; simpl.
rewrite Nat2Z.inj_mul.
rewrite Z.mul_assoc, Z.mul_shuffle0.
f_equal.
unfold adjust_terms.
f_equal.
 apply functional_extensionality.
 intros m; simpl.
 destruct (zerop (m mod m₁)) as [Hz| Hnz].
  apply Nat.mod_divides in Hz; [ idtac | assumption ].
  destruct Hz as (c, Hz); subst m.
  rewrite mult_comm, Nat.div_mul; [ idtac | assumption ].
  rewrite mult_comm.
  rewrite Nat.mul_mod_distr_l; [ idtac | assumption | assumption ].
  remember (c mod m₂) as cm₂.
  symmetry in Heqcm₂.
  rewrite mult_comm.
  rewrite Nat.div_mul_cancel_l; [ idtac | assumption | assumption ].
  destruct cm₂; [ reflexivity | idtac ].
  rewrite mult_comm; simpl.
  destruct (zerop (m₁ * S cm₂)) as [Hz| ]; [ idtac | reflexivity ].
  apply Nat.eq_mul_0_r in Hz; [ discriminate Hz | assumption ].

  destruct (zerop (m mod (m₁ * m₂))) as [Hz| ]; [ idtac | reflexivity ].
  apply Nat.mod_divides in Hz.
   destruct Hz as (c, Hz); subst m.
   rewrite <- mult_assoc, mult_comm in Hnz.
   rewrite Nat.mod_mul in Hnz; [ idtac | assumption ].
   exfalso; revert Hnz; apply lt_irrefl.

   apply Nat.neq_mul_0; split; assumption.

 simpl.
 destruct (stop (ps_terms ps)); [ idtac | reflexivity ].
 rewrite mult_assoc, Nat.mul_shuffle0; reflexivity.
Qed.

Lemma ps_comden_add : ∀ ps₁ ps₂,
  ps_comden (ps_add ps₁ ps₂) = Plcm (ps_comden ps₁) (ps_comden ps₂).
Proof.
intros ps₁ ps₂.
unfold ps_add; simpl.
remember (Plcm (ps_comden ps₁) (ps_comden ps₂)) as l.
unfold ps_add_pad; simpl.
destruct
 (ps_valnum ps₂ * Z.of_nat (lcm_div ps₂ ps₁) -
  ps_valnum ps₁ * Z.of_nat (lcm_div ps₁ ps₂))%Z; reflexivity.
Qed.

Lemma lcm_div_add : ∀ ps₁ ps₂ ps₃ l,
  lcm_div ps₁
    (ps_add
       (adjust l (lcm_div ps₂ ps₃) ps₂)
       (adjust l (lcm_div ps₃ ps₂) ps₃)) =
   (Pos.to_nat (Plcm (ps_comden ps₁) l) / Pos.to_nat (ps_comden ps₁))%nat.
Proof.
intros ps₁ ps₂ ps₃ l.
unfold lcm_div.
rewrite ps_comden_add; simpl.
rewrite Plcm_diag; reflexivity.
Qed.
*)

Open Scope Z_scope.

Lemma Z_min_mul_distr_r : ∀ n m p, Z.min n m * 'p = Z.min (n * 'p) (m * 'p).
Proof.
intros n m p.
unfold Z.min.
rewrite <- Zmult_cmp_compat_r; [ idtac | apply Pos2Z.is_pos ].
destruct (n ?= m); reflexivity.
Qed.

Close Scope Z_scope.

Lemma series_pad_left_0 : ∀ s, series_pad_left 0 s ≃ s.
Proof.
intros s.
constructor.
 intros i.
 unfold series_pad_left; simpl.
 rewrite Nat.sub_0_r; reflexivity.

 simpl.
 destruct (stop s); [ rewrite Nat.add_0_r | idtac ]; reflexivity.
Qed.

Lemma ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  ps_add (ps_add ps₁ ps₂) ps₃ ≈ ps_add ps₁ (ps_add ps₂ ps₃).
Proof.
intros ps₁ ps₂ ps₃.
unfold ps_add, lcm_div; simpl.
remember (ps_valnum ps₁) as v₁.
remember (ps_valnum ps₂) as v₂.
remember (ps_valnum ps₃) as v₃.
remember (ps_comden ps₃) as c₃.
remember (ps_comden ps₂) as c₂.
remember (ps_comden ps₁) as c₁.
constructor 1 with (k₁ := xH) (k₂ := xH); simpl.
 do 2 rewrite stretch_series_1.
 do 2 rewrite stretch_series_add_distr.
 do 2 rewrite Z_min_mul_distr_r.
 rewrite Pos2Z.inj_mul.
 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_assoc.
 rewrite Z.mul_assoc.
 remember (v₁ * ' c₂ * ' c₃)%Z as vcc eqn:Hvcc.
 remember (v₂ * ' c₁ * ' c₃)%Z as cvc eqn:Hcvc.
 remember (v₃ * ' c₁ * ' c₂)%Z as ccv eqn:Hccv.
 rewrite Z.mul_comm, Z.mul_assoc, Z.mul_shuffle0 in Hcvc.
 rewrite <- Z.mul_comm, Z.mul_assoc in Hcvc.
 rewrite <- Hcvc.
 rewrite Z.mul_shuffle0 in Hccv; rewrite <- Hccv.
 rewrite stretch_pad_series_distr; [ idtac | apply pos_to_nat_ne_0 ].
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite <- Pos2Nat.inj_mul, Pos.mul_comm.
 remember (stretch_series (Pos.to_nat (c₂ * c₃)) (ps_terms ps₁)) as ccps₁.
bbb.

 do 2 rewrite Z.mul_1_r.
 do 2 rewrite Z_min_mul_distr_r.
 rewrite Z.min_assoc.
 do 2 rewrite Pos2Z.inj_mul.
 do 2 rewrite Z.mul_assoc.
 f_equal; [ idtac | apply Z.mul_shuffle0 ].
 f_equal; apply Z.mul_shuffle0.

 rewrite Pos.mul_assoc; reflexivity.
qed.
