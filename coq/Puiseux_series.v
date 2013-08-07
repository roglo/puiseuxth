(* $Id: Puiseux_series.v,v 1.131 2013-08-07 09:48:53 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Misc.
Require Import Series.

Set Implicit Arguments.

Axiom functional_extensionality : ∀ α β (f g : α → β),
  (∀ x, f x = g x) → f = g.

Record puiseux_series α := mkps
  { ps_terms : series α;
    ps_valuation : Q }.

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

Definition Qmul₁ p q := 'p * Qnum q # p * Qden q.

Inductive eq_ps : puiseux_series α → puiseux_series α → Prop :=
  | eq_ps_base : ∀ k₁ k₂ ps₁ ps₂,
      stretch_series (Pos.to_nat k₁) (ps_terms ps₁) ≃
      stretch_series (Pos.to_nat k₂) (ps_terms ps₂)
      → Qmul₁ k₁ (ps_valuation ps₁) = Qmul₁ k₂ (ps_valuation ps₂)
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
    → stretch_series (a * b) s = stretch_series a (stretch_series b s).
Proof.
intros a b s Ha Hb.
unfold stretch_series.
f_equal; simpl.
 apply functional_extensionality.
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
constructor; simpl.
 intros i; rewrite divmod_div.
 rewrite Nat.div_1_r; reflexivity.

 destruct (stop s) as [st| ]; [ idtac | reflexivity ].
 rewrite Pos2Nat.inj_1, mult_1_r; reflexivity.
Qed.

Theorem eq_ps_trans : transitive _ eq_ps.
Proof.
intros ps₁ ps₂ ps₃ H₁ H₂.
inversion_clear H₁ as (k₁₁, k₁₂).
inversion_clear H₂ as (k₂₁, k₂₂).
apply Qmul₁_mul_cancel_l with (k := k₂₁) in H0.
apply Qmul₁_mul_cancel_l with (k := k₁₂) in H2.
rewrite Pos.mul_comm, <- H0 in H2.
econstructor; [ idtac | eassumption ].
do 2 rewrite Pos2Nat.inj_mul.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite H, <- H1.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
rewrite Nat.mul_comm; reflexivity.
Qed.

Add Parametric Relation : (puiseux_series α) eq_ps
 reflexivity proved by eq_ps_refl
 symmetry proved by eq_ps_sym
 transitivity proved by eq_ps_trans
 as eq_ps_rel.

Definition valuation (ps : puiseux_series α) :=
  match series_head (fld_eq fld (zero fld)) 0 (ps_terms ps) with
  | Some (n, c) =>
      Some (Qnum (ps_valuation ps) + Z.of_nat n # Qden (ps_valuation ps))
  | None =>
      None
  end.

Definition valuation_coeff (ps : puiseux_series α) :=
  match series_head (fld_eq fld (zero fld)) 0 (ps_terms ps) with
  | Some (_, c) => c
  | None => zero fld
  end.

Definition normalise k ps :=
  let l := (k * Qden (ps_valuation ps))%positive in
  {| ps_terms := stretch_series (Pos.to_nat k) (ps_terms ps);
     ps_valuation := Qnum (ps_valuation ps) * 'k # l |}.

Theorem normalise_eq : ∀ k ps, normalise k ps ≈ ps.
Proof.
intros k ps.
unfold normalise.
remember (ps_valuation ps) as v.
econstructor 1 with (k₁ := Qden v) (k₂ := (k * Qden v)%positive); simpl.
 rewrite <- stretch_stretch_series; try apply pos_to_nat_ne_0.
 rewrite Pos2Nat.inj_mul, Nat.mul_comm; reflexivity.

 rewrite <- Heqv.
 unfold Qmul₁; simpl.
 rewrite Pos.mul_comm; f_equal.
 remember (Qnum v) as vn.
 destruct vn; [ reflexivity | simpl | simpl ].
  rewrite Pos.mul_comm.
  symmetry.
  rewrite Pos.mul_comm, Pos.mul_assoc; reflexivity.

  rewrite Pos.mul_comm; symmetry.
  rewrite Pos.mul_comm, Pos.mul_assoc; reflexivity.
Qed.

(* ps_add *)

Definition series_pad_left n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n)%nat;
     stop :=
       match stop s with
       | Some st => Some (st + n)%nat
       | None => None
       end |}.

Definition lcm_div α (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (Qden (ps_valuation ps₁)) (Qden (ps_valuation ps₂)) in
  Pos.of_nat (Pos.to_nat l / Pos.to_nat (Qden (ps_valuation ps₁)))%nat.

Definition valnum_diff_0 ps₁ ps₂ :=
  {| ps_terms := series_add fld (ps_terms ps₁) (ps_terms ps₂);
     ps_valuation := ps_valuation ps₁ |}.

Definition valnum_diff_pos n ps₁ ps₂ :=
  {| ps_terms :=
       series_add fld (ps_terms ps₁)
         (series_pad_left (Pos.to_nat n) (ps_terms ps₂));
     ps_valuation := ps_valuation ps₁ |}.

Definition valnum_diff_neg n ps₁ ps₂ :=
  {| ps_terms :=
       series_add fld (series_pad_left (Pos.to_nat n) (ps_terms ps₁))
         (ps_terms ps₂);
     ps_valuation := ps_valuation ps₂ |}.

Definition valnum_diff ms₁ ms₂ d :=
  match d with
  | Z0 => valnum_diff_0 ms₁ ms₂
  | Zpos n => valnum_diff_pos n ms₁ ms₂
  | Zneg n => valnum_diff_neg n ms₁ ms₂
  end.

Definition ps_add (ps₁ ps₂ : puiseux_series α) :=
  let ms₁ := normalise (lcm_div ps₁ ps₂) ps₁ in
  let ms₂ := normalise (lcm_div ps₂ ps₁) ps₂ in
  valnum_diff ms₁ ms₂
    (Z.sub (Qnum (ps_valuation ms₂)) (Qnum (ps_valuation ms₁))).

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
  let ms₁ := normalise (lcm_div ps₁ ps₂) ps₁ in
  let ms₂ := normalise (lcm_div ps₂ ps₁) ps₂ in
  let l := Plcm (Qden (ps_valuation ps₁)) (Qden (ps_valuation ps₂)) in
  {| ps_terms := series_mul_term (ps_terms ms₁) (ps_terms ms₂);
     ps_valuation := Qnum (ps_valuation ms₁) + Qnum (ps_valuation ms₂) # l |}.

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
signature (eq_series fld) ==> eq ==> eq_ps as mkps_morph.
Proof.
intros s₁ s₂ Heq v.
inversion_clear Heq; subst.
constructor 1 with (k₁ := xH) (k₂ := xH).
 do 2 rewrite stretch_series_1; simpl.
 constructor; assumption.

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

Add Parametric Morphism k : (normalise k) with
signature eq_ps ==> eq_ps as normalise_morph.
Proof.
intros ps₁ ps₂ H.
unfold normalise.
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

 unfold Qmul₁ in H1.
 unfold Qmul₁.
 remember Z.mul as f; simpl; subst f.
 rewrite Z.mul_assoc, Z.mul_comm.
 rewrite Pos.mul_assoc, Pos_mul_shuffle0, Pos.mul_comm.
 symmetry.
 rewrite Z.mul_assoc, Z.mul_comm.
 rewrite Pos.mul_assoc, Pos_mul_shuffle0, Pos.mul_comm.
 remember Z.mul as f.
 injection H1; clear H1; intros; subst f.
 rewrite H, H1; reflexivity.
Qed.

(*
Add Parametric Morphism : valnum_diff with 
signature eq_ps ==> eq_ps ==> @eq Z ==> eq_ps as valnum_diff_morph.
Proof.
intros ps₁ ps₂ Heq₁ ps₃ ps₄ Heq₂ d.
inversion Heq₁.
inversion Heq₂.
unfold valnum_diff.
destruct d; simpl.
 constructor; [ simpl | assumption | assumption ].
 rewrite H, H2; reflexivity.

 unfold valnum_diff_pos; simpl.
 rewrite H, H0, H1, H2; reflexivity.

 unfold valnum_diff_neg; simpl.
 rewrite H, H2, H3, H4; reflexivity.
Qed.
*)

(*
Add Parametric Morphism : ps_add with 
signature eq_ps ==> eq_ps ==> eq_ps as ps_add_morph.
Proof.
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
unfold valnum_diff.
destruct j as [| j| j].
 unfold valnum_diff_0; simpl.
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

 unfold valnum_diff_pos; simpl.
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

 unfold valnum_diff_neg; simpl.
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

(*
Lemma zzz : ∀ p₁ p₂,
  Pos.to_nat (Plcm p₁ p₂) = Nat.lcm (Pos.to_nat p₁) (Pos.to_nat p₂).
Proof.
intros p₁ p₂.
unfold Plcm; simpl.
unfold Z.lcm, Nat.lcm.
rewrite Z.lcm_equiv1.
 simpl.
bbb.
*)

Lemma ps_add_comm : ∀ ps₁ ps₂, ps_add ps₁ ps₂ ≈ ps_add ps₂ ps₁.
Proof.
intros ps₁ ps₂.
unfold ps_add, valnum_diff; simpl.
remember
 (Qnum (ps_valuation ps₂) * ' lcm_div ps₂ ps₁ -
  Qnum (ps_valuation ps₁) * ' lcm_div ps₁ ps₂)%Z as d.
symmetry in Heqd.
remember
 (Qnum (ps_valuation ps₁) * ' lcm_div ps₁ ps₂ -
  Qnum (ps_valuation ps₂) * ' lcm_div ps₂ ps₁)%Z as e.
rewrite <- Z.opp_involutive, Z.opp_sub_distr in Heqe.
rewrite Z.add_opp_l in Heqe.
rewrite Heqd in Heqe; subst e.
destruct d.
 Focus 1.
 simpl.
 constructor 1 with (k₁ := xH) (k₂ := xH).
  simpl.
  rewrite series_add_comm.
  reflexivity.

  f_equal.
  unfold valnum_diff_0; simpl.
  apply Zminus_eq in Heqd; rewrite Heqd.
  f_equal.
  unfold lcm_div; simpl.
  remember (Qden (ps_valuation ps₁)) as q₁.
  remember (Qden (ps_valuation ps₂)) as q₂.
bbb.

constructor.
 destruct d; simpl; rewrite series_add_comm; reflexivity.

 destruct d; try reflexivity.
 apply Zminus_eq; assumption.

 destruct d; apply Plcm_comm.
Qed.

Lemma Plcm_diag : ∀ a, Plcm a a = a.
Proof.
intros a.
unfold Plcm.
rewrite Z.lcm_diag.
reflexivity.
Qed.

Lemma same_comden_valnum_diff : ∀ ps₁ ps₂ d,
  ps_comden ps₁ = ps_comden ps₂
  → ps_comden (valnum_diff ps₁ ps₂ d) = ps_comden ps₁.
Proof.
intros ps₁ ps₂ d H.
unfold valnum_diff; simpl.
destruct d; [ reflexivity | reflexivity | symmetry; assumption ].
Qed.

Lemma normalise_terms_1 : ∀ t, normalise_terms 1 t = t.
Proof.
intros t.
unfold normalise_terms.
destruct t.
f_equal.
 apply functional_extensionality.
 intros i.
 rewrite Nat.div_1_r.
 reflexivity.

 simpl.
 destruct stop.
  rewrite mult_1_r; reflexivity.

  reflexivity.
Qed.

Lemma series_pad_add_distr : ∀ s₁ s₂ n,
  eq_series fld
    (series_pad_left n (series_add fld s₁ s₂))
    (series_add fld (series_pad_left n s₁) (series_pad_left n s₂)).
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
 rewrite Nat.sub_max_distr_r; reflexivity.
Qed.

Lemma series_pad_plus : ∀ m n t,
  series_pad_left m (series_pad_left n t) =
  series_pad_left (m + n) t.
Proof.
intros m n t.
unfold series_pad_left; simpl.
f_equal.
 apply functional_extensionality.
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
 rewrite plus_comm, Nat.sub_add_distr; reflexivity.
Qed.

Lemma ps_add_assoc_same_comden : ∀ ps₁ ps₂ ps₃ l,
  l = ps_comden ps₁
  → l = ps_comden ps₂
    → l = ps_comden ps₃
      → eq_ps
          (ps_add (ps_add ps₁ ps₂) ps₃)
          (ps_add ps₁ (ps_add ps₂ ps₃)).
Proof.
intros ps₁ ps₂ ps₃ l H₁ H₂ H₃.
unfold ps_add; simpl.
rewrite <- H₁, <- H₂, <- H₃.
rewrite Plcm_diag.
unfold lcm_div.
rewrite <- H₁, <- H₂, <- H₃.
rewrite Plcm_diag.
rewrite Nat.div_same.
 simpl.
 unfold normalise; simpl.
 do 3 rewrite Zmult_1_r.
 rewrite same_comden_valnum_diff; [ idtac | reflexivity ].
 rewrite same_comden_valnum_diff; [ idtac | reflexivity ].
 simpl.
 rewrite Plcm_diag.
 rewrite Nat.div_same.
  simpl.
  do 4 rewrite Zmult_1_r.
  do 5 rewrite normalise_terms_1.
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

Lemma normalise_1_r : ∀ l ps,
  normalise l 1 ps =
    {| ps_terms := ps_terms ps;
       ps_valnum := ps_valnum ps;
       ps_comden := l |}.
Proof.
intros l ps.
unfold normalise; simpl.
rewrite Zmult_1_r.
unfold normalise_terms; simpl.
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

Lemma ps_add_normalise : ∀ ps₁ ps₂ ms₁ ms₂ l,
  l = Plcm (ps_comden ps₁) (ps_comden ps₂)
  → eq ms₁ (normalise l (lcm_div ps₁ ps₂) ps₁)
    → eq ms₂ (normalise l (lcm_div ps₂ ps₁) ps₂)
      → eq_ps (ps_add ps₁ ps₂) (ps_add ms₁ ms₂).
Proof.
intros ps₁ ps₂ ms₁ ms₂ l Hl Hms₁ Hms₂.
unfold ps_add.
subst ms₁ ms₂; simpl.
rewrite <- Hl.
rewrite Plcm_diag.
unfold lcm_div; simpl.
rewrite Plcm_diag.
rewrite Nat.div_same.
 simpl.
 do 2 rewrite Zmult_1_r.
 rewrite <- Hl, Plcm_comm, <- Hl.
 do 2 rewrite normalise_1_r.
 unfold normalise; simpl.
 reflexivity.

 apply pos_to_nat_ne_0.
Qed.

Lemma eq_eq_ps : ∀ ps₁ ps₂, ps₁ = ps₂ → ps₁ ≈ ps₂.
Proof. intros; subst; reflexivity. Qed.

Lemma ps_comden_normalise : ∀ l m ps, ps_comden (normalise l m ps) = l.
Proof. reflexivity. Qed.

Lemma lcm_div_normalise : ∀ l₁ m₁ ps₁ l₂ m₂ ps₂,
  lcm_div (normalise l₁ m₁ ps₁) (normalise l₂ m₂ ps₂) =
  (Pos.to_nat (Plcm l₁ l₂) / Pos.to_nat l₁)%nat.
Proof. reflexivity. Qed.

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

Lemma ps_add_normalise_normalise : ∀ ps₁ ps₂,
  ps_add
    (normalise (Plcm (ps_comden ps₁) (ps_comden ps₂)) (lcm_div ps₁ ps₂) ps₁)
    (normalise (Plcm (ps_comden ps₁) (ps_comden ps₂)) (lcm_div ps₂ ps₁) ps₂) =
  ps_add ps₁ ps₂.
Proof.
intros ps₁ ps₂.
unfold ps_add; simpl.
rewrite Plcm_diag.
rewrite lcm_div_normalise.
rewrite lcm_div_normalise.
rewrite Plcm_diag.
rewrite Nat.div_same.
 simpl.
 rewrite Zmult_1_r.
 rewrite Zmult_1_r.
 unfold normalise; simpl.
 rewrite normalise_terms_1.
 rewrite normalise_terms_1.
 rewrite Zmult_1_r.
 rewrite Zmult_1_r.
 reflexivity.

 apply pos_to_nat_ne_0.
Qed.

Lemma add_normalise_comden : ∀ c l m₁ m₂ ps₁ ps₂,
  c ≈ ps_add (normalise l m₁ ps₁) (normalise l m₂ ps₂)
  → ps_comden c = l.
Proof.
intros c l m₁ m₂ ps₁ ps₂ Hc.
inversion Hc.
rewrite H1; simpl.
unfold ps_add; simpl.
rewrite Plcm_diag.
rewrite same_comden_valnum_diff; reflexivity.
Qed.

Lemma normalise_normalise : ∀ ps l m₁ m₂,
  m₁ ≠ 0%nat
  → m₂ ≠ 0%nat
    → normalise l m₁ (normalise l m₂ ps) = normalise l (m₁ * m₂)%nat ps.
Proof.
intros ps l m₁ m₂ Hm₁ Hm₂.
unfold normalise; simpl.
rewrite Nat2Z.inj_mul.
rewrite Z.mul_assoc, Z.mul_shuffle0.
f_equal.
unfold normalise_terms.
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
unfold valnum_diff; simpl.
destruct
 (ps_valnum ps₂ * Z.of_nat (lcm_div ps₂ ps₁) -
  ps_valnum ps₁ * Z.of_nat (lcm_div ps₁ ps₂))%Z; reflexivity.
Qed.

Lemma lcm_div_add : ∀ ps₁ ps₂ ps₃ l,
  lcm_div ps₁
    (ps_add
       (normalise l (lcm_div ps₂ ps₃) ps₂)
       (normalise l (lcm_div ps₃ ps₂) ps₃)) =
   (Pos.to_nat (Plcm (ps_comden ps₁) l) / Pos.to_nat (ps_comden ps₁))%nat.
Proof.
intros ps₁ ps₂ ps₃ l.
unfold lcm_div.
rewrite ps_comden_add; simpl.
rewrite Plcm_diag; reflexivity.
Qed.

Lemma ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  eq_ps
    (ps_add (ps_add ps₁ ps₂) ps₃)
    (ps_add ps₁ (ps_add ps₂ ps₃)).
Proof.
intros ps₁ ps₂ ps₃.
pose proof (ps_comden_add ps₁ ps₂) as Hca.
pose proof (ps_comden_add ps₂ ps₃) as Hcc.
remember (ps_add ps₁ ps₂) as a.
remember (ps_add a ps₃) as b.
remember (ps_add ps₂ ps₃) as c.
remember (ps_add ps₁ c) as d.
remember Heqb as H; clear HeqH.
apply eq_eq_ps in H.
rewrite ps_add_normalise in H; try reflexivity.
rewrite H; clear H.
remember Heqd as H; clear HeqH.
apply eq_eq_ps in H.
rewrite ps_add_normalise in H; try reflexivity.
rewrite H; clear H.
remember Heqa as H; clear HeqH.
apply eq_eq_ps in H.
rewrite ps_add_normalise in H; try reflexivity.
rewrite H in |- * at 3; clear H.
remember Heqc as H; clear HeqH.
apply eq_eq_ps in H.
rewrite ps_add_normalise in H; try reflexivity.
rewrite H in |- * at 5; clear H.
rewrite Heqa, Heqc.
do 2 rewrite ps_comden_add.
remember (Plcm (Plcm (ps_comden ps₁) (ps_comden ps₂)) (ps_comden ps₃)) as l.
rewrite <- Plcm_assoc, <- Heql.
remember (lcm_div (ps_add ps₁ ps₂) ps₃) as v.
unfold lcm_div in Heqv.
rewrite ps_comden_add in Heqv.
rewrite <- Heql in Heqv.
subst v.
remember (lcm_div (ps_add ps₂ ps₃) ps₁) as v.
unfold lcm_div in Heqv.
rewrite ps_comden_add in Heqv.
subst v.
remember (lcm_div ps₁ (ps_add ps₂ ps₃)) as v.
unfold lcm_div in Heqv.
rewrite ps_comden_add in Heqv.
subst v.
rewrite <- Plcm_assoc.
rewrite <- Heql.
remember (Plcm (Plcm (ps_comden ps₂) (ps_comden ps₃)) (ps_comden ps₁)) as v.
rewrite Plcm_comm, <- Plcm_assoc in Heqv.
rewrite <- Heql in Heqv; subst v.
unfold lcm_div; simpl.
rewrite ps_comden_add.
remember (Plcm (ps_comden ps₃) (Plcm (ps_comden ps₁) (ps_comden ps₂))) as v.
rewrite Plcm_comm, <- Heql in Heqv; subst v.
bbb.
