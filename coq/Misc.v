(* $Id: Misc.v,v 1.60 2013-09-04 14:16:00 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).
Notation "x ++ y" := (List.app x y) (right associativity, at level 60).
Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level).
Notation "x < y <= z" := (x < y ∧ y <= z) (at level 70, y at next level).

Set Implicit Arguments.

Definition Qnat i := Z.of_nat i # 1.

Lemma minus_Sn_n : ∀ n, (S n - n = 1)%nat.
Proof.
intros n.
rewrite <- minus_Sn_m; [ rewrite minus_diag; reflexivity | apply le_n ].
Qed.

Lemma le_neq_lt : ∀ x y : nat, x ≤ y → x ≠ y → (x < y)%nat.
Proof.
intros x y Hxy Hnxy.
apply le_lt_eq_dec in Hxy.
destruct Hxy; [ assumption | idtac ].
exfalso; subst x; apply Hnxy; reflexivity.
Qed.

Lemma Qle_neq_lt : ∀ x y, x <= y → ¬ x == y → x < y.
Proof.
intros x y Hxy Hnxy.
apply Qnot_le_lt.
intros H; apply Hnxy.
apply Qle_antisym; assumption.
Qed.

Lemma rev_app_not_nil {α} : ∀ (x : α) l₁ l₂, List.rev l₁ ++ [x … l₂] ≠ [ ].
Proof.
intros x l₁ l₂.
revert x l₂.
induction l₁ as [| y]; intros x l₂.
 intros H; discriminate H.

 simpl; rewrite <- List.app_assoc; simpl.
 apply IHl₁.
Qed.

Lemma Qmutual_shift_div : ∀ x y z t,
  0 < y
  → 0 < t
    → x / y < z / t
      → x * t < z * y.
Proof.
intros x y z t Hb Hd H.
apply Qmult_lt_compat_r with (z := y) in H; [ idtac | assumption ].
rewrite Qmult_comm in H.
rewrite Qmult_div_r in H.
 apply Qmult_lt_compat_r with (z := t) in H; [ idtac | assumption ].
 rewrite <- Qmult_assoc in H.
 remember (x * t) as u.
 rewrite Qmult_comm in H.
 rewrite <- Qmult_assoc in H.
 rewrite Qmult_div_r in H.
  rewrite Qmult_comm; assumption.

  intros HH; rewrite HH in Hd; apply Qlt_irrefl in Hd; contradiction.

 intros HH; rewrite HH in Hb; apply Qlt_irrefl in Hb; contradiction.
Qed.

Lemma Qdiv_lt_compat_r : ∀ x y z, 0 < z → x < y → x / z < y / z.
Proof.
intros x y z Hc H.
apply Qmult_lt_compat_r; [ idtac | assumption ].
apply Qinv_lt_0_compat; assumption.
Qed.

Lemma Qdiv_lt_reg_r : ∀ x y z, 0 < z → x / z < y / z → x < y.
Proof.
intros x y z Hc H.
apply Qmutual_shift_div in H; [ idtac | assumption | assumption ].
apply Qmult_lt_r in H; assumption.
Qed.

Lemma Qdiv_minus_distr_r : ∀ x y z, (x - y) / z == x / z - y / z.
Proof.
intros x y z.
destruct (Qeq_dec z 0) as [Heq| Hne].
 rewrite Heq.
 unfold Qdiv, Qinv; simpl.
 do 3 rewrite Qmult_0_r.
 reflexivity.

 field; assumption.
Qed.

Lemma Qdiv_plus_distr_r : ∀ x y z, (x + y) / z == x / z + y / z.
Proof.
intros x y z.
destruct (Qeq_dec z 0) as [Heq| Hne].
 rewrite Heq.
 unfold Qdiv, Qinv; simpl.
 do 3 rewrite Qmult_0_r.
 reflexivity.

 field; assumption.
Qed.

Lemma Qeq_opp_l : ∀ x y, - x == - y → x == y.
Proof.
intros x y H.
rewrite <- Qopp_opp, H.
apply Qopp_opp.
Qed.

Lemma Qeq_opp_r : ∀ x y, x == y → - x == - y.
Proof.
intros x y H; rewrite H; reflexivity.
Qed.

Lemma Qgt_0_not_0 : ∀ x, 0 < x → ¬x == 0.
Proof.
intros x Ha.
intros H.
rewrite H in Ha.
apply Qlt_irrefl in Ha; assumption.
Qed.

Lemma Qlt_minus : ∀ x y, x < y → 0 < y - x.
Proof.
intros x y H.
unfold Qlt in H |-*; simpl.
rewrite Z.mul_1_r, <- Zopp_mult_distr_l.
apply Zlt_left_lt.
assumption.
Qed.

Lemma Qminus_eq : ∀ x y, x - y == 0 → x == y.
Proof.
intros x y H.
apply Qplus_inj_r with (z := - y).
rewrite Qplus_opp_r.
assumption.
Qed.

Lemma Qmult_div_assoc : ∀ x y z, x * (y / z) == (x * y) / z.
Proof. intros x y z; unfold Qdiv; apply Qmult_assoc. Qed.

Lemma Qmult_opp_l : ∀ x y, (- x) * y == - (x * y).
Proof.
intros x y.
unfold Qeq, Qmult, Qopp; simpl.
rewrite Z.mul_opp_l.
reflexivity.
Qed.

Lemma Qmult_opp_r : ∀ x y, x * - y == - (x * y).
Proof.
intros x y.
unfold Qeq, Qmult, Qopp; simpl.
rewrite Z.mul_opp_r.
reflexivity.
Qed.

Lemma Qmult_minus_distr_l : ∀ x y z, (x - y) * z == x * z - y * z.
Proof.
intros x y z.
unfold Qminus.
rewrite Qmult_plus_distr_l.
rewrite Qmult_opp_l; reflexivity.
Qed.

Lemma Qmult_minus_distr_r : ∀ x y z, x * (y - z) == x * y - x * z.
Proof.
intros x y z.
unfold Qminus.
rewrite Qmult_plus_distr_r.
rewrite Qmult_opp_r; reflexivity.
Qed.

Lemma QZ_plus : ∀ x y, x + y # 1 == (x # 1) + (y # 1).
Proof.
intros.
unfold Qplus; simpl.
do 2 rewrite Z.mul_1_r.
reflexivity.
Qed.

Lemma QZ_minus : ∀ x y, x - y # 1 == (x # 1) - (y # 1).
Proof.
intros.
unfold Qminus, Qplus, Zminus; simpl.
do 2 rewrite Z.mul_1_r.
reflexivity.
Qed.

Lemma Qnat_lt : ∀ i j, (i < j)%nat → Qnat i < Qnat j.
Proof.
intros i j H.
unfold Qnat, Qlt; simpl.
do 2 rewrite Zmult_1_r.
apply inj_lt; assumption.
Qed.

Lemma Qlt_not_0 : ∀ x y, x < y → ¬ y - x == 0.
Proof.
intros i j H HH.
apply Qminus_eq in HH.
rewrite HH in H; apply Qlt_irrefl in H; contradiction.
Qed.

Lemma Qopp_lt_compat: ∀ p q : Q, p < q → - q < - p.
Proof.
intros (x₁, x₂) (y₁, y₂); unfold Qlt; simpl; intros H.
apply Z.opp_lt_mono.
do 2 rewrite Z.mul_opp_l.
do 2 rewrite Z.opp_involutive.
assumption.
Qed.

Lemma Qopp_minus : ∀ x y, - (x - y) == y - x.
Proof. intros; field. Qed.

Lemma Qplus_div : ∀ x y z, ¬(z == 0) → x + y / z == (x * z + y) / z.
Proof.
intros x y z Hc.
rewrite Qdiv_plus_distr_r.
rewrite Qdiv_mult_l; [ reflexivity | assumption ].
Qed.

Lemma Qminus_minus_assoc : ∀ x y z, x - (y - z) == (x - y) + z.
Proof. intros x y z; ring. Qed.

Lemma Qminus_plus_assoc : ∀ x y z, x - (y + z) == (x - y) - z.
Proof. intros x y z; ring. Qed.

Lemma Qplus_minus_assoc : ∀ x y z, x + (y - z) == (x + y) - z.
Proof. intros x y z; ring. Qed.

Lemma Zposnat2Znat : ∀ i, (0 < i)%nat → Zpos (Pos.of_nat i) = Z.of_nat i.
Proof.
intros i Hi.
destruct i; [ apply lt_irrefl in Hi; contradiction | clear Hi ].
simpl; f_equal.
induction i; [ reflexivity | simpl ].
rewrite IHi; reflexivity.
Qed.

(* *)

Lemma Qplus_plus_swap : ∀ x y z, x + y + z == x + z + y.
Proof. intros; ring. Qed.

Lemma Qplus_minus_swap : ∀ x y z, x + y - z == x - z + y.
Proof. intros; ring. Qed.

Lemma Qminus_minus_swap : ∀ x y z, x - y - z == x - z - y.
Proof. intros; ring. Qed.

Lemma Qplus_lt_compat_r : ∀ x y z, x < y → x + z < y + z.
Proof.
intros (x₁, x₂) (y₁, y₂) (z₁, z₂) H.
unfold Qlt in H; simpl in H.
unfold Qlt, Qplus; simpl.
do 2 rewrite Pos2Z.inj_mul.
do 2 rewrite Z.mul_add_distr_r.
do 4 rewrite Z.mul_assoc.
remember (z₁ * ' y₂ * ' x₂ * ' z₂)%Z as t.
remember (z₁ * ' y₂ * ' x₂)%Z as u.
rewrite Z.mul_shuffle0 in Hequ.
subst u.
rewrite <- Heqt.
apply Zplus_lt_compat_r.
clear t Heqt.
rewrite <- Zmult_assoc.
rewrite Z.mul_shuffle1.
remember (y₁ * ' z₂ * ' x₂ * ' z₂)%Z as t.
rewrite <- Zmult_assoc in Heqt.
rewrite Z.mul_shuffle1 in Heqt; subst t.
apply Zmult_lt_compat_r; [ idtac | assumption ].
rewrite <- Pos2Z.inj_mul.
apply Pos2Z.is_pos.
Qed.

Lemma Qminus_lt_lt_plus_r : ∀ x y z, x - y < z → x < z + y.
Proof.
intros x y z H.
apply Qplus_lt_compat_r with (z := y) in H.
rewrite <- Qplus_minus_swap, <- Qplus_minus_assoc in H.
unfold Qminus in H.
rewrite Qplus_opp_r, Qplus_0_r in H.
assumption.
Qed.

Lemma Qlt_minus_plus_lt_r : ∀ x y z, x < y - z → x + z < y.
Proof.
intros x y z H.
apply Qplus_lt_compat_r with (z := z) in H.
rewrite <- Qplus_minus_swap in H.
rewrite <- Qplus_minus_assoc in H.
unfold Qminus in H.
rewrite Qplus_opp_r, Qplus_0_r in H.
assumption.
Qed.

(* to be inserted *)

Lemma Qmult_div_swap : ∀ x y z, x / y * z == x * z / y.
Proof.
intros.
rewrite Qmult_comm, Qmult_div_assoc, Qmult_comm.
reflexivity.
Qed.

Lemma Qeq_shift_mult_l : ∀ x y z, ¬z == 0 → x / z == y → x == y * z.
Proof.
intros x y z Hc H.
rewrite <- H.
rewrite Qmult_div_swap.
rewrite Qdiv_mult_l; [ reflexivity | assumption ].
Qed.

Lemma Qeq_shift_div_l : ∀ x y z, ¬z == 0 → x == y * z → x / z == y.
Proof.
intros x y z Hz H.
rewrite H.
rewrite Qdiv_mult_l; [ reflexivity | assumption ].
Qed.

Lemma Qminus_diag : ∀ x, x - x == 0.
Proof. intros; apply Qplus_opp_r. Qed.

Lemma Qminus_eq_eq_plus_r : ∀ x y z, x - y == z → x == z + y.
Proof.
intros.
rewrite <- H.
rewrite <- Qplus_minus_swap, <- Qplus_minus_assoc.
rewrite Qminus_diag, Qplus_0_r.
reflexivity.
Qed.

(* TODO: transform the above with ?= like below. *)

Lemma Zplus_cmp_compat_r : ∀ n m p,
  (n ?= m)%Z = (n + p ?= m + p)%Z.
Proof.
intros.
rewrite Zplus_comm.
replace (m + p)%Z with (p + m)%Z by apply Zplus_comm.
symmetry; apply Zcompare_plus_compat.
Qed.

Lemma Zmult_cmp_compat_r : ∀ n m p,
  (0 < p)%Z
  → (n ?= m)%Z = (n * p ?= m * p)%Z.
Proof.
intros.
apply Zmult_compare_compat_r.
apply Z.lt_gt; assumption.
Qed.

Lemma Qplus_cmp_compat_r : ∀ x y z,
  (x ?= y) = (x + z ?= y + z).
Proof.
intros (x₁, x₂) (y₁, y₂) (z₁, z₂).
unfold Qcompare; simpl.
do 2 rewrite Pos2Z.inj_mul.
do 2 rewrite Z.mul_add_distr_r.
do 4 rewrite Z.mul_assoc.
remember (z₁ * ' y₂ * ' x₂ * ' z₂)%Z as t.
remember (z₁ * ' y₂ * ' x₂)%Z as u.
rewrite Z.mul_shuffle0 in Hequ.
subst u.
rewrite <- Heqt.
rewrite <- Zplus_cmp_compat_r.
clear t Heqt.
rewrite <- Zmult_assoc.
rewrite Z.mul_shuffle1.
remember (y₁ * ' z₂ * ' x₂ * ' z₂)%Z as t.
rewrite <- Zmult_assoc in Heqt.
rewrite Z.mul_shuffle1 in Heqt; subst t.
apply Zmult_cmp_compat_r.
rewrite <- Pos2Z.inj_mul.
apply Pos2Z.is_pos.
Qed.

Lemma Qminus_cmp_compat_r : ∀ x y z,
  (x ?= y) = (x - z ?= y - z).
Proof.
intros; unfold Qminus; apply Qplus_cmp_compat_r.
Qed.

Lemma Qcmp_plus_minus_cmp_r : ∀ x y z,
  (x ?= y + z) = (x - z ?= y).
Proof.
intros x y z.
rewrite Qplus_cmp_compat_r with (z := - z).
rewrite <- Qplus_assoc.
rewrite Qplus_opp_r, Qplus_0_r.
reflexivity.
Qed.
Lemma Qeq_plus_minus_eq_r : ∀ x y z, x == y + z → x - z == y.
Proof.
intros.
apply Qeq_alt in H; apply Qeq_alt.
rewrite <- H; symmetry; apply Qcmp_plus_minus_cmp_r.
Qed.
Lemma Qlt_plus_minus_lt_r : ∀ x y z, x < y + z → x - z < y.
Proof.
intros.
apply Qlt_alt in H; apply Qlt_alt.
rewrite <- H; symmetry; apply Qcmp_plus_minus_cmp_r.
Qed.

Lemma Qmult_cmp_compat_r : ∀ x y z,
  0 < z
  → (x ?= y) = (x * z ?= y * z).
Proof.
intros (a₁, a₂) (b₁, b₂) (c₁, c₂) H.
unfold Qcompare; simpl.
do 2 rewrite Pos2Z.inj_mul.
rewrite Z.mul_shuffle1, (Z.mul_shuffle1 b₁).
rewrite <- Zmult_cmp_compat_r; [ reflexivity | idtac ].
apply Z.mul_pos_pos; [ idtac | reflexivity ].
unfold Qlt in H; simpl in H.
rewrite Zmult_1_r in H; assumption.
Qed.

Lemma Qcmp_shift_mult_l : ∀ x y z,
  0 < z
  → (x / z ?= y) = (x ?= y * z).
Proof.
intros x y z Hz.
erewrite Qmult_cmp_compat_r; [ idtac | eassumption ].
rewrite Qmult_div_swap.
unfold Qdiv.
rewrite <- Qmult_assoc.
rewrite Qmult_inv_r; [ idtac | apply Qgt_0_not_0; assumption ].
rewrite Qmult_1_r; reflexivity.
Qed.
Lemma Qlt_shift_mult_l : ∀ x y z, 0 < z → x / z < y → x < y * z.
Proof.
intros x y z Hc H.
rewrite Qlt_alt in H |- *.
rewrite <- H; symmetry; apply Qcmp_shift_mult_l; assumption.
Qed.

Lemma Qcmp_shift_mult_r : ∀ x y z,
  0 < z
  → (x ?= y / z) = (x * z ?= y).
Proof.
intros x y z Hz.
erewrite Qmult_cmp_compat_r; [ idtac | eassumption ].
rewrite Qmult_div_swap.
unfold Qdiv.
rewrite <- Qmult_assoc.
rewrite Qmult_inv_r; [ idtac | apply Qgt_0_not_0; assumption ].
rewrite Qmult_1_r; reflexivity.
Qed.
Lemma Qlt_shift_mult_r : ∀ x y z, 0 < z → x < y / z → x * z < y.
Proof.
intros x y z Hc H.
rewrite Qlt_alt in H |- *.
rewrite <- H; symmetry; apply Qcmp_shift_mult_r; assumption.
Qed.

Lemma Qplus_cmp_cmp_minus_r : ∀ x y z,
  (x + y ?= z) = (x ?= z - y).
Proof.
intros x y z.
rewrite Qplus_cmp_compat_r with (z := - y).
rewrite <- Qplus_assoc.
rewrite Qplus_opp_r, Qplus_0_r.
reflexivity.
Qed.
Lemma Qplus_lt_lt_minus_r : ∀ x y z, x + y < z → x < z - y.
Proof.
intros x y z H.
rewrite Qlt_alt in H |- *.
rewrite <- H; symmetry; apply Qplus_cmp_cmp_minus_r.
Qed.

Lemma Qplus_cmp_compat_l : ∀ x y z,
  (x ?= y) = (z + x ?= z + y).
Proof.
intros x y z.
do 2 rewrite (Qplus_comm z).
apply Qplus_cmp_compat_r.
Qed.

Lemma list_cons_app {T} : ∀ x : T, ∀ l, [x … l] = [x] ++ l.
Proof. reflexivity. Qed.

Lemma list_Forall_inv : ∀ A (P : A → Prop) a l,
  List.Forall P [a … l] → P a ∧ List.Forall P l.
Proof.
intros A P a l H.
inversion H; split; assumption.
Qed.

Lemma Zpos_ne_0 : ∀ p, (' p ≠ 0)%Z.
Proof.
intros p H.
pose proof (Zgt_pos_0 p) as HH.
rewrite H in HH.
apply Zgt_irrefl in HH; assumption.
Qed.

Lemma Qnum_inv : ∀ a, (0 < Qnum a)%Z → Qnum (/ a) = Zpos (Qden a).
Proof.
intros (a, b) Ha; simpl in Ha |- *.
unfold Qinv; simpl.
destruct a as [| a| a]; simpl.
 apply Zlt_irrefl in Ha; contradiction.

 reflexivity.

 apply Zlt_not_le in Ha.
 exfalso; apply Ha, Z.lt_le_incl, Zlt_neg_0.
Qed.

Lemma Qden_inv : ∀ a, (0 < Qnum a)%Z → Zpos (Qden (/ a)) = Qnum a.
Proof.
intros (a, b) Ha; simpl in Ha |- *.
unfold Qinv; simpl.
destruct a as [| a| a]; simpl.
 apply Zlt_irrefl in Ha; contradiction.

 reflexivity.

 apply Zlt_not_le in Ha.
 exfalso; apply Ha, Z.lt_le_incl, Zlt_neg_0.
Qed.

Lemma Qdiv_mul : ∀ a b c d,
  a ≠ 0%Z
  → (0 < c)%Z
    → (a # b) / (c # d) == a * Zpos d # b * Z.to_pos c.
Proof.
intros a b c d Ha Hc.
unfold Qeq; simpl.
do 2 rewrite Pos2Z.inj_mul.
rewrite Z.mul_shuffle1; symmetry.
rewrite Z.mul_shuffle1.
apply Z.mul_cancel_l.
 apply Z.neq_mul_0.
 split; [ assumption | apply Zpos_ne_0 ].

 rewrite Qden_inv; [ idtac | assumption ].
 rewrite Qnum_inv; [ idtac | assumption ].
 remember Zmult as f; simpl; subst f.
 apply Z.mul_cancel_l; [ apply Zpos_ne_0 | idtac ].
 symmetry; apply Z2Pos.id; assumption.
Qed.

Lemma Qnum_minus_distr_r : ∀ a b c, a - b # c == ((a # c) - (b # c)).
Proof.
intros a b c.
unfold Qeq; simpl.
rewrite Zmult_minus_distr_r.
rewrite Zmult_plus_distr_l.
rewrite Pos2Z.inj_mul.
do 2 rewrite Zmult_assoc.
do 2 rewrite Z.mul_opp_l.
reflexivity.
Qed.

Lemma Qnum_nat_minus : ∀ a b,
  (b ≤ a)%nat
  → Qnum (Qnat a - Qnat b) = Z.of_nat (a - b).
Proof.
intros a b Hba.
unfold Qnat; simpl.
do 2 rewrite Zmult_1_r.
symmetry.
apply Nat2Z.inj_sub; assumption.
Qed.

Lemma Qden_nat_minus : ∀ a b, Zpos (Qden (Qnat a - Qnat b)) = 1%Z.
Proof. reflexivity. Qed.

Lemma Pmul_not_1 : ∀ a b, (1 < a)%positive → (a * b ≠ 1)%positive.
Proof.
intros a b Ha H.
apply Pos.mul_eq_1_l in H.
subst a; revert Ha; apply Plt_irrefl.
Qed.

Definition pair_rec A B C (f : A → B → C) := λ xy, f (fst xy) (snd xy).

Definition Plcm a b := Z.to_pos (Z.lcm (Zpos a) (Zpos b)).

Lemma Plcm_comm : ∀ a b, Plcm a b = Plcm b a.
Proof.
intros a b.
unfold Plcm.
rewrite Z.lcm_comm.
reflexivity.
Qed.

Lemma Plcm_diag : ∀ a, Plcm a a = a.
Proof.
intros a.
unfold Plcm.
rewrite Z.lcm_diag.
reflexivity.
Qed.

Lemma Zlcm_pos_pos_is_pos : ∀ a b, (0 < Z.lcm (' a) (' b))%Z.
Proof.
intros a b.
remember (Z.lcm (' a) (' b)) as l.
symmetry in Heql.
destruct l as [| l| l].
 apply Z.lcm_eq_0 in Heql.
 destruct Heql as [Heql | Heql]; exfalso; revert Heql; apply Zpos_ne_0.

 apply Pos2Z.is_pos.

 pose proof (Z.lcm_nonneg (' a) (' b)) as H.
 rewrite Heql in H.
 apply Zle_not_lt in H.
 exfalso; apply H.
 apply Zlt_neg_0.
Qed.

Lemma Plcm_assoc : ∀ a b c, Plcm (Plcm a b) c = Plcm a (Plcm b c).
Proof.
intros a b c.
unfold Plcm; simpl.
rewrite Z2Pos.id; [ idtac | apply Zlcm_pos_pos_is_pos ].
rewrite Z2Pos.id; [ idtac | apply Zlcm_pos_pos_is_pos ].
rewrite Z.lcm_assoc; reflexivity.
Qed.

Lemma Plcm_1_l : ∀ n, Plcm 1 n = n.
Proof.
intros n.
unfold Plcm.
rewrite Z.lcm_1_l; reflexivity.
Qed.

Lemma divmod_div : ∀ a b, fst (divmod a b 0 b) = (a / S b)%nat.
Proof. intros a b; reflexivity. Qed.

Lemma divmod_mod : ∀ a b, (b - snd (divmod a b 0 b) = a mod S b)%nat.
Proof. intros a b; reflexivity. Qed.

Lemma Pos2Nat_ne_0 : ∀ a, (Pos.to_nat a ≠ 0)%nat.
Proof.
intros a H.
pose proof Pos2Nat.is_pos a as HH.
rewrite H in HH.
revert HH; apply lt_irrefl.
Qed.

Open Scope Z_scope.

Lemma Zpos_divides_div : ∀ a b, ('a | 'b) → 'b / 'a ≠ 0.
Proof.
intros a b Hab.
destruct Hab as (c, Hab).
rewrite Hab.
rewrite Z.div_mul; [ idtac | apply Zpos_ne_0 ].
destruct c; [ discriminate Hab | apply Zpos_ne_0 | discriminate Hab ].
Qed.

Close Scope Z_scope.

Open Scope positive_scope.

Lemma Pos_mul_shuffle0 : ∀ n m p, n * m * p = n * p * m.
Proof.
intros n m p.
rewrite <- Pos.mul_assoc.
remember (m * p) as mp.
rewrite Pos.mul_comm in Heqmp; subst mp.
apply Pos.mul_assoc.
Qed.

Lemma Pos_div_mul_r : ∀ a b,
  (a | b)
  → (Pos.of_nat (Pos.to_nat b / Pos.to_nat a) * a) = b.
Proof.
intros a b Hab.
destruct Hab as (c, Hab).
subst b.
rewrite Pos2Nat.inj_mul.
rewrite Nat.div_mul; [ idtac | apply Pos2Nat_ne_0 ].
rewrite Pos2Nat.id; reflexivity.
Qed.

Lemma Pos_div_mul_l : ∀ a b,
  (a | b)
  → (a * Pos.of_nat (Pos.to_nat b / Pos.to_nat a)) = b.
Proof.
intros a b Hab.
rewrite Pos.mul_comm.
apply Pos_div_mul_r; assumption.
Qed.

Lemma Pos_divides_lcm_l : ∀ a b, (a | Plcm a b).
Proof.
intros a b.
unfold Plcm, Z.lcm, Pos.divide.
rewrite Z.mul_comm, Z.gcd_comm.
rewrite Z.abs_mul; simpl.
rewrite Z2Pos.inj_mul; simpl.
 exists (Z.to_pos (Z.abs (' b / ' Pos.gcd b a))); reflexivity.

 apply Z.abs_pos.
 apply Zpos_divides_div.
 rewrite Pos2Z.inj_gcd.
 apply Z.gcd_divide_l.

 apply Pos2Z.is_pos.
Qed.

Lemma Pos_divides_lcm_r : ∀ a b, (b | Plcm a b).
Proof.
intros a b.
rewrite Plcm_comm.
apply Pos_divides_lcm_l.
Qed.

Lemma Pos_mul_shuffle1 : ∀ n m p q, n * m * (p * q) = n * p * (m * q).
Proof.
intros n m p q.
do 2 rewrite <- Pos.mul_assoc.
f_equal.
do 2 rewrite Pos.mul_assoc.
rewrite Pos_mul_shuffle0, Pos.mul_comm, Pos.mul_assoc.
reflexivity.
Qed.

Close Scope positive_scope.

Lemma min_add_sub : ∀ x y, (min x y + (x - y) = x)%nat.
Proof.
intros x y.
destruct (le_dec x y) as [Hle| Hgt].
 rewrite Nat.min_l; [ idtac | assumption ].
 apply Nat.sub_0_le in Hle; rewrite Hle, plus_0_r; reflexivity.

 apply not_ge in Hgt.
 rewrite Nat.min_r; [ idtac | apply Nat.lt_le_incl; assumption ].
 apply le_plus_minus_r, Nat.lt_le_incl; assumption.
Qed.

Lemma Z2Nat_sub_min1 : ∀ x y z,
  (Z.to_nat (Z.min x y - z) + Z.to_nat (y - x))%nat =
  Z.to_nat (y - Z.min z x).
Proof.
intros x y z.
rewrite <- Z.sub_min_distr_r.
rewrite <- Z.sub_max_distr_l.
destruct (Z_le_dec (x - z) (y - z)) as [Hle₁| Hgt₁].
 rewrite Z.min_l; [ idtac | assumption ].
 apply Z.sub_le_mono_r in Hle₁.
 destruct (Z_le_dec (y - z) (y - x)) as [Hle₂| Hgt₂].
  rewrite Z.max_r; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hle₂.
  rewrite Z.sub_le_mono_r with (p := z) in Hle₂.
  rewrite Z.sub_diag in Hle₂.
  destruct (x - z)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hle₂.
  exfalso; apply Hle₂, Pos2Z.is_pos.

  apply Z.nle_gt, Z.lt_le_incl in Hgt₂.
  rewrite Z.max_l; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hgt₂.
  rewrite Z.sub_le_mono_r with (p := x) in Hle₁.
  rewrite Z.sub_diag in Hle₁.
  rewrite Z.sub_le_mono_r with (p := z) in Hgt₂.
  rewrite Z.sub_diag in Hgt₂.
  rewrite <- Z2Nat.inj_add; [ idtac | assumption | assumption ].
  rewrite Z.add_comm, Z.add_sub_assoc, Z.sub_add.
  reflexivity.

 apply Z.nle_gt, Z.lt_le_incl in Hgt₁.
 rewrite Z.min_r; [ idtac | assumption ].
 apply Z.sub_le_mono_r in Hgt₁.
 destruct (Z_le_dec (y - z) (y - x)) as [Hle₂| Hgt₂].
  rewrite Z.max_r; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hle₂.
  eapply Z.le_trans in Hle₂; [ idtac | eassumption ].
  rewrite Z.sub_le_mono_r with (p := z) in Hle₂.
  rewrite Z.sub_diag in Hle₂.
  destruct (y - z)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hle₂.
  exfalso; apply Hle₂, Pos2Z.is_pos.

  apply Z.nle_gt, Z.lt_le_incl in Hgt₂.
  rewrite Z.max_l; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hgt₂.
  rewrite Z.sub_le_mono_r with (p := x) in Hgt₁.
  rewrite Z.sub_diag in Hgt₁.
  rewrite Nat.add_comm.
  destruct (y - x)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hgt₁.
  exfalso; apply Hgt₁, Pos2Z.is_pos.
Qed.

Lemma Z2Nat_sub_min2 : ∀ x y z,
  (Z.to_nat (Z.min x y - z) + Z.to_nat (x - y))%nat =
  Z.to_nat (x - Z.min y z).
Proof.
intros x y z.
rewrite <- Z.sub_min_distr_r.
rewrite <- Z.sub_max_distr_l.
destruct (Z_le_dec (x - z) (y - z)) as [Hle₁| Hgt₁].
 rewrite Z.min_l; [ idtac | assumption ].
 apply Z.sub_le_mono_r in Hle₁.
 destruct (Z_le_dec (x - y) (x - z)) as [Hle₂| Hgt₂].
  rewrite Z.max_r; [ idtac | assumption ].
  rewrite Z.sub_le_mono_r with (p := y) in Hle₁.
  rewrite Z.sub_diag in Hle₁.
  rewrite Nat.add_comm.
  destruct (x - y)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hle₁.
  exfalso; apply Hle₁, Pos2Z.is_pos.

  apply Z.nle_gt, Z.lt_le_incl in Hgt₂.
  rewrite Z.max_l; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hgt₂.
  eapply Z.le_trans in Hgt₂; [ idtac | eassumption ].
  rewrite Z.sub_le_mono_r with (p := z) in Hgt₂.
  rewrite Z.sub_diag in Hgt₂.
  destruct (x - z)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hgt₂.
  exfalso; apply Hgt₂, Pos2Z.is_pos.

 apply Z.nle_gt, Z.lt_le_incl in Hgt₁.
 rewrite Z.min_r; [ idtac | assumption ].
 apply Z.sub_le_mono_r in Hgt₁.
 destruct (Z_le_dec (x - y) (x - z)) as [Hle₂| Hgt₂].
  rewrite Z.max_r; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hle₂.
  rewrite Z.sub_le_mono_r with (p := y) in Hgt₁.
  rewrite Z.sub_diag in Hgt₁.
  rewrite Z.sub_le_mono_r with (p := z) in Hle₂.
  rewrite Z.sub_diag in Hle₂.
  rewrite <- Z2Nat.inj_add; [ idtac | assumption | assumption ].
  rewrite Z.add_comm, Z.add_sub_assoc, Z.sub_add.
  reflexivity.

  apply Z.nle_gt, Z.lt_le_incl in Hgt₂.
  rewrite Z.max_l; [ idtac | assumption ].
  apply Z.sub_le_mono_l in Hgt₂.
  rewrite Z.sub_le_mono_r with (p := z) in Hgt₂.
  rewrite Z.sub_diag in Hgt₂.
  destruct (y - z)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
  apply Z.le_ngt in Hgt₂.
  exfalso; apply Hgt₂, Pos2Z.is_pos.
Qed.

Lemma Z2Nat_inj_mul_pos_r : ∀ n m,
  Z.to_nat (n * 'm) = (Z.to_nat n * Pos.to_nat m)%nat.
Proof.
intros n m.
destruct n as [| n| ]; [ reflexivity | simpl | reflexivity ].
rewrite Pos2Nat.inj_mul; reflexivity.
Qed.

Lemma Z_add_neg : ∀ a b, (a + Z.neg b = a - Z.pos b)%Z.
Proof. reflexivity. Qed.

Lemma Z2Nat_sub_add_nat_l : ∀ a b, (0 <= a)%Z
  → (Z.to_nat (a + Z.of_nat b) - Z.to_nat a)%nat = b.
Proof.
intros a b Ha.
unfold Z.of_nat; simpl.
destruct a as [| a| a]; simpl.
 rewrite Nat.sub_0_r.
 destruct b as [| b]; [ reflexivity | simpl ].
 rewrite SuccNat2Pos.id_succ; reflexivity.

 destruct b as [| b]; simpl.
  rewrite Nat.sub_diag; reflexivity.

  rewrite Pos2Nat.inj_add.
  rewrite SuccNat2Pos.id_succ.
  rewrite Nat.add_comm, Nat.add_sub; reflexivity.

 apply Zle_not_lt in Ha.
 exfalso; apply Ha, Pos2Z.neg_is_neg.
Qed.

Lemma Z2Nat_sub_add_nat_r : ∀ a b,
  (Z.to_nat a - Z.to_nat (a + Z.of_nat b))%nat = O.
Proof.
intros a b.
unfold Z.of_nat; simpl.
destruct a as [| a| a]; [ reflexivity | simpl | reflexivity ].
destruct b as [| b]; simpl.
 rewrite Nat.sub_diag; reflexivity.

 rewrite Pos2Nat.inj_add.
 rewrite Nat.sub_add_distr, Nat.sub_diag; reflexivity.
Qed.

Lemma min_if_then_else : ∀ x y, min x y = if lt_dec x y then x else y.
Proof.
intros x y.
destruct (Nat.min_dec x y) as [Hlt| Hge].
 rewrite Hlt.
 destruct (lt_dec x y) as [| Hge]; [ reflexivity | idtac ].
 apply not_gt in Hge.
 apply le_antisym; [ idtac | assumption ].
 rewrite <- Hlt.
 apply Min.le_min_r.

 rewrite Hge.
 destruct (lt_dec x y) as [Hlt| ]; [ idtac | reflexivity ].
 apply gt_not_le in Hlt.
 exfalso; apply Hlt.
 rewrite <- Hge.
 apply Min.le_min_l.
Qed.

Lemma Z2Nat_lt_le : ∀ n m, (n < m)%Z → (Z.to_nat n ≤ Z.to_nat m)%nat.
Proof.
intros n m Hnm.
destruct n as [| n| n].
 apply Nat.le_0_l.

 destruct m as [| m| m].
  apply Zlt_not_le in Hnm.
  exfalso; apply Hnm, Pos2Z.is_nonneg.

  simpl.
  apply Nat.lt_le_incl.
  apply Pos2Nat.inj_lt.
  assumption.

  apply Zlt_not_le in Hnm.
  exfalso; apply Hnm.
  apply Zle_neg_pos.

 apply Nat.le_0_l.
Qed.

Lemma Z2Nat_lt_lt : ∀ n m, (Z.to_nat n < Z.to_nat m)%nat → (n < m)%Z.
Proof.
intros n m Hnm.
destruct n as [| n| n].
 destruct m as [| m| m].
  exfalso; revert Hnm; apply Nat.lt_irrefl.

  apply Pos2Z.is_pos.

  exfalso; revert Hnm; apply Nat.lt_irrefl.

 destruct m as [| m| m].
  apply Nat.lt_le_incl in Hnm.
  apply le_not_lt in Hnm.
  exfalso; apply Hnm; apply Pos2Nat.is_pos.

  apply Pos2Nat.inj_lt in Hnm; assumption.

  simpl in Hnm.
  apply Nat.lt_le_incl in Hnm.
  apply le_not_lt in Hnm.
  exfalso; apply Hnm; apply Pos2Nat.is_pos.

 destruct m as [| m| m].
  exfalso; revert Hnm; apply Nat.lt_irrefl.

  transitivity 0%Z; [ apply Pos2Z.neg_is_neg | apply Pos2Z.is_pos ].

  exfalso; revert Hnm; apply Nat.lt_irrefl.
Qed.

Lemma Z2Nat_add_cancel_r : ∀ n m p,
  (Z.to_nat (n + p) < Z.to_nat (m + p))%nat → (n < m)%Z.
Proof.
intros n m p Hnm.
apply Z.add_lt_mono_r with (p := p).
apply Z2Nat_lt_lt.
assumption.
Qed.
