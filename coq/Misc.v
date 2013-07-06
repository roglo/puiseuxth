(* $Id: Misc.v,v 1.28 2013-07-06 09:57:05 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).
Notation "x ++ y" := (List.app x y) (right associativity, at level 60).
Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level).
Notation "x < y <= z" := (x < y ∧ y <= z) (at level 70, y at next level).

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
 exfalso; apply Ha, Zlt_le_weak, Zlt_neg_0.
Qed.

Lemma Qden_inv : ∀ a, (0 < Qnum a)%Z → Zpos (Qden (/ a)) = Qnum a.
Proof.
intros (a, b) Ha; simpl in Ha |- *.
unfold Qinv; simpl.
destruct a as [| a| a]; simpl.
 apply Zlt_irrefl in Ha; contradiction.

 reflexivity.

 apply Zlt_not_le in Ha.
 exfalso; apply Ha, Zlt_le_weak, Zlt_neg_0.
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
