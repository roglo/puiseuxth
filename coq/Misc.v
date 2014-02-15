(* Misc.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).
Notation "x ++ y" := (List.app x y) (right associativity, at level 60).
Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level).
Notation "x < y <= z" := (x < y ∧ y <= z) (at level 70, y at next level).
Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

Ltac negation H := exfalso; apply H; reflexivity.
Tactic Notation "fast_omega" hyp_list(Hs) := revert Hs; clear; intros; omega.

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

Lemma Pos2Z_ne_0 : ∀ p, (' p ≠ 0)%Z.
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
 split; [ assumption | apply Pos2Z_ne_0 ].

 rewrite Qden_inv; [ idtac | assumption ].
 rewrite Qnum_inv; [ idtac | assumption ].
 remember Zmult as f; simpl; subst f.
 apply Z.mul_cancel_l; [ apply Pos2Z_ne_0 | idtac ].
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
 destruct Heql as [Heql | Heql]; exfalso; revert Heql; apply Pos2Z_ne_0.

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
Hint Resolve Pos2Nat_ne_0.

Open Scope Z_scope.

Lemma Zpos_divides_div : ∀ a b, ('a | 'b) → 'b / 'a ≠ 0.
Proof.
intros a b Hab.
destruct Hab as (c, Hab).
rewrite Hab.
rewrite Z.div_mul; [ idtac | apply Pos2Z_ne_0 ].
destruct c; [ discriminate Hab | apply Pos2Z_ne_0 | discriminate Hab ].
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

Lemma Z2Nat_sub_min :  ∀ x y, Z.to_nat (x - Z.min x y) = Z.to_nat (x - y).
Proof.
intros x y.
destruct (Z.min_dec x y) as [H₁| H₁].
 rewrite H₁.
 rewrite Z.sub_diag.
 apply Z.min_l_iff in H₁.
 apply Z.le_sub_0 in H₁.
 destruct (x - y)%Z as [| p| p]; [ reflexivity | idtac | reflexivity ].
 apply Z.nlt_ge in H₁.
 exfalso; apply H₁, Pos2Z.is_pos.

 rewrite H₁; reflexivity.
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

Lemma Nat_sub_sub_distr : ∀ n m p, (p ≤ m → n - (m - p) = n + p - m)%nat.
Proof.
intros n m p Hpm.
rewrite Nat.add_comm.
revert n m Hpm.
induction p; intros.
 rewrite Nat.sub_0_r, Nat.add_0_l; reflexivity.

 destruct m as [| m].
  exfalso; revert Hpm; apply Nat.nle_succ_0.

  rewrite Nat.sub_succ; simpl.
  apply Nat.succ_le_mono in Hpm.
  apply IHp; assumption.
Qed.

Lemma Z2Nat_id_max : ∀ x, Z.of_nat (Z.to_nat x) = Z.max 0 x.
Proof.
intros x.
destruct x as [| x| x]; [ reflexivity | idtac | reflexivity ].
rewrite Z2Nat.id; [ reflexivity | apply Pos2Z.is_nonneg ].
Qed.

Lemma Nat_sub_succ_1 : ∀ n, (S n - 1 = n)%nat.
Proof. intros n; simpl; rewrite Nat.sub_0_r; reflexivity. Qed.

Definition Nat_div_sup x y := ((x + y - 1) / y)%nat.

Theorem Nat_fold_div_sup : ∀ x y, ((x + y - 1) / y)%nat = Nat_div_sup x y.
Proof. reflexivity. Qed.

Theorem Nat_lt_div_sup_lt_mul_r : ∀ n m p,
  (n < Nat_div_sup m p → n * p < m)%nat.
Proof.
intros n m p Hn.
unfold Nat_div_sup in Hn.
destruct p as [| p]; [ exfalso; revert Hn; apply Nat.nlt_0_r | idtac ].
destruct (zerop (m mod S p)) as [Hz| Hnz].
 apply Nat.mod_divide in Hz; [ idtac | intros H; discriminate H ].
 destruct Hz as (k, Hz).
 subst m.
 rewrite Nat.add_comm in Hn.
 simpl in Hn.
 rewrite divmod_div in Hn.
 rewrite Nat.sub_0_r in Hn.
 rewrite Nat.div_add in Hn; [ idtac | intros H; discriminate H ].
 rewrite Nat.div_small in Hn.
  simpl in Hn.
  apply Nat.mul_lt_mono_pos_r; [ idtac | assumption ].
  apply Nat.lt_0_succ.

  apply Nat.lt_succ_r; reflexivity.

 destruct m as [| m].
  rewrite Nat.mod_0_l in Hnz; [ idtac | intros H; discriminate H ].
  exfalso; revert Hnz; apply Nat.lt_irrefl.

  simpl in Hn.
  rewrite divmod_div in Hn.
  rewrite Nat.sub_0_r in Hn.
  remember (m + S p)%nat as q.
  replace (S p) with (1 * S p)%nat in Heqq .
   subst q.
   rewrite Nat.div_add in Hn; [ idtac | intros H; discriminate H ].
   rewrite Nat.add_1_r in Hn.
   apply Nat.lt_succ_r with (m := (m / S p)%nat) in Hn.
   apply Nat.mul_le_mono_pos_r with (p := S p) in Hn.
    eapply Nat.le_lt_trans; [ eassumption | idtac ].
    apply Nat.succ_le_mono with (m := m).
    rewrite Nat.mul_comm.
    apply Nat.mul_div_le.
    intros H; discriminate H.

    apply Nat.lt_0_succ.

   rewrite Nat.mul_1_l; reflexivity.
Qed.

Theorem Nat_lt_mul_r_lt_div_sup : ∀ n m p, (0 < p →
  n * p < m → n < Nat_div_sup m p)%nat.
Proof.
intros n m p Hp Hn.
unfold Nat_div_sup.
destruct p as [| p]; [ exfalso; revert Hp; apply Nat.lt_irrefl | idtac ].
destruct (zerop (m mod S p)) as [Hz| Hnz].
 apply Nat.mod_divide in Hz; [ idtac | intros H; discriminate H ].
 destruct Hz as (k, Hz); subst m.
 rewrite Nat.add_comm; simpl; rewrite divmod_div, Nat.sub_0_r.
 rewrite Nat.div_add; [ idtac | intros H; discriminate H ].
 rewrite Nat.div_small; [ simpl | apply Nat.lt_succ_diag_r ].
 apply Nat.mul_lt_mono_pos_r in Hn; [ assumption | apply Nat.lt_0_succ ].

 (* à revoir... *)
 assert (m = S p * (m / S p) + m mod S p)%nat as Hm.
  apply Nat.div_mod; intros H; discriminate H.

  rewrite Hm in Hn.
  remember (m / S p)%nat as q.
  remember (m mod S p) as r.
  apply Nat.lt_trans with (p := (S p * q + S p * 1)%nat) in Hn.
   rewrite <- Nat.mul_add_distr_l in Hn.
   rewrite Nat.mul_comm in Hn.
   apply Nat.mul_lt_mono_pos_l in Hn; [ idtac | apply Nat.lt_0_succ ].
   rewrite Nat.add_comm; simpl; rewrite divmod_div, Nat.sub_0_r.
   rewrite Hm.
   rewrite Nat.add_assoc, Nat.add_shuffle0.
   rewrite Nat.mul_comm.
   rewrite Nat.div_add; [ idtac | intros H; discriminate H ].
   rewrite Nat.add_1_r in Hn.
   apply Nat.lt_succ_r with (n := n) in Hn.
   eapply Nat.le_lt_trans; [ eassumption | idtac ].
   assert (1 <= (p + r) / S p)%nat as Hq.
    destruct r; [ exfalso; revert Hnz; apply Nat.lt_irrefl | idtac ].
    rewrite <- Nat.add_succ_comm, Nat.add_comm.
    remember (r + S p)%nat as x.
    replace (S p) with (1 * S p)%nat in Heqx ; subst x.
     rewrite Nat.div_add; [ idtac | intros H; discriminate H ].
     rewrite Nat.add_comm; simpl.
     apply Nat.succ_le_mono with (n := O).
     apply Nat.le_0_l.

     rewrite Nat.mul_1_l; reflexivity.

    destruct ((p + r) / S p)%nat.
     apply Nat.nlt_ge in Hq.
     exfalso; apply Hq; apply Nat.lt_0_1.

     apply Nat.lt_succ_r with (m := (n0 + q)%nat).
     apply Nat.le_sub_le_add_r.
     rewrite Nat.sub_diag.
     apply Nat.le_0_l.

   apply Nat.add_lt_mono_l.
   rewrite Nat.mul_1_r, Heqr.
   apply Nat.mod_upper_bound.
   intros H; discriminate H.
Qed.

Lemma le_div_sup_mul : ∀ a b, (0 < b → a ≤ Nat_div_sup a b * b)%nat.
Proof.
intros a b Hbpos.
unfold Nat_div_sup.
rewrite Nat.mul_comm.
apply Nat.add_le_mono_r with (p := (a + b - 1) mod b).
rewrite <- Nat.div_mod.
 rewrite <- Nat.add_sub_assoc.
  apply Nat.add_le_mono_l.
  rewrite Nat.sub_1_r.
  apply Nat.lt_le_pred.
  apply Nat.mod_upper_bound.
  intros H; subst b; revert Hbpos; apply Nat.lt_irrefl.

  apply lt_le_S; assumption.

 intros H; subst b; revert Hbpos; apply Nat.lt_irrefl.
Qed.

Lemma Z_div_pos_is_nonneg : ∀ x y, (0 <= ' x / ' y)%Z.
Proof.
intros x y.
apply Z_div_pos.
 apply Z.lt_gt, Pos2Z.is_pos.

 apply Pos2Z.is_nonneg.
Qed.

Lemma Pos2Nat_to_pos : ∀ x,
  (0 < x)%Z
  → Pos.to_nat (Z.to_pos x) = Z.to_nat x.
Proof.
intros x Hx.
destruct x as [| x| x].
 exfalso; revert Hx; apply Z.lt_irrefl.

 reflexivity.

 exfalso; apply Z.nle_gt in Hx.
 apply Hx, Pos2Z.neg_is_nonpos.
Qed.

Lemma Z_gcd3_div_gcd3 : ∀ a b c g,
  g ≠ 0%Z
  → g = Z.gcd (Z.gcd a b) c
    → Z.gcd (Z.gcd (a / g) (b / g)) (c / g) = 1%Z.
Proof.
intros a b c g Hg Hgabc.
rewrite Z.gcd_div_factor.
 rewrite Z.gcd_div_factor.
  rewrite <- Hgabc.
  rewrite Z.div_same; [ reflexivity | assumption ].

  pose proof (Z.gcd_nonneg (Z.gcd a b) c) as H.
  rewrite <- Hgabc in H; clear Hgabc; omega.

  subst g; apply Z.gcd_divide_l.

  subst g; apply Z.gcd_divide_r.

 pose proof (Z.gcd_nonneg (Z.gcd a b) c) as H.
 rewrite <- Hgabc in H; clear Hgabc; omega.

 subst g.
 etransitivity; [ apply Z.gcd_divide_l | apply Z.gcd_divide_l ].

 subst g.
 etransitivity; [ apply Z.gcd_divide_l | apply Z.gcd_divide_r ].
Qed.

Lemma Nat_mod_add_1 : ∀ a b, (b ≠ 0 → (a + b) mod b = a mod b)%nat.
Proof.
intros a b Hb.
symmetry.
rewrite <- Nat.mod_add with (b := 1%nat); auto with arith.
Qed.

(* Allows proof by induction with the case
     proved for n implies proved for S n
   changed into
     proved for all nats before n implies proved for S n.

   Then, the proof may be easier to perform.
*)
Lemma all_lt_all : ∀ P : nat → Prop,
  (∀ n, (∀ m, (m < n)%nat → P m) → P n)
  → ∀ n, P n.
Proof.
intros P Hm n.
apply Hm.
induction n; intros m Hmn.
 apply Nat.nle_gt in Hmn.
 exfalso; apply Hmn, Nat.le_0_l.

 destruct (eq_nat_dec m n) as [H₁| H₁].
  subst m; apply Hm; assumption.

  apply IHn.
  apply le_neq_lt; [ idtac | assumption ].
  apply Nat.succ_le_mono; assumption.
Qed.

(* it makes 'exists_prime_divisor' work, that's a miracle.
   I was supposed to program 'infinite descent' method, but
   it turned out like this by some rewrittings *)
Lemma infinite_descent : ∀ P : nat → Prop,
  (∀ n, (∀ m, n ≤ m ∨ P m) → P n)
  → ∀ n, P n.
Proof.
intros P HP n.
apply HP.
induction n; intros m.
 left; apply Nat.le_0_l.

 destruct (eq_nat_dec n m) as [H₁| H₁].
  subst m.
  apply HP in IHn.
  right; assumption.

  pose proof (IHn m) as Hm.
  destruct Hm as [Hm| Hm]; [ idtac | right; assumption ].
  left; apply le_neq_lt; assumption.
Qed.

Require Import Znumtheory.

Lemma exists_prime_divisor : ∀ n, (1 < n)%Z → ∃ p, prime p ∧ (p | n)%Z.
Proof.
(* à nettoyer, peut-être *)
intros n Hn.
remember (Z.to_nat n) as nn eqn:Hnn .
assert (n = Z.of_nat nn) as H.
 subst nn.
 rewrite Z2Nat.id; [ reflexivity | idtac ].
 eapply Z.le_trans; [ apply Z.le_0_1 | apply Z.lt_le_incl; assumption ].

 clear Hnn.
 subst n.
 destruct nn.
  apply Z.nle_gt in Hn.
  exfalso; apply Hn, Z.le_0_1.

  destruct nn.
   exfalso; revert Hn; apply Z.lt_irrefl.

   clear Hn.
   induction nn using infinite_descent.
   rename nn into n.
   case (prime_dec (Z.of_nat (S (S n)))); intros H₁.
    exists (Z.of_nat (S (S n))).
    split; [ assumption | reflexivity ].

    apply not_prime_divide in H₁.
     destruct H₁ as (m, ((Hm, Hmn), (p, Hp))).
     pose proof (H (Z.to_nat (m - 2))) as HH.
     destruct HH as [HH| HH].
      apply Nat.nlt_ge in HH.
      exfalso; apply HH; clear HH.
      apply Nat2Z.inj_lt.
      rewrite Z2Nat.id.
       apply Z.add_lt_mono_r with (p := 2%Z).
       rewrite Z.sub_add.
       rewrite Nat2Z.inj_succ in Hmn.
       rewrite Nat2Z.inj_succ in Hmn.
       simpl in Hmn.
       rewrite <- Z.add_1_r in Hmn.
       rewrite <- Z.add_1_r in Hmn.
       rewrite <- Z.add_assoc in Hmn.
       assumption.

       apply Z.add_le_mono_r with (p := 2%Z).
       rewrite Z.sub_simpl_r.
       apply Z.lt_pred_le; assumption.

      assert (S (S (Z.to_nat (m - 2))) = Z.to_nat m)%nat.
       revert Hm; clear; intros.
       rewrite Z2Nat.inj_sub; [ idtac | apply Zle_0_pos ].
       rewrite <- Nat.sub_succ_l.
        rewrite <- Nat.sub_succ_l.
         simpl; rewrite Nat.sub_0_r; reflexivity.

         rewrite <- Z2Nat.inj_succ; [ idtac | omega ].
         apply Z2Nat.inj_le; omega.

        apply Z2Nat.inj_le; omega.

       rewrite H0 in HH.
       rewrite Z2Nat.id in HH; [ idtac | fast_omega Hm ].
       destruct HH as (q, (Hq, Hqm)).
       exists q.
       split; [ assumption | idtac ].
       rewrite Hp.
       destruct Hqm as (c, Hc).
       rewrite Hc, Z.mul_assoc.
       apply Z.divide_factor_r.

     do 2 rewrite Nat2Z.inj_succ.
     fast_omega .
Qed.

Lemma Nat_divides_l : ∀ a b, (∃ c, a = (b * c)%nat) ↔ (b | a)%nat.
Proof.
intros a b.
split; intros H.
 destruct H as (c, Hc); subst a.
 exists c; apply Nat.mul_comm.

 destruct H as (c, Hc); subst a.
 exists c; apply Nat.mul_comm.
Qed.

Lemma Nat_lcm_divides : ∀ a b c,
  (a ≠ 0
   → b ≠ 0
     → (a | c)
       → (b | c)
         → (Nat.lcm a b | c))%nat.
Proof.
intros k l c Hkp Hlp Hkm Hlm.
apply Nat_divides_l in Hkm.
apply Nat_divides_l in Hlm.
apply Nat_divides_l.
destruct Hkm as (k₁, Hk₁).
destruct Hlm as (l₁, Hl₁).
pose proof (Nat.gcd_divide_l k l) as Hk'.
pose proof (Nat.gcd_divide_r k l) as Hl'.
destruct Hk' as (k', Hk').
destruct Hl' as (l', Hl').
remember (gcd k l) as g eqn:Hg .
subst k l.
apply Nat.gcd_div_gcd in Hg.
 rewrite Nat.div_mul in Hg.
  rewrite Nat.div_mul in Hg.
   unfold Nat.lcm.
   rewrite Nat.gcd_mul_mono_r.
   rewrite Hg, Nat.mul_1_l.
   rewrite Nat.div_mul.
    rewrite Hk₁ in Hl₁.
    rewrite Nat.mul_shuffle0 in Hl₁; symmetry in Hl₁.
    rewrite Nat.mul_shuffle0 in Hl₁; symmetry in Hl₁.
    apply Nat.mul_cancel_r in Hl₁.
     exists (k₁ / l')%nat.
     rewrite <- Nat.mul_assoc.
     rewrite <- Nat.divide_div_mul_exact.
      replace (l' * k₁)%nat with (k₁ * l')%nat by apply Nat.mul_comm.
      rewrite Nat.div_mul.
       assumption.

       intros H; apply Hlp; subst l'; reflexivity.

      intros H; apply Hlp; subst l'; reflexivity.

      apply Nat.gauss with (m := k').
       rewrite Hl₁; exists l₁; apply Nat.mul_comm.

       rewrite Nat.gcd_comm; assumption.

     intros H; apply Hlp; subst g; auto.

    intros H; apply Hlp; subst g; auto.

   intros H; apply Hlp; subst g; auto.

  intros H; apply Hlp; subst g; auto.

 intros H; apply Hlp; subst g; auto.
Qed.

Lemma Nat_gcd_le_l : ∀ a b, (a ≠ 0 → Nat.gcd a b ≤ a)%nat.
Proof.
intros a b Ha.
pose proof (Nat.gcd_divide_l a b) as Hg.
destruct Hg as (c, Hg).
rewrite Hg in |- * at 2.
unfold Nat.gcd.
destruct c; [ contradiction | simpl ].
apply le_plus_l.
Qed.

Lemma Nat_le_lcm_l : ∀ a b, (b ≠ 0 → a ≤ Nat.lcm a b)%nat.
Proof.
intros a b Hb.
remember Hb as Hab; clear HeqHab.
apply Nat_gcd_le_l with (b := a) in Hab.
rewrite Nat.gcd_comm in Hab.
unfold Nat.lcm.
eapply Nat.div_le_mono in Hab.
 rewrite Nat.div_same in Hab.
  apply Nat.mul_le_mono_l with (p := a) in Hab.
  rewrite Nat.mul_1_r in Hab; assumption.

  destruct a; [ assumption | idtac ].
  intros H; apply Nat.gcd_eq_0_r in H; contradiction.

 intros H; apply Nat.gcd_eq_0_r in H; contradiction.
Qed.

Lemma Nat_divides_lcm_l : ∀ a b, (a | Nat.lcm a b)%nat.
Proof.
intros a b.
unfold Nat.lcm.
exists (b / gcd a b)%nat.
apply Nat.mul_comm.
Qed.

Lemma List_in_nth : ∀ A (x : A) l d,
  x ∈ l
  → ∃ n, List.nth n l d = x ∧ (n < List.length l)%nat.
Proof.
intros A x l d Hx.
apply List.In_split in Hx.
destruct Hx as (l₁, (l₂, Hx)).
exists (List.length l₁).
subst l; split.
 induction l₁ as [| y]; [ reflexivity | assumption ].

 rewrite List.app_length; simpl.
 apply Nat.lt_sub_lt_add_l.
 rewrite Nat.sub_diag.
 apply Nat.lt_0_succ.
Qed.

Lemma list_map_app_at : ∀ A B (g : A → B) l x,
  List.map g l ++ [g x] = List.map g (l ++ [x]).
Proof.
intros.
induction l as [| b]; [ reflexivity | simpl ].
rewrite IHl; reflexivity.
Qed.

Lemma imp_or_tauto : ∀ A B : Prop, (A → B) → A → A ∧ B.
Proof. tauto. Qed.

Lemma list_nth_last : ∀ A (l : list A) d len,
  pred (length l) = len
  → List.nth len l d = List.last l d.
Proof.
intros A l d len H.
revert d len H.
induction l as [| x]; intros.
 subst len; reflexivity.

 simpl in H.
 destruct len.
  simpl.
  destruct l; [ reflexivity | discriminate H ].

  remember List.last as g; simpl; subst g.
  rewrite IHl.
   simpl.
   destruct l; [ discriminate H | reflexivity ].

   rewrite H; reflexivity.
Qed.

Lemma list_last_cons_app : ∀ A x y (l : list A) d,
  List.last [x … l ++ [y]] d = y.
Proof.
intros A x y l d.
revert x.
induction l as [| z]; [ reflexivity | intros ].
simpl in IHl; simpl.
apply IHl.
Qed.

Lemma list_skipn_cons_nth : ∀ A c₁ (cl cl₁ : list A) i d,
  List.skipn i cl = [c₁ … cl₁]
  → List.nth i cl d = c₁.
Proof.
intros A c₁ cl cl₁ i d H.
revert cl H.
induction i; intros.
 destruct cl as [| c]; [ discriminate H | idtac ].
 simpl in H; simpl.
 injection H; intros; subst; reflexivity.

 destruct cl as [| c]; [ discriminate H | idtac ].
 simpl in H; simpl.
 apply IHi; assumption.
Qed.

Lemma list_nth_nil : ∀ A n (d : A), List.nth n [] d = d.
Proof. intros A n d; destruct n; reflexivity. Qed.

Lemma list_skipn_nil : ∀ A n, List.skipn n [] = ([] : list A).
Proof. intros A n; destruct n; reflexivity. Qed.

Lemma list_skipn_overflow : ∀ A n (cl : list A),
  length cl ≤ n → List.skipn n cl = [].
Proof.
intros A n cl H.
revert n H.
induction cl as [| c]; intros.
 rewrite list_skipn_nil; reflexivity.

 destruct n; [ exfalso; simpl in H; fast_omega H | simpl ].
 apply IHcl, le_S_n; assumption.
Qed.

Lemma list_skipn_overflow_if : ∀ A n (cl : list A),
  List.skipn n cl = [] → length cl ≤ n.
Proof.
intros A n cl H.
revert n H.
induction cl as [| c]; intros; [ apply Nat.le_0_l | simpl ].
destruct n; [ discriminate H | idtac ].
apply le_n_S, IHcl; assumption.
Qed.

Lemma list_nth_skipn : ∀ α i j (l : list α) d,
  List.nth i (List.skipn j l) d = List.nth (i + j) l d.
Proof.
intros α i j l d.
revert i j d.
induction l as [| x]; intros; simpl.
 rewrite list_skipn_nil; simpl.
 destruct (i + j)%nat, i; reflexivity.

 destruct j; simpl; [ rewrite Nat.add_0_r; reflexivity | idtac ].
 rewrite IHl, Nat.add_succ_r; reflexivity.
Qed.

Lemma match_id : ∀ α a (b : α), match a with O => b | S _ => b end = b.
Proof. intros α a b; destruct a; reflexivity. Qed.

Lemma fold_sub_succ_l : ∀ a b,
  (match a with 0 => S b | S c => b - c end = S b - a)%nat.
Proof. reflexivity. Qed.
