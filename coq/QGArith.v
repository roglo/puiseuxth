(* implementation of rationals with the normal rationals of
   coq (library QArith) together with a field saying that the
   numerator and the denominator are coprimes. This allows to
   use normal equality instead of ==. Therefore rewrite is
   possible. *)

Set Nested Proofs Allowed.
Set Implicit Arguments.
From Stdlib Require Import Utf8.
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.

Notation "x ≤ y" := (Z.le x y) : Z_scope.
Notation "x ≤ y" := (Qle x y) : Q_scope.
Notation "x ≤ y" := (le x y) : nat_scope.
Notation "x ≤ y" := (Pos.le x y) : positive_scope.

Definition Z_pos_gcd z p :=
  match z with
  | Z0 => p
  | Zpos zp => Pos.gcd zp p
  | Zneg zp => Pos.gcd zp p
  end.

Record QG := mk_qg
  {qg_q : Q; qg_gcd : Z_pos_gcd (Qnum qg_q) (Qden qg_q) = 1%positive}.

Theorem Z_pos_gcd_Z_gcd :
  ∀ n d, Z_pos_gcd n d = Z.to_pos (Z.gcd n (Z.pos d)).
Proof.
intros.
unfold Z_pos_gcd.
now destruct n.
Qed.

Theorem Z_pos_gcd_opp_l : ∀ z p, Z_pos_gcd (- z) p = Z_pos_gcd z p.
Proof. now intros; destruct z. Qed.

Theorem Pos_gcd_comm : ∀ a b, Pos.gcd a b = Pos.gcd b a.
Proof.
intros.
apply Pos2Z.inj.
do 2 rewrite Pos2Z.inj_gcd.
apply Z.gcd_comm.
Qed.

Theorem Pos_gcd_le_l : ∀ a b, (Pos.gcd a b <= a)%positive.
Proof.
intros.
specialize (Pos.gcd_divide_l a b) as H1.
apply Z.divide_Zpos in H1.
apply Znumtheory.Zdivide_mod in H1.
apply Zdiv.Zmod_divides in H1; [ | easy ].
destruct H1 as (c & Hc).
destruct c as [| c| c]; [ easy | | easy ].
cbn in Hc.
apply Pos2Z.inj in Hc.
rewrite Hc at 2.
remember (_ * _)%positive as x.
rewrite <- (Pos.mul_1_r (Pos.gcd _ _)); subst x.
apply Pos.mul_le_mono_l.
apply Pos.le_1_l.
Qed.

Theorem Pos_gcd_le_r : ∀ a b, (Pos.gcd a b <= b)%positive.
Proof.
intros.
rewrite Pos_gcd_comm.
apply Pos_gcd_le_l.
Qed.

Theorem Z_ggcd_split :
  ∀ n d g n1 d1,
  Z.ggcd n d = (g, (n1, d1))
  → n = (g * n1)%Z ∧ d = (g * d1)%Z ∧
     Z.gcd n d = g ∧ (g = 0%Z ∨ Z.gcd n1 d1 = 1%Z).
Proof.
intros * Hnd.
specialize (Z.ggcd_correct_divisors n d) as H1.
rewrite Hnd in H1.
destruct H1 as (H1, H2).
split; [ easy | ].
split; [ easy | ].
generalize Hnd; intros H3.
apply (f_equal fst) in H3.
rewrite Z.ggcd_gcd in H3.
cbn in H3.
split; [ easy | ].
destruct (Z.eq_dec g 0) as [Hgz| Hgz]; [ now left | right ].
generalize H3; intros H4.
rewrite H1, H2 in H4.
rewrite Z.gcd_mul_mono_l in H4.
rewrite Z.abs_eq in H4. 2: {
  rewrite <- H3.
  apply Z.gcd_nonneg.
}
rewrite <- (Z.mul_1_r g) in H4 at 2.
now apply Z.mul_reg_l in H4.
Qed.

Theorem Z_pos_gcd_eq_1 :
  ∀ n d,
  Z_pos_gcd n d = 1%positive
  ↔ Z.gcd n (Z.pos d) = 1%Z.
Proof.
intros.
rewrite Z_pos_gcd_Z_gcd.
rewrite <- Z2Pos.inj_1.
split; intros Hnd; [ | now f_equal ].
apply Z2Pos.inj in Hnd; [ easy | | easy ].
destruct (Z.eq_dec (Z.gcd n (Z.pos d)) 0) as [H1| H1]. {
  now apply Z.gcd_eq_0 in H1.
}
specialize (Z.gcd_nonneg n (Z.pos d)) as H2.
apply Z.nle_gt.
intros H3; apply H1.
now apply Z.le_antisymm.
Qed.

Theorem QG_of_Q_prop :
  ∀ q, Z_pos_gcd (Qnum (Qred q)) (Qden (Qred q)) = 1%positive.
Proof.
intros.
destruct q as (n, d); cbn.
remember (Z.ggcd n (Z.pos d)) as g eqn:Hg.
symmetry in Hg.
destruct g as (g, (r1, r2)).
cbn.
apply Z_ggcd_split in Hg.
destruct Hg as (Hn & Hd & Hg & Hg1).
destruct Hg1 as [Hg1| Hg1]. {
  now move Hg1 at top; subst g.
}
apply Z_pos_gcd_eq_1.
rewrite Z2Pos.id; [ easy | ].
apply (Z.mul_lt_mono_pos_l g). {
  apply Z.le_neq.
  split; [ rewrite <- Hg; apply Z.gcd_nonneg | ].
  now intros H; move H at top; subst g.
}
rewrite Z.mul_0_r.
now rewrite <- Hd.
Qed.

Definition QG_of_Q (q : Q) := mk_qg (Qred q) (QG_of_Q_prop q).

Definition QG_of_Z a := QG_of_Q (a # 1).
Definition Z_of_QG a := (Qnum (qg_q a) / QDen (qg_q a))%Z.
Definition QG_of_Z_pair n d := QG_of_Q (n # d).
Definition QG_of_nat_pair n d := QG_of_Q (Z.of_nat n # Pos.of_nat d).

Definition QG_0 := QG_of_Q 0.
Definition QG_1 := QG_of_Q 1.
Definition QG_add (a b : QG) := QG_of_Q (qg_q a + qg_q b).
Definition QG_mul (a b : QG) := QG_of_Q (qg_q a * qg_q b).
Definition QG_opp (a : QG) := QG_of_Q (- qg_q a).
Definition QG_inv (a : QG) := QG_of_Q (/ qg_q a).
Definition QG_sub (a b : QG) := QG_add a (QG_opp b).
Definition QG_div (a b : QG) := QG_mul a (QG_inv b).

Definition QG_eqb (a b : QG) := Qeq_bool (qg_q a) (qg_q b).
Definition QG_leb (a b : QG) := Qle_bool (qg_q a) (qg_q b).
Definition QG_le a b := QG_leb a b = true.
Definition QG_lt a b := QG_leb b a = false.

Declare Scope QG_scope.
Delimit Scope QG_scope with QG.
Bind Scope QG_scope with QG.

Notation "0" := QG_0 : QG_scope.
Notation "1" := QG_1 : QG_scope.
Notation "- a" := (QG_opp a) : QG_scope.
Notation "a + b" := (QG_add a b) : QG_scope.
Notation "a - b" := (QG_sub a b) : QG_scope.
Notation "a * b" := (QG_mul a b) : QG_scope.
Notation "a / b" := (QG_div a b) : QG_scope.
Notation "a '⁻¹'" := (QG_inv a) (at level 1, format "a ⁻¹") :
  QG_scope.

Notation "a =? b" := (QG_eqb a b) (at level 70) : QG_scope.
Notation "a ≤? b" := (QG_leb a b) (at level 70) : QG_scope.
Notation "a <? b" := (negb (QG_leb b a)) (at level 70) : QG_scope.
Notation "a ≤ b" := (QG_le a b) : QG_scope.
Notation "a < b" := (QG_lt a b) : QG_scope.
Notation "a ≤ b ≤ c" := (QG_le a b ∧ QG_le b c)
  (at level 70, b at next level) : QG_scope.
Notation "a ≤ b < c" := (QG_le a b ∧ QG_lt b c)
  (at level 70, b at next level) : QG_scope.
Notation "a < b ≤ c" := (QG_lt a b ∧ QG_le b c)
  (at level 70, b at next level) : QG_scope.
Notation "a < b < c" := (QG_lt a b ∧ QG_lt b c)
  (at level 70, b at next level) : QG_scope.

Theorem fold_QG_of_Z : ∀ a, QG_of_Q (a # 1) = QG_of_Z a.
Proof. easy. Qed.

Theorem eq_QG_eq : ∀ q1 q2 : QG, q1 = q2 ↔ qg_q q1 = qg_q q2.
Proof.
intros.
split; intros Hq; [ now subst q2 | ].
destruct q1 as (q1, Hq1).
destruct q2 as (q2, Hq2).
cbn in Hq; subst q2.
f_equal.
apply (Eqdep_dec.UIP_dec Pos.eq_dec).
Qed.

Theorem neq_QG_neq : ∀ q1 q2 : QG, q1 ≠ q2 ↔ qg_q q1 ≠ qg_q q2.
Proof.
intros.
now split; intros H Hq'; apply H; clear H; apply eq_QG_eq.
Qed.

Theorem QG_of_Q_0 : ∀ d, QG_of_Q (0 # d) = QG_of_Q 0.
Proof.
intros.
now apply eq_QG_eq.
Qed.

(* should be added in coq library ZArith *)

Theorem fold_Z_sub : ∀ a b, (a + - b = a - b)%Z.
Proof. easy. Qed.

Theorem Z_div_gcd_1 : ∀ a b c d,
  (0 < a * c → a * d = b * c → Z.gcd a b = 1 → Z.gcd c d = 1 → a = c)%Z.
Proof.
intros * Hacp Hadbc Hab Hcd.
specialize (Z.gauss a b c) as H1.
rewrite <- Hadbc in H1.
assert (H : Z.divide a (a * d)) by (exists d; apply Z.mul_comm).
specialize (H1 H Hab); clear H.
specialize (Z.gauss c d a) as H2.
rewrite Z.mul_comm, Hadbc in H2.
assert (H : Z.divide c (b * c)) by now exists b.
specialize (H2 H Hcd); clear H.
apply Z.divide_antisym in H1; [ | easy ].
destruct H1 as [H1| H1]; [ easy | ].
rewrite H1 in Hacp.
rewrite Z.mul_opp_r in Hacp.
exfalso; apply Z.nle_gt in Hacp; apply Hacp.
apply Z.opp_nonpos_nonneg.
apply Z.square_nonneg.
Qed.

Theorem Z_div_gcd : ∀ a b c d : Z,
  (0 < a)%Z
  → (0 < b)%Z
  → (0 < c)%Z
  → (0 < d)%Z
  → (a * d)%Z = (b * c)%Z
  → (a / Z.gcd a b)%Z = (c / Z.gcd c d)%Z.
Proof.
intros * Hap Hbp Hcp Hdp Hadbc.
remember (Z.gcd a b) as gab eqn:Hgab.
remember (Z.gcd c d) as gcd eqn:Hgcd.
assert (Hgabz : gab ≠ 0%Z). {
  intros H; subst gab.
  apply Z.gcd_eq_0 in H.
  now destruct H; subst a; apply Z.lt_irrefl in Hap.
}
assert (Hgcdz : gcd ≠ 0%Z). {
  intros H; subst gcd.
  apply Z.gcd_eq_0 in H.
  now destruct H; subst c; apply Z.lt_irrefl in Hcp.
}
apply Z_div_gcd_1 with (b := (b / gab)%Z) (d := (d / gcd)%Z); cycle 2. {
  now apply Z.gcd_div_gcd.
} {
  now apply Z.gcd_div_gcd.
} {
  apply Z.mul_pos_pos. {
    apply Z.div_str_pos.
    split. {
      specialize (Z.lt_total 0 gab) as H1.
      destruct H1 as [H1| H1]; [ easy | ].
      destruct H1 as [H1| H1]; [ now symmetry in H1 | ].
      apply Z.nle_gt in H1; exfalso; apply H1.
      rewrite Hgab.
      apply Z.gcd_nonneg.
    } {
      rewrite Hgab.
      destruct a as [| a| a]; [ easy | | easy ].
      destruct b as [| b| b]; [ easy | | easy ].
      rewrite <- Pos2Z.inj_gcd.
      apply Pos2Z.pos_le_pos.
      apply Pos_gcd_le_l.
    }
  } {
    apply Z.div_str_pos.
    split. {
      specialize (Z.lt_total 0 gcd) as H1.
      destruct H1 as [H1| H1]; [ easy | ].
      destruct H1 as [H1| H1]; [ now symmetry in H1 | ].
      apply Z.nle_gt in H1; exfalso; apply H1.
      rewrite Hgcd.
      apply Z.gcd_nonneg.
    } {
      rewrite Hgcd.
      destruct c as [| c| c]; [ easy | | easy ].
      destruct d as [| d| d]; [ easy | | easy ].
      rewrite <- Pos2Z.inj_gcd.
      apply Pos2Z.pos_le_pos.
      apply Pos_gcd_le_l.
    }
  }
}
rewrite <- Z.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgcd.
  apply Z.gcd_divide_r.
}
rewrite <- Z.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgcd.
  apply Z.gcd_divide_l.
}
f_equal.
rewrite Z.mul_comm.
rewrite <- Z.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgab.
  apply Z.gcd_divide_l.
}
rewrite (Z.mul_comm _ c).
rewrite <- Z.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgab.
  apply Z.gcd_divide_r.
}
f_equal.
rewrite Z.mul_comm, Hadbc.
apply Z.mul_comm.
Qed.

From Stdlib Require Import Psatz.

(* I don't understand why the proof of that is so complicated *)
Theorem qeq_eq : ∀ q1 q2,
  Z.gcd (Qnum q1) (QDen q1) = 1%Z
  → Z.gcd (Qnum q2) (QDen q2) = 1%Z
  → q1 == q2
  → q1 = q2.
Proof.
intros * Hq1 Hq2 Hq.
progress unfold "==" in Hq.
destruct (Z.eq_dec (Qnum q1) 0) as [Hqz1| Hqz1]. {
  rewrite Hqz1 in Hq1; cbn in Hq1.
  rewrite Hqz1, Z.mul_0_l in Hq.
  symmetry in Hq.
  apply Z.mul_eq_0 in Hq.
  destruct Hq as [Hqz2| Hqz2]; [ | easy ].
  rewrite Hqz2 in Hq2; cbn in Hq2.
  destruct q1 as (qn1, qd1).
  destruct q2 as (qn2, qd2).
  cbn in *.
  subst qn1 qn2.
  apply Pos2Z.inj in Hq1, Hq2.
  now rewrite Hq1, Hq2.
}
assert (H1 : (0 < Qnum q1 * Qnum q2)%Z). {
  destruct (Z_dec' 0 (Qnum q1)) as [[H1| H1]| H1]. {
    rewrite <- (Z.mul_0_l (Qnum q2)).
    apply Z.mul_lt_mono_pos_r; [ | easy ].
    lia.
  } {
    rewrite <- (Z.mul_0_l (Qnum q2)).
    apply Z.mul_lt_mono_neg_r; [ | easy ].
    lia.
  } {
    now symmetry in H1.
  }
}
rewrite (Z.mul_comm (Qnum q2)) in Hq.
specialize (Z_div_gcd_1 (Qnum q1) (QDen q1) (Qnum q2) (QDen q2)) as H2.
specialize (H2 H1 Hq Hq1 Hq2).
destruct q1 as (qn1, qd1).
destruct q2 as (qn2, qd2).
cbn in Hq1, Hq2, Hqz1, H1, H2.
subst qn2.
f_equal.
rewrite (Z.mul_comm (QDen _)) in Hq.
cbn in Hq.
apply Z.mul_reg_l in Hq; [ | easy ].
now apply Pos2Z.inj in Hq.
Qed.

Theorem qeq_QG_eq : ∀ q1 q2 : QG, q1 = q2 ↔ qg_q q1 == qg_q q2.
Proof.
intros.
split; intros Hq; [ now subst q2 | ].
destruct q1 as (q1, Hq1).
destruct q2 as (q2, Hq2).
cbn in Hq.
move q2 before q1.
apply eq_QG_eq; cbn.
apply Z_pos_gcd_eq_1 in Hq1, Hq2.
now apply qeq_eq.
Qed.

Theorem qlt_QG_lt: ∀ q1 q2 : QG, (q1 < q2)%QG ↔ (qg_q q1 < qg_q q2)%Q.
Proof.
intros.
destruct q1 as (q1, Hq1).
destruct q2 as (q2, Hq2).
cbn.
progress unfold QG_lt.
progress unfold QG_leb.
cbn.
split; intros Hqq. {
  apply Qnot_le_lt.
  intros H.
  apply Bool.not_true_iff_false in Hqq.
  apply Hqq; clear Hqq.
  now apply Qle_bool_iff.
} {
  apply Bool.not_true_iff_false.
  intros H.
  apply Qlt_not_le in Hqq.
  apply Hqq; clear Hqq.
  now apply Qle_bool_iff.
}
Qed.

Theorem Z_le_0_div_nonneg_r :
  ∀ x y, (0 < y → 0 ≤ x / y ↔ 0 ≤ x)%Z.
Proof.
intros * Hy.
progress unfold Z.div.
specialize (Zdiv.Z_div_mod x y) as H1.
apply Z.lt_gt in Hy.
specialize (H1 Hy).
apply Z.gt_lt in Hy.
remember (Z.div_eucl x y) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (q, r); cbn.
destruct H1 as (Hq, Hr).
clear Hqr.
subst x.
split. {
  intros Hq.
  apply Z.add_nonneg_nonneg; [ | easy ].
  apply Z.mul_nonneg_nonneg; [ | easy ].
  now apply Z.lt_le_incl.
} {
  intros Hyqr.
  apply Z.le_sub_le_add_l in Hyqr.
  rewrite Z.sub_0_l in Hyqr.
  rewrite <- Z.mul_opp_r in Hyqr.
  apply Z.nlt_ge.
  intros Hq.
  apply Z.opp_lt_mono in Hq.
  rewrite Z.opp_0 in Hq.
  remember (- q)%Z as x.
  clear q Heqx.
  move x after y.
  move r before y.
  destruct Hr as (Hrz, Hry).
  assert (H1 : (y * x < y)%Z) by now apply (Z.le_lt_trans _ r).
  rewrite <- Z.mul_1_r in H1.
  apply Z.mul_lt_mono_pos_l in H1; [ | easy ].
  destruct x as [| x| x]; [ easy | | easy ].
  now destruct x.
}
Qed.

(* end of should be added in coq library ZArith *)

Theorem Q_num_den_div_gcd :
  ∀ x y,
  x / Z.gcd x (Z.pos y) # Z.to_pos (Z.pos y / Z.gcd x (Z.pos y)) == x # y.
Proof.
intros.
progress unfold "=="; cbn.
remember (Z.pos y) as z.
assert (Hzz : (0 < z)%Z) by now subst z.
clear y Heqz; rename z into y.
rewrite Z2Pos.id. 2: {
  specialize (Z.gcd_divide_r x y) as H1.
  destruct H1 as (k, Hk).
  rewrite Hk at 1.
  rewrite Z.div_mul. 2: {
    intros H.
    apply Z.gcd_eq_0 in H.
    now destruct H; subst.
  }
  destruct k as [| k| k]; [ | easy | ]. {
    now cbn in Hk; subst y.
  } {
    exfalso; apply Z.nle_gt in Hzz; apply Hzz; clear Hzz.
    rewrite Hk; clear Hk.
    specialize (Z.gcd_nonneg x y) as H1.
    now destruct (Z.gcd x y).
  }
}
rewrite Z.mul_comm.
rewrite <- Z.divide_div_mul_exact; cycle 1. {
  intros H.
  apply Z.gcd_eq_0 in H.
  now destruct H; subst.
} {
  apply Z.gcd_divide_l.
}
rewrite <- Z.divide_div_mul_exact; cycle 1. {
  intros H.
  apply Z.gcd_eq_0 in H.
  now destruct H; subst.
} {
  apply Z.gcd_divide_r.
}
now rewrite Z.mul_comm.
Qed.

Global Instance GQ_of_eq_morph : Proper (Qeq ==> eq) QG_of_Q.
Proof.
intros (xn, xd) (yn, yd) Hxy.
apply eq_QG_eq.
cbn - [ Qred ].
now apply Qred_eq_iff.
Qed.

Theorem QG_eq_dec : ∀ q1 q2 : QG, {q1 = q2} + {q1 ≠ q2}.
Proof.
intros (q1, Hq1) (q2, Hq2).
move q2 before q1.
specialize (Qeq_dec q1 q2) as H1.
destruct H1 as [H1| H1]; [ left | right ]. {
  apply eq_QG_eq; cbn.
  apply qeq_eq; [ | | easy ]. {
    unfold Z_pos_gcd in Hq1.
    destruct (Qnum q1) as [| n| n]. {
      now rewrite Hq1.
    } {
      now apply (f_equal Z.pos) in Hq1.
    } {
      now apply (f_equal Z.pos) in Hq1.
    }
  } {
    unfold Z_pos_gcd in Hq2.
    destruct (Qnum q2) as [| n| n]. {
      now rewrite Hq2.
    } {
      now apply (f_equal Z.pos) in Hq2.
    } {
      now apply (f_equal Z.pos) in Hq2.
    }
  }
}
intros H2.
apply H1; clear H1.
now injection H2; clear H2; intros; subst q2.
Qed.

Theorem Qred_idemp : ∀ q, Qred (Qred q) = Qred q.
Proof.
intros.
apply Qred_eq_iff.
apply Qred_correct.
Qed.

Theorem QG_of_Q_opp : ∀ a, QG_of_Q (- a) = (- QG_of_Q a)%QG.
Proof.
intros.
apply eq_QG_eq.
progress unfold QG_opp.
progress unfold QG_of_Q.
cbn - [ Qred ].
do 2 rewrite Qred_opp.
progress f_equal.
symmetry; apply Qred_idemp.
Qed.

Theorem QG_of_Q_add_idemp_l :
  ∀ a b, QG_of_Q (qg_q (QG_of_Q a) + b) = QG_of_Q (a + b).
Proof.
intros; cbn.
apply eq_QG_eq.
cbn - [ Qred ].
apply Qred_eq_iff.
apply Qplus_inj_r.
apply Qred_correct.
Qed.

Theorem QG_of_Q_add_idemp_r :
  ∀ a b, QG_of_Q (a + qg_q (QG_of_Q b)) = QG_of_Q (a + b).
Proof.
intros.
rewrite Qplus_comm.
rewrite (Qplus_comm a).
apply QG_of_Q_add_idemp_l.
Qed.

Theorem QG_of_Q_mul_idemp_l :
  ∀ a b, QG_of_Q (qg_q (QG_of_Q a) * b) = QG_of_Q (a * b).
Proof.
intros; cbn.
apply eq_QG_eq.
cbn - [ Qred ].
apply Qred_eq_iff.
destruct (Qeq_dec b 0) as [Hbz| Hbz]. {
  rewrite Hbz.
  now do 2 rewrite Qmult_0_r.
}
apply Qmult_inj_r; [ easy | ].
apply Qred_correct.
Qed.

Theorem QG_of_Q_mul_idemp_r :
  ∀ a b, QG_of_Q (a * qg_q (QG_of_Q b)) = QG_of_Q (a * b).
intros.
rewrite Qmult_comm.
rewrite (Qmult_comm a).
apply QG_of_Q_mul_idemp_l.
Qed.

Theorem Z_gcd_eq_1_Qred :
  ∀ q,
  Z.gcd (Qnum q) (Z.pos (Qden q)) = 1%Z
  → Qred q = q.
Proof.
intros * Hq.
destruct q as (n, d).
cbn in Hq.
(**)
cbn.
remember (Z.ggcd n (Z.pos d)) as g eqn:Hg; symmetry in Hg.
destruct g as (g, (r1, r2)); cbn.
apply Z_ggcd_split in Hg.
destruct Hg as (Hn & Hd & Hg & Hg1).
subst n.
rewrite Hg in Hq; subst g.
rewrite Z.mul_1_l in Hd |-*.
now subst r2.
Qed.

Theorem QG_of_Q_qg_q : ∀ a, QG_of_Q (qg_q a) = a.
Proof.
intros.
apply eq_QG_eq.
destruct a as ((n, d), ap); cbn - [ Qred ].
apply Z_pos_gcd_eq_1 in ap.
now apply Z_gcd_eq_1_Qred.
Qed.

(* *)

Theorem QG_add_comm : ∀ a b : QG, (a + b)%QG = (b + a)%QG.
Proof.
intros.
progress unfold QG_add.
now rewrite Qplus_comm.
Qed.

Theorem QG_add_assoc : ∀ a b c : QG, (a + (b + c))%QG = (a + b + c)%QG.
Proof.
intros.
progress unfold QG_add.
rewrite QG_of_Q_add_idemp_r.
rewrite QG_of_Q_add_idemp_l.
now rewrite Qplus_assoc.
Qed.

Theorem QG_add_0_l : ∀ a : QG, (0 + a)%QG = a.
Proof.
intros.
progress unfold QG_add.
rewrite Qplus_0_l.
apply QG_of_Q_qg_q.
Qed.

Theorem QG_add_0_r : ∀ a : QG, (a + 0)%QG = a.
Proof.
intros.
rewrite QG_add_comm.
apply QG_add_0_l.
Qed.

Theorem QG_add_opp_diag_l : ∀ a : QG, (- a + a)%QG = 0%QG.
Proof.
intros.
progress unfold QG_add, QG_opp.
rewrite Qplus_comm.
rewrite QG_of_Q_add_idemp_r.
now rewrite Qplus_opp_r.
Qed.

Theorem QG_add_opp_diag_r : ∀ a : QG, (a + - a)%QG = 0%QG.
Proof.
intros.
rewrite QG_add_comm.
apply QG_add_opp_diag_l.
Qed.

Theorem QG_mul_comm : ∀ a b : QG, (a * b)%QG = (b * a)%QG.
Proof.
intros.
progress unfold QG_mul.
now rewrite Qmult_comm.
Qed.

Theorem QG_mul_assoc : ∀ a b c : QG, (a * (b * c))%QG = (a * b * c)%QG.
Proof.
intros.
progress unfold QG_mul.
rewrite QG_of_Q_mul_idemp_r.
rewrite QG_of_Q_mul_idemp_l.
now rewrite Qmult_assoc.
Qed.

Theorem QG_mul_1_l : ∀ a : QG, (1 * a)%QG = a.
Proof.
intros.
progress unfold QG_mul.
rewrite Qmult_1_l.
apply QG_of_Q_qg_q.
Qed.

Theorem QG_mul_1_r : ∀ a : QG, (a * 1)%QG = a.
Proof.
intros.
rewrite QG_mul_comm.
apply QG_mul_1_l.
Qed.

Theorem QG_mul_inv_diag_l : ∀ a : QG, a ≠ 0%QG → (a⁻¹ * a)%QG = 1%QG.
Proof.
intros * Haz.
progress unfold QG_mul.
progress unfold QG_inv.
rewrite Qmult_comm.
rewrite QG_of_Q_mul_idemp_r.
rewrite Qmult_inv_r; [ easy | ].
intros H1.
apply Haz; clear Haz.
rewrite <- (QG_of_Q_qg_q a).
rewrite <- QG_of_Q_qg_q.
now rewrite H1.
Qed.

Theorem QG_mul_inv_diag_r : ∀ a : QG, a ≠ 0%QG → (a * a⁻¹)%QG = 1%QG.
Proof.
intros * Haz.
rewrite QG_mul_comm.
now apply QG_mul_inv_diag_l.
Qed.

Theorem QG_mul_add_distr_l :  ∀ a b c, (a * (b + c))%QG = (a * b + a * c)%QG.
Proof.
intros.
progress unfold QG_mul.
progress unfold QG_add.
rewrite QG_of_Q_mul_idemp_r.
rewrite QG_of_Q_add_idemp_l.
rewrite QG_of_Q_add_idemp_r.
now rewrite Qmult_plus_distr_r.
Qed.

Theorem QG_mul_add_distr_r :  ∀ a b c, ((a + b) * c)%QG = (a * c + b * c)%QG.
Proof.
intros.
do 3 rewrite (QG_mul_comm _ c).
apply QG_mul_add_distr_l.
Qed.

Theorem QG_eqb_eq : ∀ a b : QG, (a =? b)%QG = true ↔ a = b.
Proof.
intros.
split; intros Hab. {
  apply Qeq_bool_iff in Hab.
  rewrite <- (QG_of_Q_qg_q a).
  rewrite <- (QG_of_Q_qg_q b).
  now rewrite Hab.
} {
  subst b.
  now apply Qeq_bool_iff.
}
Qed.

Theorem QG_le_dec : ∀ a b : QG, {(a ≤ b)%QG} + {¬ (a ≤ b)%QG}.
Proof.
intros.
unfold QG_le.
apply Bool.bool_dec.
Qed.

Theorem QG_le_refl : ∀ a : QG, (a ≤ a)%QG.
Proof.
intros.
apply Qle_bool_iff.
apply Qle_refl.
Qed.

Theorem QG_le_antisymm : ∀ a b : QG, (a ≤ b → b ≤ a → a = b)%QG.
Proof.
intros * Hab Hba.
apply Qle_bool_iff in Hab, Hba.
apply Qle_antisym in Hab; [ | easy ].
rewrite <- QG_of_Q_qg_q.
rewrite <- (QG_of_Q_qg_q a).
now rewrite Hab.
Qed.

Theorem QG_le_trans : ∀ x y z : QG, (x ≤ y → y ≤ z → x ≤ z)%QG.
Proof.
intros * Hxy Hyz.
apply Qle_bool_iff in Hxy, Hyz.
apply Qle_bool_iff.
now apply (Qle_trans _ (qg_q y)).
Qed.

Theorem QG_lt_le_incl : ∀ a b, (a < b → a ≤ b)%QG.
Proof.
intros * Hab.
apply Qle_bool_iff.
apply Qnot_lt_le; intros H1.
apply Bool.not_true_iff_false in Hab.
apply Hab.
apply Qle_bool_iff.
now apply Qlt_le_weak.
Qed.

Theorem QG_lt_irrefl : ∀ a, ¬ (a < a)%QG.
Proof.
intros * Ha.
apply Bool.not_true_iff_false in Ha.
apply Ha.
apply QG_le_refl.
Qed.

Theorem QG_lt_iff : ∀ a b, (a < b ↔ a ≤ b ∧ a ≠ b)%QG.
Proof.
intros.
split. {
  intros Hab.
  split; [ now apply QG_lt_le_incl | ].
  intros H; subst b; revert Hab.
  apply QG_lt_irrefl.
} {
  intros (H1, H2).
  apply Bool.not_true_iff_false.
  intros H3; apply H2.
  now apply QG_le_antisymm.
}
Qed.

Theorem QG_lt_trans : ∀ x y z : QG, (x < y → y < z → x < z)%QG.
Proof.
intros * Hxy Hyz.
apply QG_lt_iff in Hxy, Hyz.
apply QG_lt_iff.
destruct Hxy as (Hxy, Hnxy).
destruct Hyz as (Hyz, Hnyz).
split; [ apply (QG_le_trans Hxy Hyz) | ].
intros H; subst z.
now apply QG_le_antisymm in Hyz.
Qed.

Theorem QG_le_lt_trans : ∀ x y z : QG, (x ≤ y → y < z → x < z)%QG.
Proof.
intros * Hxy Hyz.
apply QG_lt_iff in Hyz.
apply QG_lt_iff.
destruct Hyz as (Hyz, Hnyz).
split; [ apply (QG_le_trans Hxy Hyz) | ].
intros H; subst z.
apply not_eq_sym in Hnyz.
now apply QG_le_antisymm in Hyz.
Qed.

Theorem QG_lt_le_trans : ∀ x y z : QG, (x < y → y ≤ z → x < z)%QG.
Proof.
intros * Hxy Hyz.
apply QG_lt_iff in Hxy.
apply QG_lt_iff.
destruct Hxy as (Hxy, Hnxy).
split; [ apply (QG_le_trans Hxy Hyz) | ].
intros H; subst z.
now apply QG_le_antisymm in Hyz.
Qed.

Theorem QG_le_0_sub : ∀ x y : QG, (0 ≤ y - x)%QG ↔ (x ≤ y)%QG.
Proof.
intros.
split; intros Hxy. {
  destruct x as (x, xp).
  destruct y as (y, yp).
  cbn.
  cbn in Hxy.
  progress unfold QG_sub in Hxy.
  progress unfold QG_opp in Hxy.
  cbn in Hxy.
  progress unfold QG_add in Hxy.
  apply Qle_bool_iff; cbn.
  cbn - [ QG_of_Q ] in Hxy.
  rewrite QG_of_Q_add_idemp_r in Hxy.
  apply Qle_minus_iff.
  remember (y + - x) as yx eqn:Hyx.
  clear - Hxy.
  rename yx into x; rename Hxy into Hx.
  apply Qle_bool_iff in Hx.
  remember (qg_q 0%QG) as y.
  cbn in Heqy; subst y.
  progress unfold Qle in Hx |-*.
  cbn in Hx |-*.
  rewrite Z.mul_1_r in Hx |-*.
  destruct x as (xn, xd).
  cbn - [ Qred ] in Hx |-*.
  destruct xn as [| xn| xn]; [ easy | easy | ].
  cbn in Hx.
  remember (Pos.ggcd xn xd) as g eqn:Hg.
  symmetry in Hg.
  now destruct g as (g, (r1, r2)).
} {
  destruct x as (x, xp).
  destruct y as (y, yp).
  progress unfold QG_sub.
  progress unfold QG_opp.
  cbn.
  progress unfold QG_add.
  apply Qle_bool_iff in Hxy; cbn in Hxy.
  cbn - [ QG_of_Q ].
  rewrite QG_of_Q_add_idemp_r.
  apply Qle_minus_iff in Hxy.
  remember (y + - x) as yx eqn:Hyx.
  clear - Hxy.
  rename yx into x; rename Hxy into Hx.
  apply Qle_bool_iff.
  remember (qg_q 0%QG) as y.
  cbn in Heqy; subst y.
  progress unfold Qle in Hx |-*.
  cbn in Hx |-*.
  rewrite Z.mul_1_r in Hx |-*.
  destruct x as (xn, xd).
  destruct xn as [| xn| xn]; [ easy | | easy ].
  cbn.
  remember (Pos.ggcd xn xd) as g eqn:Hg.
  symmetry in Hg.
  now destruct g as (g, (r1, r2)).
}
Qed.

Theorem qg_q_opp : ∀ a, qg_q (- a)%QG = - qg_q a.
Proof.
intros.
destruct a as (a, Hap).
cbn - [ Qred ].
rewrite Qred_opp.
progress f_equal.
apply Z_pos_gcd_eq_1 in Hap.
now apply Z_gcd_eq_1_Qred.
Qed.

Theorem QG_opp_add_distr : ∀ a b, (- (a + b) = - a - b)%QG.
Proof.
intros.
progress unfold QG_sub.
progress unfold QG_opp.
progress unfold QG_add.
rewrite QG_of_Q_opp.
rewrite QG_of_Q_qg_q, QG_of_Q_opp.
rewrite QG_of_Q_qg_q, QG_of_Q_opp.
rewrite QG_of_Q_qg_q.
do 2 rewrite qg_q_opp.
rewrite <- Qopp_plus.
symmetry; apply QG_of_Q_opp.
Qed.

Theorem fold_QG_sub : ∀ a b, (a + - b = a - b)%QG.
Proof. easy. Qed.

Theorem QG_add_le_mono_l : ∀ a b c : QG, (b ≤ c)%QG ↔ (a + b ≤ a + c)%QG.
Proof.
intros.
split; intros Hbc. {
  apply -> QG_le_0_sub.
  rewrite QG_add_comm.
  progress unfold QG_sub.
  rewrite QG_opp_add_distr.
  progress unfold QG_sub.
  rewrite QG_add_assoc.
  rewrite QG_add_comm.
  rewrite <- QG_add_assoc.
  rewrite QG_add_opp_diag_r.
  rewrite QG_add_0_r.
  rewrite QG_add_comm.
  now apply QG_le_0_sub.
} {
  apply QG_le_0_sub in Hbc.
  rewrite QG_add_comm in Hbc.
  progress unfold QG_sub in Hbc.
  rewrite QG_opp_add_distr in Hbc.
  progress unfold QG_sub in Hbc.
  rewrite QG_add_assoc in Hbc.
  rewrite QG_add_comm in Hbc.
  rewrite <- QG_add_assoc in Hbc.
  rewrite QG_add_opp_diag_r in Hbc.
  rewrite QG_add_0_r in Hbc.
  rewrite QG_add_comm in Hbc.
  now apply -> QG_le_0_sub in Hbc.
}
Qed.

Theorem QG_add_le_mono_r : ∀ a b c : QG, (a ≤ b)%QG ↔ (a + c ≤ b + c)%QG.
Proof.
intros.
do 2 rewrite (QG_add_comm _ c).
apply QG_add_le_mono_l.
Qed.

Theorem QG_add_le_compat : ∀ a b c d : QG, (a ≤ b → c ≤ d → a + c ≤ b + d)%QG.
Proof.
intros * Hab Hcd.
apply QG_le_trans with (y := (b + c)%QG). {
  now apply QG_add_le_mono_r.
} {
  now apply QG_add_le_mono_l.
}
Qed.

Theorem QG_opp_involutive: ∀ a : QG, (- - a)%QG = a.
Proof.
intros.
progress unfold QG_opp.
rewrite (QG_of_Q_opp (qg_q a)).
rewrite qg_q_opp.
rewrite Qopp_opp.
now do 2 rewrite QG_of_Q_qg_q.
Qed.

Theorem Z_pos_pos_gcd : ∀ a b, Z.pos (Z_pos_gcd a b) = Z.gcd a (Z.pos b).
Proof.
intros.
unfold Z_pos_gcd.
now destruct a.
Qed.

Theorem qg_q_add : ∀ a b, qg_q (a + b) == qg_q a + qg_q b.
Proof. intros; apply Qred_correct. Qed.

Theorem qg_q_mul : ∀ a b, qg_q (a * b) == qg_q a * qg_q b.
Proof. intros. apply Qred_correct. Qed.

Theorem QG_of_Q_qg_q_mul :
  ∀ a b : QG, QG_of_Q (qg_q a * qg_q b) = (a * b)%QG.
Proof.
intros.
rewrite <- QG_of_Q_qg_q.
rewrite qg_q_mul.
now rewrite <- QG_of_Q_mul_idemp_l.
Qed.

Theorem Q_mul_opp_l : ∀ n m : Q, (- n * m)%Q == (- (n * m))%Q.
Proof.
intros.
progress unfold "=="%Q; cbn.
f_equal.
apply Z.mul_opp_l.
Qed.

Theorem QG_mul_opp_l : ∀ a b : QG, (- a * b = - (a * b))%QG.
Proof.
intros.
rewrite <- QG_of_Q_qg_q; symmetry.
rewrite <- QG_of_Q_qg_q; symmetry.
rewrite <- QG_of_Q_qg_q_mul.
rewrite <- QG_of_Q_qg_q_mul.
rewrite <- QG_of_Q_opp.
rewrite QG_of_Q_qg_q.
rewrite QG_of_Q_qg_q.
rewrite qg_q_opp.
now rewrite Q_mul_opp_l.
Qed.

Theorem QG_mul_opp_r : ∀ a b : QG, (a * - b = - (a * b))%QG.
Proof.
intros.
do 2 rewrite (QG_mul_comm a).
apply QG_mul_opp_l.
Qed.

Theorem QG_mul_sub_distr_l :  ∀ a b c, (a * (b - c))%QG = (a * b - a * c)%QG.
Proof.
intros.
progress unfold QG_sub.
rewrite QG_mul_add_distr_l.
f_equal.
apply QG_mul_opp_r.
Qed.

Theorem QG_mul_sub_distr_r :  ∀ a b c, ((a - b) * c)%QG = (a * c - b * c)%QG.
Proof.
intros.
do 3 rewrite (QG_mul_comm _ c).
apply QG_mul_sub_distr_l.
Qed.

Theorem QG_div_sub_distr_r : ∀ a b c : QG, ((a - b) / c = a / c - b / c)%QG.
Proof.
intros.
apply QG_mul_sub_distr_r.
Qed.

Theorem QG_mul_nonneg_nonneg : ∀ a b : QG, (0 ≤ a → 0 ≤ b → 0 ≤ a * b)%QG.
Proof.
intros * Ha Hb.
apply Qle_bool_iff in Ha, Hb.
apply Qle_bool_iff.
cbn in Ha, Hb.
cbn - [ QG_mul ].
rewrite qg_q_mul.
now apply Qmult_le_0_compat.
Qed.

Theorem QG_mul_le_compat_nonneg :
  ∀ a b c d : QG, (0 ≤ a ≤ c → 0 ≤ b ≤ d → a * b ≤ c * d)%QG.
Proof.
intros * Hac Hbd.
apply QG_le_trans with (y := (c * b)%QG). {
  apply QG_le_0_sub.
  rewrite <- QG_mul_sub_distr_r.
  apply QG_mul_nonneg_nonneg; [ now apply QG_le_0_sub | easy ].
} {
  apply QG_le_0_sub.
  rewrite <- QG_mul_sub_distr_l.
  apply QG_mul_nonneg_nonneg; [ | now apply QG_le_0_sub ].
  eapply QG_le_trans; [ apply Hac | easy ].
}
Qed.

Theorem QG_opp_le_mono: ∀ a b : QG, (a ≤ b ↔ - b ≤ - a)%QG.
Proof.
intros.
split; intros Hab. {
  apply QG_le_0_sub.
  progress unfold QG_sub.
  rewrite QG_opp_involutive.
  rewrite QG_add_comm.
  rewrite fold_QG_sub.
  now apply <- QG_le_0_sub.
} {
  apply QG_le_0_sub in Hab.
  progress unfold QG_sub in Hab.
  rewrite QG_opp_involutive in Hab.
  rewrite QG_add_comm in Hab.
  rewrite fold_QG_sub in Hab.
  now apply -> QG_le_0_sub in Hab.
}
Qed.

Theorem QG_mul_le_compat_nonpos :
  ∀ a b c d : QG, (c ≤ a ≤ 0 → d ≤ b ≤ 0 → a * b ≤ c * d)%QG.
Proof.
intros * Hac Hbd.
assert (Hle : ∀ a b c, (c ≤ a ≤ 0 → b ≤ 0 → a * b ≤ c * b)%QG). {
  clear.
  intros * Hac Hbz.
  rewrite <- (QG_opp_involutive a).
  rewrite QG_mul_opp_l.
  rewrite <- (QG_opp_involutive c).
  rewrite (QG_mul_opp_l (- c))%QG.
  rewrite <- (QG_opp_involutive b).
  do 2 rewrite (QG_mul_opp_r _ (- b))%QG.
  do 2 rewrite QG_opp_involutive.
  apply QG_mul_le_compat_nonneg. {
    split. {
      apply QG_opp_le_mono.
      now rewrite QG_opp_involutive.
    } {
      now apply -> QG_opp_le_mono.
    }
  }
  split; [ | apply QG_le_refl ].
  apply QG_opp_le_mono.
  now rewrite QG_opp_involutive.
}
apply QG_le_trans with (y := (c * b)%QG). {
  now apply Hle.
} {
  do 2 rewrite (QG_mul_comm c).
  assert (Hcz : (c ≤ 0)%QG) by now apply QG_le_trans with (y := a).
  destruct Hac as (Hca, Haz).
  now apply Hle.
}
Qed.

Theorem QG_not_le : ∀ a b : QG, (¬ (a ≤ b) → a ≠ b ∧ b ≤ a)%QG.
Proof.
intros * Hab.
split. {
  intros H1; apply Hab; clear Hab; subst b.
  apply QG_le_refl.
}
apply Qle_bool_iff.
apply Qnot_lt_le.
intros H1.
apply Hab; clear Hab.
apply Qle_bool_iff.
now apply Qlt_le_weak.
Qed.

Theorem nat_of_inv_Q :
  ∀ n d,
  (Pos.to_nat d / Z.to_nat n =
     Z.to_nat (Qnum (/ (n # d))) / Pos.to_nat (Qden (/ (n # d))))%nat.
Proof.
intros.
destruct n as [| n| n]; [ easy | easy | cbn ].
symmetry; apply Nat.Div0.div_0_l.
Qed.

Theorem QG_add_sub : ∀ a b, (a + b - b)%QG = a.
Proof.
intros.
progress unfold QG_sub.
rewrite <- QG_add_assoc, QG_add_comm.
rewrite QG_add_opp_diag_r.
apply QG_add_0_l.
Qed.

Theorem QG_sub_add : ∀ a b, (a - b + b)%QG = a.
Proof.
intros.
progress unfold QG_sub.
rewrite <- QG_add_assoc.
rewrite QG_add_opp_diag_l.
apply QG_add_0_r.
Qed.

Theorem QG_characteristic_prop :
  ∀ i, List.fold_right QG_add 0%QG (List.repeat 1%QG (S i)) ≠ 0%QG.
Proof.
intros * H1.
assert (Hle : ∀ i, (0 ≤ List.fold_right QG_add 0 (List.repeat 1 i))%QG). {
  clear i H1; intros.
  induction i; cbn; [ easy | ].
  eapply QG_le_trans; [ apply IHi | ].
  apply QG_le_0_sub.
  now rewrite QG_add_sub.
}
specialize (Hle i).
apply (QG_add_le_mono_l 1%QG) in Hle.
rewrite QG_add_0_r in Hle.
cbn in H1.
now rewrite H1 in Hle.
Qed.

Theorem qg_q_mul_nat :
  ∀ a n,
  qg_q (List.fold_right QG_add 0%QG (List.repeat a n)) ==
  List.fold_right Qplus 0 (List.repeat (qg_q a) n).
Proof.
intros.
induction n; [ easy | ].
cbn - [ QG_add ].
rewrite qg_q_add.
now rewrite IHn.
Qed.

Theorem Q_mul_nat : ∀ a n,
  List.fold_right Qplus 0 (List.repeat a n) == a * (Z.of_nat n # 1).
Proof.
intros.
induction n; cbn; [ symmetry; apply Qmult_0_r | ].
rewrite IHn; clear IHn.
progress unfold "==".
cbn.
rewrite Pos.mul_1_r.
rewrite Pos2Z.inj_mul.
do 2 rewrite <- Z.mul_assoc.
rewrite <- Z.mul_add_distr_l.
rewrite <- Z.mul_assoc.
f_equal.
rewrite Z.mul_assoc.
f_equal.
rewrite <- (Z.mul_1_l (QDen a)) at 1.
rewrite <- Z.mul_add_distr_r.
f_equal.
rewrite Zpos_P_of_succ_nat.
apply Z.add_comm.
Qed.

Theorem List_fold_right_QG_add :
  ∀ a lb,
  List.fold_right QG_add a lb =
  QG_of_Q (List.fold_right Qplus (qg_q a) (List.map qg_q lb)).
Proof.
intros.
induction lb as [| b]; cbn. {
  symmetry; apply QG_of_Q_qg_q.
}
rewrite <- QG_of_Q_add_idemp_r.
rewrite <- IHlb.
rewrite <- qg_q_add.
now rewrite QG_of_Q_qg_q.
Qed.

Theorem Pos_ggcd_1_r : ∀ a , Pos.ggcd a 1 = (1, (a, 1))%positive.
Proof.
intros.
progress unfold Pos.ggcd.
cbn.
rewrite Nat.add_comm.
cbn.
now destruct a.
Qed.

Theorem Z_ggcd_1_r : ∀ a , Z.ggcd a 1 = (1%Z, (a, 1%Z)).
Proof.
intros.
destruct a as [| a| a]; [ easy | | ]. {
  now cbn; rewrite Pos_ggcd_1_r.
} {
  now cbn; rewrite Pos_ggcd_1_r.
}
Qed.

Theorem Qred_1_r : ∀ a, Qred (a # 1) = a # 1.
Proof.
intros.
now cbn; rewrite Z_ggcd_1_r.
Qed.

Theorem QG_of_Z_add :
  ∀ a b, QG_of_Z (a + b) = (QG_of_Z a + QG_of_Z b)%QG.
Proof.
intros.
progress unfold QG_of_Z.
apply eq_QG_eq; cbn - [ Qred ].
do 3 rewrite Qred_1_r.
cbn.
do 2 rewrite Z.mul_1_r.
now rewrite Z_ggcd_1_r.
Qed.

Theorem QG_nle_gt : ∀ a b : QG, ¬ (a ≤ b)%QG ↔ (b < a)%QG.
Proof.
intros.
split. {
  intros Hab.
  apply QG_lt_iff.
  apply QG_not_le in Hab.
  split; [ easy | ].
  now apply not_eq_sym.
} {
  intros Hba Hab.
  apply QG_lt_iff in Hba.
  destruct Hba as (Hba, H).
  apply H; clear H.
  now apply QG_le_antisymm.
}
Qed.

Theorem QG_of_Z_QG_of_Q : ∀ a, QG_of_Z a = QG_of_Q (a # 1).
Proof. easy. Qed.

Theorem QG_of_Z_Z_of_QG_interv :
  ∀ a : QG, (QG_of_Z (Z_of_QG a) ≤ a < QG_of_Z (Z_of_QG a) + 1)%QG.
Proof.
intros.
destruct a as ((an, ap), Hap).
cbn in Hap.
split. {
  apply Qle_bool_iff; cbn.
  progress unfold Z_of_QG; cbn.
  rewrite Z_ggcd_1_r.
  cbn.
  apply Z_pos_gcd_eq_1 in Hap.
  progress unfold Qle.
  cbn.
  rewrite Z.mul_1_r.
  rewrite Z.mul_comm.
  now apply Z.mul_div_le.
}
apply QG_lt_iff.
split. {
  apply Qle_bool_iff; cbn.
  progress unfold Z_of_QG; cbn.
  do 2 rewrite Z_ggcd_1_r.
  cbn.
  rewrite Z.mul_1_r.
  progress unfold Qle.
  cbn.
  rewrite Z.mul_1_r.
  rewrite Z.mul_add_distr_r.
  rewrite Z.mul_1_l.
  rewrite Z.mul_comm.
  rewrite (Z.div_mod an (Z.pos ap)) at 1; [ | easy ].
  apply Z.add_le_mono_l.
  apply Z.lt_le_incl.
  now apply Z.mod_pos_bound.
}
apply neq_QG_neq.
progress unfold qg_q at 1.
progress unfold Z_of_QG.
cbn.
do 2 rewrite Z_ggcd_1_r.
cbn.
rewrite Z.mul_1_r.
intros H1.
injection H1; clear H1; intros H1 H2.
rewrite H1, Z.div_1_r in H2.
rewrite Z.add_1_r in H2.
revert H2.
apply Z.neq_succ_diag_r.
Qed.

Theorem QG_of_Z_Z_of_QG_interv' :
  ∀ a : QG, (a - 1 < QG_of_Z (Z_of_QG a) ≤ a)%QG.
Proof.
intros.
specialize (QG_of_Z_Z_of_QG_interv a) as H1.
split; [ | apply H1 ].
apply QG_lt_iff.
split. {
  apply QG_add_le_mono_r with (c := 1%QG).
  rewrite QG_sub_add.
  now apply QG_lt_le_incl.
}
intros H2.
apply (f_equal (QG_add 1%QG)) in H2.
rewrite QG_add_comm, QG_sub_add in H2.
rewrite QG_add_comm in H2.
rewrite <- H2 in H1.
destruct H1 as (_, H1).
revert H1.
apply QG_lt_irrefl.
Qed.

Theorem QG_mul_cancel_l :
  ∀ a b c : QG, a ≠ 0%QG → (a * b)%QG = (a * c)%QG ↔ b = c.
Proof.
intros * Haz.
split; intros Hbc; [ | now subst c ].
apply (f_equal (λ b, QG_div b a)) in Hbc.
do 2 rewrite (QG_mul_comm a) in Hbc.
progress unfold QG_div in Hbc.
do 2 rewrite <- QG_mul_assoc in Hbc.
rewrite QG_mul_inv_diag_r in Hbc; [ | easy ].
now do 2 rewrite QG_mul_1_r in Hbc.
Qed.

Theorem QG_mul_lt_mono_pos_l :
  ∀ a b c : QG, (0 < a)%QG → (b < c)%QG ↔ (a * b < a * c)%QG.
Proof.
intros * Ha.
split; intros Hbc. {
  apply QG_lt_iff in Ha, Hbc.
  apply QG_lt_iff.
  destruct Ha as (Ha, Haz); apply not_eq_sym in Haz.
  destruct Hbc as (Hbc, Hbcz).
  apply Qle_bool_iff in Ha, Hbc.
  apply neq_QG_neq in Haz, Hbcz.
  cbn in Ha, Haz.
  split. {
    apply Qle_bool_iff.
    do 2 rewrite qg_q_mul.
    apply Qmult_le_l; [ | easy ].
    apply Qnot_le_lt.
    intros H1; apply Haz; clear Haz.
    apply Qle_antisym in Ha; [ | easy ].
    destruct a as ((an, ad), Hap).
    cbn in Hap, Ha, H1 |-*.
    progress unfold "==" in Ha.
    cbn in Ha.
    rewrite Z.mul_1_r in Ha.
    subst an.
    rewrite Z_pos_gcd_Z_gcd in Hap.
    rewrite Z.gcd_0_l in Hap.
    now cbn in Hap; subst ad.
  } {
    intros H1.
    apply QG_mul_cancel_l in H1; [ | now intros H2; subst a ].
    now subst c.
  }
}
apply QG_nle_gt in Hbc.
apply QG_nle_gt.
intros Hcb; apply Hbc; clear Hbc.
(*lemma?*)
apply QG_le_0_sub.
rewrite <- QG_mul_sub_distr_l.
apply QG_mul_nonneg_nonneg; [ now apply QG_lt_le_incl | ].
now apply QG_le_0_sub.
Qed.

Theorem QG_mul_lt_mono_pos_r :
  ∀ a b c : QG, (0 < c)%QG → (a < b)%QG ↔ (a * c < b * c)%QG.
Proof.
intros * Hc.
do 2 rewrite (QG_mul_comm _ c).
now apply QG_mul_lt_mono_pos_l.
Qed.

Theorem Qred_add_idemp_l :
  ∀ a b, Qred (Qred a + b) = Qred (a + b).
Proof.
intros.
apply Qred_complete.
apply Qplus_inj_r.
apply Qred_correct.
Qed.

Theorem Qred_add_idemp_r :
  ∀ a b, Qred (a + Qred b) = Qred (a + b).
Proof.
intros.
apply Qred_complete.
apply Qplus_inj_l.
apply Qred_correct.
Qed.

Theorem Qred_mul_idemp_l :
  ∀ a b, Qred (Qred a * b) = Qred (a * b).
Proof.
intros.
apply Qred_complete.
destruct (Qeq_dec b 0) as [Hbz| Hbz]. {
  now rewrite Hbz; do 2 rewrite Qmult_0_r.
}
apply Qmult_inj_r; [ easy | ].
apply Qred_correct.
Qed.

Theorem Qred_mul_idemp_r :
  ∀ a b, Qred (a * Qred b) = Qred (a * b).
Proof.
intros.
apply Qred_complete.
destruct (Qeq_dec a 0) as [Haz| Haz]; [ now rewrite Haz | ].
apply Qmult_inj_l; [ easy | ].
apply Qred_correct.
Qed.

Theorem Qnum_Qred_nonneg : ∀ a, (0 ≤ Qnum a → 0 ≤ Qnum (Qred a))%Z.
Proof.
intros * Hza.
destruct a as (an, ad).
cbn in Hza |-*.
remember (Z.ggcd an (Z.pos ad)) as g eqn:Hg.
symmetry in Hg.
destruct g as (g, (n, d)).
apply Z_ggcd_split in Hg.
destruct Hg as (Hn & Hd & Hg & Hg1).
cbn.
apply (Z.mul_le_mono_pos_l _ _ g). {
  apply Z.le_neq.
  split; [ rewrite <- Hg; apply Z.gcd_nonneg | ].
  now intros H; move H at top; subst g.
}
now rewrite Z.mul_0_r, <- Hn.
Qed.

Theorem QG_archimedean :
  ∀ a b : QG, (0 < a)%QG →
  ∃ n : nat,
  (b < List.fold_right QG_add 0 (List.repeat a n))%QG.
Proof.
intros * Ha *.
exists (Z.to_nat (Z_of_QG (b / a)) + 1)%nat.
rewrite List_fold_right_QG_add.
rewrite List.map_repeat.
rewrite Q_mul_nat.
rewrite Nat2Z.inj_add; cbn.
destruct (Qlt_le_dec 0 (qg_q b)) as [Hbz| Hbz]. 2: {
  apply QG_le_lt_trans with (y := 0%QG). {
    now apply Qle_bool_iff; cbn.
  }
  remember (Z.to_nat _) as x.
  apply QG_lt_iff.
  split. {
    apply Qle_bool_iff.
    cbn - [ Qred ].
    apply Qred_le.
    apply Z.mul_nonneg_nonneg; [ cbn | easy ].
    apply QG_lt_iff in Ha.
    destruct Ha as (Ha, Haz).
    apply Qle_bool_iff in Ha; cbn in Ha.
    progress unfold Qle in Ha.
    cbn in Ha.
    rewrite Z.mul_1_r in Ha.
    apply Z.mul_nonneg_nonneg; [ easy | ].
    apply Z.add_nonneg_nonneg; [ | easy ].
    apply Nat2Z.is_nonneg.
  } {
    intros H1; symmetry in H1.
    apply eq_QG_eq in H1; cbn - [ Qred ] in H1.
    apply Qred_eq_iff in H1.
    apply Qmult_integral_l in H1. {
      apply Qden_cancel in H1.
      apply Z.add_move_0_r in H1.
      cbn in H1.
      specialize (Nat2Z.is_nonneg x) as H2.
      now rewrite H1 in H2.
    }
    intros H.
    progress unfold QG_lt in Ha.
    apply Bool.not_true_iff_false in Ha.
    apply Ha; clear Ha.
    progress unfold QG_leb.
    now rewrite H.
  }
}
assert (Hb : (0 < b)%QG). {
  destruct b as ((bn, bd), Hb).
  cbn in Hbz.
  apply QG_lt_iff.
  split. {
    apply Qle_bool_iff; cbn.
    now apply Qlt_le_weak.
  }
  intros H.
  symmetry in H.
  apply qeq_QG_eq in H; cbn in H.
  now rewrite H in Hbz.
}
rename Hbz into Hzb.
rewrite Z2Nat.id. 2: {
  apply Z.div_pos; [ | easy ].
  cbn - [ Qred ].
  rewrite Qred_mul_idemp_r.
  replace (_ * / _) with (qg_q b / qg_q a) by easy.
  apply Qnum_Qred_nonneg.
  destruct a as (a, Hap).
  destruct b as (b, Hbp).
  move b before a.
  cbn - [ Qred ].
  apply qlt_QG_lt in Ha, Hb.
  cbn in Ha, Hb.
  clear Hzb.
  apply Z_pos_gcd_eq_1 in Hap, Hbp.
  destruct a as (an, ad).
  destruct b as (bn, bd).
  cbn in Hap, Hbp.
  cbn.
  progress unfold Qinv.
  cbn.
  destruct an as [| an| an]; [ easy | | easy ].
  destruct bn as [| bn| bn]; [ easy | | easy ].
  easy.
}
rewrite <- QG_of_Q_mul_idemp_r.
rewrite QG_of_Q_qg_q_mul.
rewrite fold_QG_of_Z.
rewrite QG_of_Z_add.
progress unfold QG_of_Z at 2; fold QG_1.
specialize (QG_of_Z_Z_of_QG_interv (b / a)%QG) as H1.
destruct H1 as (H1, H2).
apply (@QG_mul_lt_mono_pos_l a) in H2; [ | easy ].
progress unfold QG_div in H2 at 1.
rewrite (QG_mul_comm a) in H2.
rewrite <- QG_mul_assoc in H2.
rewrite QG_mul_inv_diag_l in H2. 2: {
  now intros H; subst a.
}
now rewrite QG_mul_1_r in H2.
Qed.

(* *)

Definition QG_num q := Qnum (qg_q q).
Definition QG_den q := Qden (qg_q q).

Theorem fold_QG_num : ∀ q, Qnum (qg_q q) = QG_num q.
Proof. easy. Qed.

Theorem fold_QG_den : ∀ q, Qden (qg_q q) = QG_den q.
Proof. easy. Qed.

(* *)

Definition QG_compare a b := Qcompare (qg_q a) (qg_q b).

Notation "a ?= b" := (QG_compare a b) : QG_scope.

Theorem QG_compare_refl : ∀ a, (a ?= a)%QG = Eq.
Proof.
intros.
apply Z.compare_refl.
Qed.

Theorem QG_compare_eq_iff : ∀ a b, (a ?= b)%QG = Eq ↔ a = b.
Proof.
intros.
progress unfold QG_compare.
split; intros Hab. {
  apply Qeq_alt in Hab.
  apply eq_QG_eq.
  apply qeq_eq; [ | | easy ]. {
    destruct a as (aq, Ha); cbn.
    cbn in Hab.
    apply (f_equal Z.pos) in Ha.
    now rewrite Z_pos_pos_gcd in Ha.
  } {
    destruct b as (bq, Hb); cbn.
    cbn in Hab.
    apply (f_equal Z.pos) in Hb.
    now rewrite Z_pos_pos_gcd in Hb.
  }
}
subst b.
apply Z.compare_refl.
Qed.

Theorem QG_compare_lt_iff : ∀ a b, (a ?= b)%QG = Lt ↔ (a < b)%QG.
Proof.
intros.
now split; intros Hab; apply Z.leb_gt.
Qed.

(* *)

Theorem QG_lt_0_neq_0 : ∀ a, (0 < a → a ≠ 0)%QG.
Proof.
intros a Ha H; subst a.
now apply QG_lt_irrefl in Ha.
Qed.

Theorem QG_sub_diag : ∀ a, (a - a = 0)%QG.
Proof. apply QG_add_opp_diag_r. Qed.

Theorem QG_sub_move_0_r : ∀ a b, (a - b = 0)%QG ↔ a = b.
Proof.
intros.
split; intros Hab. {
  apply (f_equal (QG_add b)) in Hab.
  rewrite QG_add_comm, QG_sub_add in Hab.
  now rewrite QG_add_0_r in Hab.
} {
  subst b.
  apply QG_sub_diag.
}
Qed.

Theorem QG_lt_0_sub : ∀ x y : QG, (0 < y - x)%QG ↔ (x < y)%QG.
Proof.
intros.
split; intros Hxy. {
  apply QG_lt_iff.
  split. {
    apply QG_lt_le_incl in Hxy.
    now apply QG_le_0_sub.
  }
  intros H; subst y.
  rewrite QG_sub_diag in Hxy.
  now apply QG_lt_irrefl in Hxy.
} {
  apply QG_lt_iff.
  split. {
    apply QG_lt_le_incl in Hxy.
    now apply QG_le_0_sub.
  }
  intros H; symmetry in H.
  apply -> QG_sub_move_0_r in H.
  subst y.
  now apply QG_lt_irrefl in Hxy.
}
Qed.

Theorem QG_add_move_l : ∀ a b c, (a + b)%QG = c ↔ b = (c - a)%QG.
Proof.
intros.
split; intros Hab; subst; rewrite QG_add_comm. {
  symmetry; apply QG_add_sub.
} {
  apply QG_sub_add.
}
Qed.

Theorem QG_sub_sub_swap : ∀ a b c, (a - b - c = a - c - b)%QG.
Proof.
intros.
progress unfold QG_sub.
do 2 rewrite <- QG_add_assoc.
progress f_equal.
apply QG_add_comm.
Qed.

Theorem QG_sub_opp_r : ∀ a b, (a - - b)%QG = (a + b)%QG.
Proof.
intros.
symmetry.
apply QG_add_move_l.
rewrite QG_sub_sub_swap.
rewrite QG_sub_diag.
progress unfold QG_sub.
rewrite QG_add_0_l.
symmetry; apply QG_opp_involutive.
Qed.

Theorem QG_opp_sub_distr : ∀ a b, (- (a - b))%QG = (- a + b)%QG.
Proof.
intros.
progress unfold QG_sub.
rewrite QG_opp_add_distr.
apply QG_sub_opp_r.
Qed.

(* *)

From Stdlib Require Import Ring.

Theorem QG_sub_def : ∀ x y : QG, (x - y = x + (- y))%QG.
Proof. easy. Qed.

Definition QG_ring_theory :=
  {| Radd_0_l := QG_add_0_l;
     Radd_comm := QG_add_comm;
     Radd_assoc := QG_add_assoc;
     Rmul_1_l := QG_mul_1_l;
     Rmul_comm := QG_mul_comm;
     Rmul_assoc := QG_mul_assoc;
     Rdistr_l := QG_mul_add_distr_r;
     Rsub_def := QG_sub_def;
     Ropp_def := QG_add_opp_diag_r |}.

Add Ring QG_ring : QG_ring_theory.

From Stdlib Require Import Field.

Theorem QG_1_neq_0 : (1 ≠ 0)%QG.
Proof. easy. Qed.

Theorem QG_Fdiv_def : ∀ p q : QG, (p / q = p * q⁻¹)%QG.
Proof. easy. Qed.

Theorem QG_Finv_l : ∀ p : QG, p ≠ 0%QG → (p⁻¹ * p)%QG = 1%QG.
Proof.
intros * Hpz.
now apply QG_mul_inv_diag_l.
Qed.

Definition QG_field_theory :=
  {| F_R := QG_ring_theory;
     F_1_neq_0 := QG_1_neq_0;
     Fdiv_def := QG_Fdiv_def;
     Finv_l := QG_Finv_l |}.

Add Field QG_field : QG_field_theory.
