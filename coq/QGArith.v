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

Theorem QG_of_Q_prop : ∀ q,
  let g := Z_pos_gcd (Qnum q) (Qden q) in
  Z_pos_gcd (Qnum (Qnum q / Z.pos g # Z.to_pos (QDen q / Z.pos g)))
    (Qden (Qnum q / Z.pos g # Z.to_pos (QDen q / Z.pos g))) = 1%positive.
Proof.
intros; cbn.
subst g; cbn.
progress unfold Z_pos_gcd.
remember (Qnum q) as qn eqn:Hqn; symmetry in Hqn.
destruct qn as [| qn| qn]. {
  now cbn; rewrite Z.div_same.
} {
  remember (Z.pos qn / _)%Z as z eqn:Hz; symmetry in Hz.
  destruct z as [| z| z]. {
    apply Z.div_small_iff in Hz; [ | easy ].
    destruct Hz as [(Hz1, Hz2)| Hz]; [ | easy ].
    exfalso.
    apply Z.nle_gt in Hz2; apply Hz2; clear Hz2.
    apply Pos2Z.pos_le_pos.
    apply Pos_gcd_le_l.
  } {
    apply Pos2Z.inj; cbn.
    rewrite Pos2Z.inj_gcd.
    rewrite <- Hz.
    rewrite Z2Pos.id. 2: {
      apply Z.div_str_pos.
      split; [ easy | ].
      apply Pos2Z.pos_le_pos.
      apply Pos_gcd_le_r.
    }
    now apply Z.gcd_div_gcd.
  } {
    specialize (Zdiv.Z_div_nonneg_nonneg) as H1.
    remember (Z.pos _) as x eqn:Hx in Hz.
    remember (Z.pos _) as y eqn:Hy in Hz.
    specialize (H1 x y).
    assert (H : (0 <= x)%Z) by now subst x.
    specialize (H1 H); clear H.
    assert (H : (0 <= y)%Z) by now subst y.
    specialize (H1 H); clear H.
    now rewrite Hz in H1.
  }
} {
  remember (Z.neg qn / _)%Z as z eqn:Hz; symmetry in Hz.
  destruct z as [| z| z]. {
    apply Z.div_small_iff in Hz; [ | easy ].
    now destruct Hz.
  } {
    apply Pos2Z.inj; cbn.
    rewrite Pos2Z.inj_gcd.
    rewrite <- Hz.
    rewrite Z2Pos.id. 2: {
      apply Z.div_str_pos.
      split; [ easy | ].
      apply Pos2Z.pos_le_pos.
      apply Pos_gcd_le_r.
    }
    now apply Z.gcd_div_gcd.
  } {
    apply (f_equal Z.opp) in Hz.
    cbn in Hz.
    rewrite <- Zdiv.Z_div_zero_opp_full in Hz. 2: {
      rewrite Pos2Z.inj_gcd.
      rewrite <- Z.gcd_opp_l.
      rewrite Pos2Z.opp_pos.
      apply Znumtheory.Zdivide_mod.
      apply Z.gcd_divide_l.
    }
    cbn in Hz.
    apply (f_equal Z.to_pos) in Hz.
    cbn in Hz.
    rewrite <- Hz.
    rewrite Pos2Z.inj_gcd.
    rewrite <- Z2Pos.inj_gcd; cycle 1. {
      apply Z.div_str_pos.
      split; [ easy | ].
      apply Znumtheory.Zdivide_le; [ easy | easy | ].
      apply Z.gcd_divide_l.
    } {
      apply Z.div_str_pos.
      split; [ easy | ].
      apply Znumtheory.Zdivide_le; [ easy | easy | ].
      apply Z.gcd_divide_r.
    }
    rewrite Z.gcd_div_factor; [ | easy | | ]; cycle 1. {
      apply Z.gcd_divide_l.
    } {
      apply Z.gcd_divide_r.
    }
    now rewrite Z.div_same.
  }
}
Qed.

Definition QG_of_Q (q : Q) :=
  let g := Z_pos_gcd (Qnum q) (Qden q) in
  mk_qg (Qmake (Qnum q / Zpos g) (Z.to_pos (Zpos (Qden q) / Zpos g)%Z))
    (QG_of_Q_prop q).

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
apply eq_QG_eq; cbn.
now rewrite (Z.div_same (Z.pos d)).
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

(* I don't understand why the proof of that too is so complicated *)
Theorem qeq_QG_eq : ∀ q1 q2 : QG, q1 = q2 ↔ qg_q q1 == qg_q q2.
Proof.
intros.
split; intros Hq; [ now subst q2 | ].
destruct q1 as (q1, Hq1).
destruct q2 as (q2, Hq2).
cbn in Hq.
move q2 before q1.
apply eq_QG_eq; cbn.
rewrite Z_pos_gcd_Z_gcd in Hq1, Hq2.
rewrite <- Z2Pos.inj_1 in Hq1, Hq2.
apply Z2Pos.inj in Hq1; [ | | easy ]. 2: {
  destruct (Z.eq_dec (Z.gcd (Qnum q1) (QDen q1)) 0) as [H1| H1]. {
    now apply Z.gcd_eq_0 in H1.
  }
  specialize (Z.gcd_nonneg (Qnum q1) (QDen q1)) as H2.
  apply Z.nle_gt.
  intros H3; apply H1.
  now apply Z.le_antisymm.
}
apply Z2Pos.inj in Hq2; [ | | easy ]. 2: {
  destruct (Z.eq_dec (Z.gcd (Qnum q2) (QDen q2)) 0) as [H1| H1]. {
    now apply Z.gcd_eq_0 in H1.
  }
  specialize (Z.gcd_nonneg (Qnum q2) (QDen q2)) as H2.
  apply Z.nle_gt.
  intros H3; apply H1.
  now apply Z.le_antisymm.
}
now apply qeq_eq.
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
apply eq_QG_eq; cbn.
f_equal. {
  progress unfold Z_pos_gcd.
  destruct xn as [| xn| xn]; [ now destruct yn | | ]. {
    destruct yn as [| yn| yn]; [ easy | | easy ].
    progress unfold Qeq in Hxy.
    cbn in Hxy.
    do 2 rewrite Pos2Z.inj_mul in Hxy.
    symmetry in Hxy; rewrite Z.mul_comm in Hxy.
    symmetry in Hxy.
    do 2 rewrite Pos2Z.inj_gcd.
    now apply Z_div_gcd.
  } {
    destruct yn as [| yn| yn]; [ easy | easy | ].
    progress unfold Qeq in Hxy.
    cbn in Hxy.
    injection Hxy; clear Hxy; intros Hxy.
    apply (f_equal Z.pos) in Hxy.
    do 2 rewrite Pos2Z.inj_mul in Hxy.
    symmetry in Hxy; rewrite Z.mul_comm in Hxy.
    symmetry in Hxy.
    do 2 rewrite Pos2Z.inj_gcd.
    do 2 rewrite <- Pos2Z.opp_pos.
    rewrite Z.div_opp_l_z; [ | easy | ]. 2: {
      apply Z.mod_divide; [ easy | ].
      apply Z.gcd_divide_l.
    }
    rewrite Z.div_opp_l_z; [ | easy | ]. 2: {
      apply Z.mod_divide; [ easy | ].
      apply Z.gcd_divide_l.
    }
    f_equal.
    now apply Z_div_gcd.
  }
} {
  progress unfold "==" in Hxy.
  cbn in Hxy.
  f_equal.
  progress unfold Z_pos_gcd.
  destruct xn as [| xn| xn]; cbn. {
    destruct yn as [| yn| yn]; cbn; [ | easy | easy ].
    rewrite Z.div_same; [ | easy ].
    rewrite Z.div_same; [ | easy ].
    easy.
  } {
    destruct yn as [| yn| yn]; cbn; [ easy | | easy ].
    do 2 rewrite Pos2Z.inj_gcd.
    rewrite Z.gcd_comm.
    rewrite (Z.gcd_comm (Z.pos yn)).
    symmetry in Hxy.
    rewrite Z.mul_comm in Hxy.
    now apply Z_div_gcd.
  } {
    destruct yn as [| yn| yn]; cbn; [ easy | easy | ].
    do 2 rewrite <- Pos2Z.opp_pos in Hxy.
    do 2 rewrite Z.mul_opp_l in Hxy.
    injection Hxy; clear Hxy; intros Hxy.
    apply (f_equal Z.pos) in Hxy.
    do 2 rewrite Pos2Z.inj_mul in Hxy.
    do 2 rewrite Pos2Z.inj_gcd.
    rewrite Z.gcd_comm.
    rewrite (Z.gcd_comm (Z.pos yn)).
    symmetry in Hxy.
    rewrite Z.mul_comm in Hxy.
    now apply Z_div_gcd.
  }
}
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

Theorem QG_of_Q_opp : ∀ a, QG_of_Q (- a) = (- QG_of_Q a)%QG.
Proof.
intros.
unfold QG_opp.
destruct a as (an, ad); cbn.
destruct an as [| an| an]. {
  unfold Qopp; cbn.
  rewrite QG_of_Q_0; symmetry.
  now rewrite QG_of_Q_0.
} {
  cbn.
  rewrite Pos2Z.inj_gcd.
  now rewrite Q_num_den_div_gcd.
} {
  cbn.
  rewrite Pos2Z.inj_gcd.
  rewrite <- Z.gcd_opp_l.
  now rewrite Q_num_den_div_gcd.
}
Qed.

Theorem QG_of_Q_add_idemp_l :
  ∀ a b, QG_of_Q (qg_q (QG_of_Q a) + b) = QG_of_Q (a + b).
Proof.
intros; cbn.
destruct a as (an, ad).
destruct b as (bn, bd).
cbn.
progress unfold Z_pos_gcd.
destruct an as [| an| an]; cbn. {
  rewrite Z.div_same; [ cbn | easy ].
  rewrite Qplus_0_l.
  progress unfold "+"%Q; cbn.
  rewrite Z.mul_comm.
  now rewrite Qreduce_l.
} {
  rewrite Pos2Z.inj_gcd.
  now rewrite Q_num_den_div_gcd.
} {
  rewrite Pos2Z.inj_gcd.
  rewrite <- Z.gcd_opp_l.
  now rewrite Q_num_den_div_gcd.
}
Qed.

Theorem QG_of_Q_add_idemp_r :
  ∀ a b, QG_of_Q (a + qg_q (QG_of_Q b)) = QG_of_Q (a + b).
intros.
rewrite Qplus_comm.
rewrite (Qplus_comm a).
apply QG_of_Q_add_idemp_l.
Qed.

Theorem QG_of_Q_mul_idemp_l :
  ∀ a b, QG_of_Q (qg_q (QG_of_Q a) * b) = QG_of_Q (a * b).
Proof.
intros.
intros; cbn.
destruct a as (an, ad).
destruct b as (bn, bd).
cbn.
progress unfold Z_pos_gcd.
destruct an as [| an| an]; cbn. {
  rewrite Z.div_same; [ cbn | easy ].
  rewrite Qmult_0_l.
  progress unfold "*"%Q; cbn.
  symmetry.
  now rewrite Qreduce_zero.
} {
  rewrite Pos2Z.inj_gcd.
  now rewrite Q_num_den_div_gcd.
} {
  rewrite Pos2Z.inj_gcd.
  rewrite <- Z.gcd_opp_l.
  now rewrite Q_num_den_div_gcd.
}
Qed.

Theorem QG_of_Q_mul_idemp_r :
  ∀ a b, QG_of_Q (a * qg_q (QG_of_Q b)) = QG_of_Q (a * b).
intros.
rewrite Qmult_comm.
rewrite (Qmult_comm a).
apply QG_of_Q_mul_idemp_l.
Qed.

Theorem QG_of_Q_qg_q : ∀ a, QG_of_Q (qg_q a) = a.
Proof.
intros.
apply eq_QG_eq.
destruct a as (a, ap); cbn.
rewrite ap.
do 2 rewrite Z.div_1_r.
now destruct a.
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
  cbn in Hx |-*.
  remember (Z_pos_gcd _ _) as y eqn:Hy.
  clear Hy xd.
  rename xn into x; rename y into p.
  now apply Z_le_0_div_nonneg_r in Hx.
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
  cbn in Hx |-*.
  remember (Z_pos_gcd _ _) as y eqn:Hy.
  clear Hy xd.
  rename xn into x; rename y into p.
  now apply Z_le_0_div_nonneg_r.
}
Qed.

Theorem qg_q_opp : ∀ a, qg_q (- a)%QG = - qg_q a.
Proof.
intros.
destruct a as (a, Hap); cbn.
rewrite Z_pos_gcd_opp_l.
rewrite Hap.
now do 2 rewrite Z.div_1_r.
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
Proof.
intros.
destruct a as (a, Ha).
destruct b as (b, Hb).
move b before a.
progress unfold "==".
cbn.
assert (Han : ∀ an ad bn bd,
  ((Z.pos an * Z.pos bd + bn * Z.pos ad) /
   Z.pos (Z_pos_gcd (Z.pos an * Z.pos bd + bn * Z.pos ad) (ad * bd)) *
   Z.pos (ad * bd))%Z =
  ((Z.pos an * Z.pos bd + bn * Z.pos ad) *
   Z.pos
     (Z.to_pos
        (Z.pos (ad * bd) /
         Z.pos
           (Z_pos_gcd (Z.pos an * Z.pos bd + bn * Z.pos ad)
              (ad * bd)))))%Z). {
  clear.
  intros.
  rewrite Z2Pos.id. 2: {
    apply Z.div_str_pos.
    split; [ easy | ].
    apply Pos2Z.pos_le_pos.
    progress unfold Z_pos_gcd.
    remember (_ + _)%Z as x.
    destruct x as [| x| x]; [ apply Pos.le_refl | | ]. {
      apply Pos_gcd_le_r.
    } {
      apply Pos_gcd_le_r.
    }
  }
  remember (_ + _)%Z as x.
  rewrite Z_pos_pos_gcd.
  rewrite Z.lcm_equiv2; [ | now rewrite <- Z_pos_pos_gcd ].
  rewrite Z.lcm_equiv1; [ easy | ].
  now rewrite <- Z_pos_pos_gcd.
}
destruct a as (an, ad).
destruct b as (bn, bd); cbn in Ha, Hb |-*.
destruct an as [| an| an]; [ | | ]. {
  cbn in Ha; subst ad.
  rewrite Z.mul_0_l, Z.mul_1_r.
  rewrite Z.add_0_l, Pos.mul_1_l.
  rewrite Hb.
  do 2 rewrite Z.div_1_r.
  now rewrite Pos2Z.id.
} {
  apply Han.
} {
  rewrite <- Pos2Z.opp_pos.
  rewrite <- (Z.opp_involutive bn).
  remember (- bn)%Z as bn'.
  do 2 rewrite Z.mul_opp_l.
  rewrite <- Z.opp_add_distr.
  rewrite Z_pos_gcd_opp_l.
  rewrite Z.div_opp_l_z; [ | easy | ]. 2: {
    apply Z.mod_divide; [ easy | ].
    progress unfold Z_pos_gcd.
    remember (_ + _)%Z as x.
    destruct x as [| x| x]; [ apply Z.divide_0_r | | ]. {
      rewrite Pos2Z.inj_gcd.
      apply Z.gcd_divide_l.
    } {
      rewrite Pos2Z.inj_gcd.
      apply Z.divide_opp_r.
      rewrite Pos2Z.opp_neg.
      apply Z.gcd_divide_l.
    }
  }
  do 2 rewrite Z.mul_opp_l.
  f_equal.
  apply Han.
}
Qed.

Theorem qg_q_mul : ∀ a b, qg_q (a * b) == qg_q a * qg_q b.
Proof.
intros.
destruct a as (a, Ha).
destruct b as (b, Hb).
move b before a.
progress unfold "==".
cbn.
clear Ha Hb.
destruct a as (an, ad).
destruct b as (bn, bd); cbn.
assert (Han : ∀ an,
  (Z.pos an * bn / Z.pos (Z_pos_gcd (Z.pos an * bn) (ad * bd)) *
     Z.pos (ad * bd))%Z =
  (Z.pos an * bn *
     Z.pos
       (Z.to_pos
          (Z.pos (ad * bd) /
           Z.pos (Z_pos_gcd (Z.pos an * bn) (ad * bd)))))%Z). {
  clear an; intros.
  assert (Hbn : ∀ bn,
    (Z.pos (an * bn) / Z.pos (Pos.gcd (an * bn) (ad * bd)) *
       Z.pos (ad * bd))%Z =
    Z.pos
      (an * bn *
       Z.to_pos
         (Z.pos (ad * bd) / Z.pos (Pos.gcd (an * bn) (ad * bd))))). {
    clear bn; intros.
    rewrite Pos2Z.inj_gcd.
    rewrite Z.gcd_div_swap.
    rewrite Z.lcm_equiv1; [ | now rewrite <- Pos2Z.inj_gcd ].
    remember (an * bn)%positive as abn.
    remember (ad * bd)%positive as abd.
    rewrite Pos2Z.inj_mul.
    subst abn abd.
    rewrite Z2Pos.id. 2: {
      apply Z.div_str_pos.
      rewrite <- Pos2Z.inj_gcd.
      split; [ easy | ].
      apply Pos2Z.pos_le_pos.
      apply Pos_gcd_le_r.
    }
    apply Z.divide_div_mul_exact; [ | apply Z.gcd_divide_r ].
    now intros H; apply Z.gcd_eq_0_l in H.
  }
  destruct bn as [| bn| bn]; [ easy | apply Hbn | ].
  cbn.
  do 2 rewrite <- Pos2Z.opp_pos.
  rewrite Z.div_opp_l_z; [ | easy | ]. 2: {
    rewrite Pos2Z.inj_gcd.
    apply Z.mod_divide; [ now intros H; apply Z.gcd_eq_0_l in H | ].
    apply Z.gcd_divide_l.
  }
  rewrite Z.mul_opp_l.
  f_equal.
  apply Hbn.
}
destruct an as [| an| an]; [ easy | apply Han | ].
rewrite <- Pos2Z.opp_pos.
rewrite Z.mul_opp_l.
rewrite Z_pos_gcd_opp_l.
rewrite Z.div_opp_l_z; [ | easy | ]. 2: {
  remember (Z.pos an * bn)%Z as x.
  progress unfold Z_pos_gcd.
  destruct x as [| x| x]; [ easy | | ]. {
    rewrite Pos2Z.inj_gcd.
    apply Z.mod_divide; [ now intros H; apply Z.gcd_eq_0_l in H | ].
    apply Z.gcd_divide_l.
  } {
    rewrite <- Pos2Z.opp_pos.
    apply Z.mod_opp_l_z; [ easy | ].
    rewrite Pos2Z.inj_gcd.
    apply Z.mod_divide; [ now intros H; apply Z.gcd_eq_0_l in H | ].
    apply Z.gcd_divide_l.
  }
}
do 2 rewrite Z.mul_opp_l.
f_equal.
apply Han.
Qed.

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

Theorem QG_of_Z_add :
  ∀ a b, QG_of_Z (a + b) = (QG_of_Z a + QG_of_Z b)%QG.
Proof.
intros.
progress unfold QG_of_Z.
apply eq_QG_eq; cbn.
do 4 rewrite Z_pos_pos_gcd.
do 4 rewrite Z.gcd_1_r; cbn.
do 4 rewrite Z.div_1_r.
now do 2 rewrite Z.mul_1_r.
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
  rewrite Z_pos_pos_gcd.
  rewrite Z.gcd_1_r; cbn.
  rewrite Z.div_1_r.
  progress unfold Qle; cbn.
  rewrite Z.mul_1_r.
  rewrite Z.mul_comm.
  now apply Z.mul_div_le.
}
apply QG_lt_iff.
split. {
  apply Qle_bool_iff; cbn.
  progress unfold Z_of_QG; cbn.
  do 2 rewrite Z_pos_pos_gcd.
  do 2 rewrite Z.gcd_1_r; cbn.
  do 2 rewrite Z.div_1_r.
  rewrite Z.mul_1_r.
  progress unfold Qle; cbn.
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
do 2 rewrite Z_pos_pos_gcd.
do 2 rewrite Z.gcd_1_r.
do 4 rewrite Z.div_1_r.
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
    apply Qle_bool_iff; cbn.
    progress unfold Qle; cbn.
    rewrite Pos.mul_1_r, Z.mul_1_r.
    apply Z.div_pos; [ | easy ].
    apply Z.mul_nonneg_nonneg. {
      apply QG_lt_iff in Ha.
      destruct Ha as (Ha, Haz).
      apply Qle_bool_iff in Ha; cbn in Ha.
      progress unfold Qle in Ha.
      cbn in Ha.
      now rewrite Z.mul_1_r in Ha.
    } {
      apply Z.le_trans with (m := 1%Z); [ easy | ].
      apply Z.le_sub_le_add_r.
      rewrite Z.sub_diag.
      apply Nat2Z.is_nonneg.
    }
  } {
    intros H1; symmetry in H1.
    apply eq_QG_eq in H1; cbn in H1.
    remember (Qnum (qg_q a) * (Z.of_nat x + 1))%Z as y.
    rewrite Pos.mul_1_r in H1.
    injection H1; clear H1; intros H1 H2.
    apply -> Z.div_small_iff in H2; [ | easy ].
    rewrite Z_pos_pos_gcd in H2.
    destruct H2 as [H2| H2]. 2: {
      destruct H2 as (H2, H3).
      apply Z.nlt_ge in H3; apply H3; clear H3.
      rewrite Heqy.
      apply Z.mul_pos_pos. {
        destruct a as ((an, ad), Hap).
        cbn in Ha |-*.
        apply QG_lt_iff in Ha.
        destruct Ha as (Ha1, Ha2).
        apply Qle_bool_iff in Ha1.
        cbn in Ha1.
        assert (H : ¬ an # ad == 0). {
          intros H.
          apply Ha2.
          now apply qeq_QG_eq.
        }
        move H before Ha2; clear Ha2; rename H into Ha2.
        cbn in Ha2.
        progress unfold Qle in Ha1.
        cbn in Ha1.
        rewrite Z.mul_1_r in Ha1.
        apply Z.nle_gt; intros Ha3.
        apply Z.le_antisymm in Ha3; [ | easy ].
        subst an.
        now apply Ha2; clear Ha2.
      }
      apply (Z.lt_le_trans _ 1%Z); [ easy | ].
      apply Z.le_sub_le_add_r.
      rewrite Z.sub_diag.
      apply Nat2Z.is_nonneg.
    }
    destruct H2 as (H2, H3).
    apply Z.nle_gt in H3; apply H3; clear H3.
    apply Z.divide_pos_le. {
      apply Z.nle_gt; intros H3.
      apply Z.le_antisymm in H3; [ | easy ].
      rewrite Heqy in H3.
      symmetry in H3.
      apply Z.eq_mul_0 in H3.
      destruct H3 as [H3| H3]. {
        apply QG_lt_iff in Ha.
        destruct a as ((an, ad), Hap).
        cbn in H3; subst an.
        destruct Ha as (Ha1, Ha2).
        apply Ha2; symmetry.
        now apply qeq_QG_eq.
      }
      apply Z.add_move_0_r in H3.
      specialize (Nat2Z.is_nonneg x) as H4.
      now rewrite H3 in H4.
    }
    apply Z.gcd_divide_l.
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
  cbn.
  remember (Z_pos_gcd (Qnum (/ qg_q a)) _) as ga eqn:Hga.
  remember (Z_pos_gcd _ _) as gb eqn:Hgb in |-*.
  apply Z.div_pos; [ | easy ].
  apply Z.mul_nonneg_nonneg. {
    apply QG_lt_iff in Hb.
    destruct Hb as (Hb, Hbz).
    apply Qle_bool_iff in Hb; cbn in Hb.
    progress unfold Qle in Hb.
    now rewrite Z.mul_1_r in Hb.
  } {
    apply Z.div_pos; [ | easy ].
    progress unfold Qinv.
    remember (Qnum (qg_q a)) as x eqn:Hx; symmetry in Hx.
    destruct x as [| x| x]; [ easy | easy | ].
    exfalso.
    destruct a as ((an, ap), Hap).
    cbn in Ha, Hx.
    subst an.
    apply QG_lt_iff in Ha.
    destruct Ha as (Ha, Ha').
    apply Qle_bool_iff in Ha.
    cbn in Ha.
    apply Qle_not_lt in Ha.
    now apply Ha.
  }
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

Definition QG_compare a b :=
  let qa := qg_q a in
  let qb := qg_q b in
  (Qnum qa * QDen qb ?= Qnum qb * QDen qa)%Z.

Notation "a ?= b" := (QG_compare a b) : QG_scope.

Theorem QG_compare_refl : ∀ a, (a ?= a)%QG = Eq.
Proof.
intros.
apply Z.compare_refl.
Qed.

Theorem QG_compare_eq_iff : ∀ a b, (a ?= b)%QG = Eq ↔ a = b.
Proof.
intros.
split; intros Hab; [ | subst b; apply QG_compare_refl ].
progress unfold QG_compare in Hab.
apply Z.compare_eq_iff in Hab.
destruct a as (qa, Ha).
destruct b as (qb, Hb).
cbn in Hab.
move qb before qa.
apply eq_QG_eq; cbn.
rewrite Z_pos_gcd_Z_gcd in Ha, Hb.
rewrite <- Z2Pos.inj_1 in Ha, Hb.
destruct (Z.eq_dec (Qnum qa) 0) as [Haz| Haz]. {
  rewrite Haz in Ha, Hab.
  cbn in Ha, Hab.
  symmetry in Hab.
  apply (Z.eq_mul_0_l) in Hab; [ | easy ].
  rewrite Hab in Hb; cbn in Hb.
  destruct qa, qb; cbn in *.
  congruence.
}
destruct (Z.eq_dec (Qnum qb) 0) as [Hbz| Hbz]. {
  rewrite Hbz in Hb, Hab.
  cbn in Hb, Hab.
  now apply (Z.eq_mul_0_l) in Hab.
}
apply Z2Pos.inj in Ha; [ | | easy ]. 2: {
  apply Z.le_neq.
  split; [ apply Z.gcd_nonneg | ].
  intros H; symmetry in H.
  now apply Z.gcd_eq_0_r in H.
}
apply Z2Pos.inj in Hb; [ | | easy ]. 2: {
  apply Z.le_neq.
  split; [ apply Z.gcd_nonneg | ].
  intros H; symmetry in H.
  now apply Z.gcd_eq_0_r in H.
}
generalize Ha; intros Hab1.
apply (Z.gauss _ _ (Qnum qb)) in Hab1. 2: {
  rewrite Z.mul_comm, <- Hab.
  apply Z.divide_factor_l.
}
generalize Hb; intros Hba1.
apply (Z.gauss _ _ (Qnum qa)) in Hba1. 2: {
  rewrite Z.mul_comm, Hab.
  apply Z.divide_factor_l.
}
apply Z.divide_antisym_abs in Hab1; [ | easy ].
clear Hba1.
apply Z.abs_eq_cases in Hab1.
destruct Hab1 as [Hab1| Hab1]. {
  rewrite Hab1 in Hab.
  apply Z.mul_reg_l in Hab; [ | easy ].
  destruct qa, qb.
  cbn in *.
  congruence.
}
rewrite Hab1 in Hab.
rewrite Z.mul_opp_l in Hab.
rewrite <- Z.mul_opp_r in Hab.
now apply Z.mul_reg_l in Hab.
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
