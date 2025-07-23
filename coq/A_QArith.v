(** * A ℚ arithmetics *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Morphisms.
Require Import A_PosArith A_ZArith.

Record Q := mk_q
  { q_num : Z;
    q_den : pos;
    q_prop : Z.gcd q_num (Z.of_pos q_den) = 1%Z }.

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.
Bind Scope Q_scope with Q.

Definition q_Den a := Z.of_pos (q_den a).

(* misc *)

Theorem Nat_sub_lt_mono_l :
  ∀ a b c, (c < a ∨ b <= a → c < b → a - b < a - c)%nat.
Proof. intros * H1 H2; flia H1 H2. Qed.

Theorem Nat_sub_lt_mono_r :
  ∀ a b c, (c < b ∨ c <= a → a < b → a - c < b - c)%nat.
Proof. intros * H1 H2; flia H1 H2. Qed.

Theorem Nat_add_1_r_pos : ∀ a, (0 < a + 1)%nat.
Proof. flia. Qed.

Theorem q_Den_num_den : ∀ a b p, q_Den (mk_q a b p) = Z.of_pos b.
Proof. easy. Qed.

Theorem q_Den_neq_0 : ∀ a, q_Den a ≠ 0%Z.
Proof. easy. Qed.

Theorem q_Den_pos : ∀ a, (0 < q_Den a)%Z.
Proof. easy. Qed.

Theorem q_Den_nonneg : ∀ a, (0 ≤ q_Den a)%Z.
Proof. easy. Qed.

Hint Resolve Nat_add_1_r_pos : core.
Hint Resolve q_Den_pos : core.

(* end misc *)

Theorem fold_q_Den : ∀ a, Z.of_pos (q_den a) = q_Den a.
Proof. easy. Qed.

Module Q.

Open Scope Z_scope.

Theorem add_prop : ∀ a b,
  let n := q_num a * q_Den b + q_num b * q_Den a in
  let d := q_Den a * q_Den b in
  Z.gcd (n / Z.gcd n d) (Z.of_pos (Z.to_pos (d / Z.gcd n d))) = 1.
Proof.
intros.
rewrite Z2Pos.id. {
  apply Z.gcd_div_gcd; [ | easy ].
  intros H.
  now apply Z.gcd_eq_0 in H.
}
Theorem Z_div_le_lower_bound : ∀ a b c, 0 < c → c * a ≤ b → a ≤ b / c.
Proof.
intros * Hzc Hca.
Theorem Z_div_le_mono : ∀ a b c : Z, 0 < c → a ≤ b → a / c ≤ b / c.
Proof.
intros * Hzc Hab.
apply Z.lt_eq_cases in Hab.
destruct Hab as [Hab| ]; [ | now subst ].
apply Z.lt_succ_r.
apply (Z.mul_lt_mono_pos_l c); [ easy | ].
rewrite Z.mul_add_distr_l, Z.mul_1_r.
Theorem Z_div_mod : ∀ a b : Z, b ≠ 0 → a = b * (a / b) + a mod b.
Proof.
intros * Hbz.
progress unfold Z.div.
progress unfold Z.rem.
remember (Z.div_eucl a b) as ab eqn:Hab.
symmetry in Hab.
destruct ab as (q, r); cbn.
progress unfold Z.div_eucl in Hab.
destruct a as [| sa va]. {
  injection Hab; clear Hab; intros; subst.
  rewrite Z.mul_0_r; symmetry.
  apply Z.add_0_l.
}
destruct b as [| sb vb]; [ easy | ].
destruct sa. {
  destruct sb. {
    cbn in Hab.
    injection Hab; clear Hab; intros; subst.
    specialize (Nat.div_mod (Pos.to_nat va) (Pos.to_nat vb)) as H1.
    assert (H : Pos.to_nat vb ≠ 0%nat) by easy.
    specialize (H1 H); clear H.
    apply (f_equal Z.of_nat) in H1.
    rewrite Z.pos_nat in H1.
    rewrite H1 at 1.
    rewrite Nat2Z.inj_add.
    progress f_equal.
    rewrite Nat2Z.inj_mul.
    progress f_equal.
    apply Z.pos_nat.
  }
  cbn in Hab.
  injection Hab; clear Hab; intros; subst.
  rewrite Nat2Z.inj_mod.
  do 2 rewrite Z.pos_nat.
  remember (z_val true va mod z_val true vb) as ab eqn:Hab.
  symmetry in Hab.
  destruct ab as [| sab vab]. {
    rewrite Z.add_0_r.
    rewrite Z.mul_opp_r.
    rewrite <- Z.mul_opp_l.
    cbn - [ Z.mul ].
    apply Z.mod_divide in Hab; [ | easy ].
    destruct Hab as (c, Hc).
    rewrite Hc.
    rewrite Z.mul_comm.
    progress f_equal.
    symmetry.
    rewrite Nat2Z.inj_div.
    do 2 rewrite Z.pos_nat.
    rewrite Hc.
    now apply Z.mul_div.
  }
  rewrite Z.mul_opp_r, <- Z.mul_opp_l.
  cbn - [ Z.mul ].
  rewrite Nat2Z.inj_div.
  do 2 rewrite Z.pos_nat.
  destruct sab. {
    remember (vb ?= vab)%pos as vbab eqn:Hvbab.
    symmetry in Hvbab.
    specialize (Z.mod_pos_bound (z_val true va) (z_val true vb)) as H1.
    assert (H : 0 < z_val true vb) by easy.
    specialize (H1 H); clear H.
    rewrite Hab in H1.
    destruct H1 as (_, H1).
    destruct vbab. {
      exfalso.
      apply Pos.compare_eq_iff in Hvbab; subst vab.
      now apply Z.lt_irrefl in H1.
    } {
      apply Pos.compare_lt_iff in Hvbab.
      do 2 rewrite <- Z.pos_nat in H1.
      apply Nat2Z.inj_lt in H1.
      apply Pos2Nat.inj_lt in H1.
      now apply Pos.lt_asymm in H1.
    } {
      apply Pos.compare_gt_iff in Hvbab.
      replace (z_val false _) with (- z_val true (vb - vab)) by easy.
      rewrite Z.add_opp_r.
      rewrite Z.mul_add_distr_l, Z.mul_1_r.
      do 3 rewrite <- Z.pos_nat.
      rewrite Pos2Nat.inj_sub; [ | easy ].
      rewrite Nat2Z.inj_sub. 2: {
        apply Nat.lt_le_incl.
        now apply Pos2Nat.inj_lt.
      }
      rewrite Z.sub_sub_distr.
      rewrite Z.add_sub.
      cbn in Hab.
      rewrite <- Z.pos_nat in Hab.
      apply Nat2Z.inj in Hab.
      specialize (Nat.div_mod) as H2.
      specialize (H2 (Pos.to_nat va) (Pos.to_nat vb)).
      assert (H : Pos.to_nat vb ≠ 0%nat) by easy.
      specialize (H2 H); clear H.
      rewrite Hab in H2.
      rewrite H2 at 1.
      rewrite Nat2Z.inj_add.
      progress f_equal.
      rewrite Nat2Z.inj_mul.
      progress f_equal.
      apply Nat2Z.inj_div.
    }
  }
  exfalso.
  specialize (Z.mod_pos_bound (z_val true va) (z_val true vb)) as H1.
  assert (H : 0 < z_val true vb) by easy.
  specialize (H1 H); clear H.
  destruct H1 as (H1, _).
  now rewrite Hab in H1.
}
clear Hbz.
destruct sb. {
  cbn in Hab.
  injection Hab; clear Hab; intros; subst.
  remember (Z.of_nat _) as vab eqn:Hvab.
  symmetry in Hvab.
  destruct vab as [| svab vvab]. {
    rewrite Nat2Z.inj_mod in Hvab.
    rewrite Nat2Z.inj_div.
    do 2 rewrite Z.pos_nat in Hvab |-*.
    apply Z.mod_divide in Hvab; [ | easy ].
    destruct Hvab as (c, Hc).
    apply (f_equal Z.opp) in Hc.
    cbn in Hc.
    rewrite <- Z.mul_opp_r in Hc.
    cbn in Hc.
    rewrite Hc, Z.mul_comm.
    rewrite Z.mul_opp_r, <- Z.mul_opp_l; cbn.
    destruct c as [| sc vc]; [ easy | ].
    destruct sc; [ | easy ].
    cbn in Hc.
    injection Hc; clear Hc; intros Hc.
    rewrite Hc.
    rewrite Nat2Z.inj_div.
    rewrite Pos2Nat.inj_mul.
    rewrite Nat2Z.inj_mul.
    do 2 rewrite Z.pos_nat.
    rewrite Z.mul_div; [ | easy ].
    symmetry; apply Z.add_0_r.
  }
  destruct svab. {
    cbn.
    rewrite (Z.add_comm _ 1).
    cbn.
    remember (Z.of_nat (_ / _)) as vab eqn:Hdab.
    symmetry in Hdab.
    destruct vab as [| sdab vdab]. {
      apply Z.of_nat_eq_0 in Hdab.
      apply Nat.div_small_iff in Hdab; [ | easy ].
      rewrite Nat.mod_small in Hvab; [ | easy ].
      rewrite Z.pos_nat in Hvab.
      injection Hvab; clear Hvab; intros H; subst vvab.
      apply Pos2Nat.inj_lt in Hdab.
      cbn - [ Z.add ].
      rewrite Pos.mul_1_r.
      rewrite Pos.compare_antisym.
      generalize Hdab; intros H.
      apply Pos.compare_lt_iff in H.
      rewrite H; clear H; cbn.
      remember (vb ?= vb - va)%pos as c eqn:Hc.
      symmetry in Hc.
      destruct c. {
        apply Pos.compare_eq_iff in Hc.
        progress unfold Pos.sub in Hc.
        destruct vb as (b).
        injection Hc; clear Hc; intros Hc.
        destruct b; [ easy | flia Hc ].
      } {
        apply Pos.compare_lt_iff in Hc.
        exfalso; apply Pos.nle_gt in Hc.
        apply Hc; clear Hc.
        progress unfold Pos.le; cbn.
        flia.
      } {
        apply Pos.compare_gt_iff in Hc.
        f_equal.
        rewrite Pos.sub_sub_distr; [ | easy | easy ].
        rewrite Pos.add_comm; symmetry.
        apply Pos.add_sub.
      }
    }
    destruct sdab. {
      cbn - [ Z.add ].
      rewrite Nat2Z.inj_mod in Hvab.
      do 2 rewrite Z.pos_nat in Hvab.
      specialize (Z.mod_pos_bound (z_val true va) (z_val true vb)) as H1.
      assert (H : 0 < z_val true vb) by easy.
      specialize (H1 H); clear H.
      destruct H1 as (_, H1).
      rewrite Hvab in H1.
      do 2 rewrite <- Z.pos_nat in H1.
      apply Nat2Z.inj_lt in H1.
      generalize H1; intros H2.
      apply Pos2Nat.inj_lt in H1.
      rewrite Pos.compare_antisym.
      generalize H1; intros H.
      apply Pos.compare_lt_iff in H.
      rewrite H; clear H.
      apply Z.opp_inj.
      cbn - [ Z.add ].
      rewrite Z.opp_add_distr.
      cbn - [ Z.add ].
      do 3 rewrite <- Z.pos_nat.
      rewrite Pos2Nat.inj_mul.
      rewrite Pos2Nat.inj_sub; [ | easy ].
      rewrite Pos2Nat.inj_add.
      rewrite Nat2Z.inj_mul.
      rewrite Nat2Z.inj_sub; [ | now apply Nat.lt_le_incl ].
      rewrite Nat2Z.inj_add.
      rewrite (Z.pos_nat 1).
      do 4 rewrite Z.pos_nat.
      rewrite Z.mul_add_distr_l, Z.mul_1_r.
      rewrite Z.sub_sub_distr.
      rewrite Z.add_sub_swap.
      rewrite Z.sub_diag, Z.add_0_l.
      destruct (Pos.divide_dec vb va) as [Hdba| Hdba]. {
        destruct Hdba as (c, Hc).
        subst va.
        do 3 rewrite <- Z.pos_nat in Hvab.
        rewrite Pos2Nat.inj_mul in Hvab.
        rewrite Nat2Z.inj_mul in Hvab.
        do 3 rewrite Z.pos_nat in Hvab.
        now rewrite Z.mod_mul in Hvab.
      }
      rewrite Nat2Z.inj_div in Hdab.
      do 2 rewrite Z.pos_nat in Hdab.
      rename va into a.
      rename vb into b.
      rename vdab into q.
      rename vvab into r.
      do 4 rewrite <- Z.pos_nat.
      rewrite <- Nat2Z.inj_mul, <- Nat2Z.inj_add.
      destruct (Pos.eq_dec a b) as [Hab| Hab]. {
        subst b.
        now rewrite Z.mod_same in Hvab.
      }
      progress f_equal.
      rewrite <- Pos2Nat.inj_mul, <- Pos2Nat.inj_add.
      progress f_equal.
      do 3 rewrite <- Z.pos_nat in Hvab, Hdab.
      rewrite <- Nat2Z.inj_mod in Hvab.
      rewrite <- Nat2Z.inj_div in Hdab.
      apply Nat2Z.inj in Hvab, Hdab.
      rewrite <- Pos2Nat.inj_mod in Hvab. 2: {
        intros H; rewrite H in Hvab; symmetry in Hvab.
        now apply Pos2Nat.neq_0 in Hvab.
      }
      apply Pos2Nat.inj in Hvab.
      destruct (le_dec (Pos.to_nat a) (Pos.to_nat b)) as [Hba| Hba]. {
        symmetry in Hdab.
        rewrite Nat.div_small in Hdab. 2: {
          apply Nat.le_neq.
          split; [ easy | ].
          intros H.
          now apply Pos2Nat.inj in H.
        }
        now apply Pos.to_nat_neq_0 in Hdab.
      }
      apply Nat.nle_gt in Hba.
      apply Pos2Nat.inj_lt in Hba.
      rewrite <- Pos2Nat.inj_div in Hdab. 2: {
        intros H; rewrite H in Hdab; symmetry in Hdab.
        now apply Pos2Nat.neq_0 in Hdab.
      }
      apply Pos2Nat.inj in Hdab.
      subst q r.
      now apply Pos.div_mod.
    }
...
Search Pos.divide.
      intros (c, Hc).
...
intros.
progress unfold Pos.div, Pos.rem.
rewrite <- Pos2Nat.inj_div.
rewrite Pos2Nat.id.
rewrite <- Pos2Nat.inj_mod.
rewrite Pos2Nat.id.
...
      apply (f_equal Z.to_pos) in Hvab.
Search (Z.to_pos (_ mod _)).
Search (Z.to_pos _ = _).
      rewrite <- Z2Pos.inj in Hvab.
...
      rewrite Pos2Nat.inj_sub; [ | easy ].
      rewrite Nat2Z.inj_sub; [ | now apply Nat.lt_le_incl ].
      do 2 rewrite Z.pos_nat.
      apply
...
      remember (vb ?= vvab)%pos as c eqn:Hc.
      symmetry in Hc.
      destruct c. {
        apply Pos.compare_eq_iff in Hc; subst vvab.
        rewrite Nat2Z.inj_mod in Hvab.
        do 2 rewrite Z.pos_nat in Hvab.
        specialize (Z.mod_pos_bound (z_val true va) (z_val true vb)) as H1.
        assert (H : 0 < z_val true vb) by easy.
        specialize (H1 H); clear H.
        destruct H1 as (_, H1).
        rewrite Hvab in H1.
        now apply Z.lt_irrefl in H1.
      } {
        apply Pos.compare_lt_iff in Hc.
        rewrite Nat2Z.inj_mod in Hvab.
        do 2 rewrite Z.pos_nat in Hvab.
        specialize (Z.mod_pos_bound (z_val true va) (z_val true vb)) as H1.
        assert (H : 0 < z_val true vb) by easy.
        specialize (H1 H); clear H.
        destruct H1 as (_, H1).
        rewrite Hvab in H1.
        now apply Z.lt_irrefl in H1.
...
Require Import ZArith.
Search (_ - (_ - _))%positive.
...
Require Import ZArith.
Search (_ - _ = _ ↔ _)%positive.
Search (_ = _ - _ ↔ _)%positive.
Search (_ ↔ _ - _ = _)%positive.
Search (_ ↔ _ = _ - _)%positive.
...
(* faux si a = 1 et b = 1 *)
Theorem Pos_compare_sub_diag_r : ∀ a b, (a ?= a - b)%pos = Gt.
Proof.
intros.
remember (_ ?= _)%pos as c eqn:Hc.
symmetry in Hc.
destruct c; [ | | easy ]. {
  apply Pos.compare_eq_iff in Hc.
  progress unfold Pos.sub in Hc.
  destruct a as (a).
  destruct b as (b).
  cbn in Hc.
  injection Hc; clear Hc; intros Hc.


  apply (f_equal Pos.to_nat) in Hc.

  rewrite Pos2Nat.inj_sub in Hc.
progress unfold Pos.compare.

...
      rewrite Pos_compare_sub_diag_r.
      remember (_ ?= _ - _)%pos as c eqn:Hc.
      symmetry in Hc.
      destruct c. {
        rewrite Pos.compare_eq_iff in Hc.
Search (_ - _ = _)%pos.
...
Search (_ = _ - _)%pos.

Search (CompOpp (_ ?= _)%pos).
      rewrite <- Pos.compare_antisym in H1.
Search CompOpp.
...
      remember (vb ?= vvab)%pos as vbab eqn:Hvbab.
      symmetry in Hvbab.

      destruct vbab. {
        apply Pos.compare_eq_iff in Hvbab; subst vvab.
        now apply Nat.lt_irrefl in H1.
      } {
        apply Pos.compare_lt_iff in Hvbab.
   Search (Pos.to_nat _ < _)%nat.
     apply Pos.lt_asymm in Hvbab.
...
        specialize Nat.mod_upper_bound as H1.
        specialize (H1 (Pos.to_nat va) (Pos.to_nat vb)).
        assert (H : Pos.to_nat vb ≠ 0%nat) by easy.
        specialize (H1 H); clear H.
        rewrite Hvab in H1.
        now apply Nat.lt_irrefl in H1.
...
Search (_ mod _ < _).
...
apply (Z.mul_le_mono_pos_l b); [ easy | ].
transitivity a; [ easy | ].
...
rewrite <- Z.divide_div_mul_exact.
...
apply Z_div_le_lower_bound. {
  apply Z.lt_iff.
  split; [ apply Z.gcd_nonneg | ].
  intros H; symmetry in H.
  subst n d.
  now apply Z.gcd_eq_0 in H.
}
rewrite Z.mul_1_r.
destruct n as [| sn vn]. {
  cbn - [ Z.abs ].
  now rewrite Z.abs_nonneg_eq.
}
destruct sn. {
Print Z.gcd.
  cbn.
...
Search (z_val _ _ ≤ z_val _ _).
...
destruct a as (an, ad, Hap).
destruct b as (bn, bd, Hbp).
cbn.
do 2 rewrite q_Den_num_den.
move bn before an; move bd before ad.
destruct ad as (ad).
destruct bd as (bd).
(**)
progress unfold Z.gcd in Hap, Hbp.
destruct an as [| sa va]. {
  cbn.
  destruct bn as [| sb vb]. {
    cbn.
    rewrite Nat.sub_add; [ | easy ].
    cbn in Hap, Hbp |-*.
    rewrite Nat.add_1_r in Hap, Hbp.
    destruct ad; [ now destruct bd | easy ].
  }
  cbn in Hap, Hbp |-*.
  rewrite Nat.add_1_r in Hap.
  destruct ad; [ clear Hap | easy ].
  rewrite Pos.mul_1_r, Pos.mul_1_l.
  easy.
}
destruct bn as [| sb vb]. {
  cbn.
  cbn in Hap, Hbp |-*.
  rewrite Nat.add_1_r in Hbp.
  destruct bd; [ clear Hbp | easy ].
  now do 2 rewrite Pos.mul_1_r.
}
destruct va as (va).
destruct vb as (vb).
cbn in Hap, Hbp |-*.
progress unfold Pos.gcd in Hap, Hbp.
cbn in Hap, Hbp |-*.
injection Hap; clear Hap; intros Hap.
injection Hbp; clear Hbp; intros Hbp.
apply Nat.sub_0_le in Hap, Hbp.
apply Nat.le_1_r in Hap, Hbp.
destruct Hap as [Hap| Hap]. {
  apply Nat.gcd_eq_0_l in Hap.
  now rewrite Nat.add_1_r in Hap.
}
destruct Hbp as [Hbp| Hbp]. {
  apply Nat.gcd_eq_0_l in Hbp.
  now rewrite Nat.add_1_r in Hbp.
}
destruct sa; cbn. {
  destruct sb; cbn. {
    f_equal.
    progress unfold Pos.gcd.
    cbn.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.sub_add; [ | flia ].
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.add_shuffle0.
    rewrite Nat.sub_add; [ | easy ].
    apply Nat2Pos.eq_1; right.
...
    rewrite Nat.gcd_comm.
    rewrite <- Nat.Lcm0.gcd_mod.
...
Theorem Nat_gcd_1_mul_r : ∀ a b c,
  Nat.gcd a b = 1%nat
  → Nat.gcd a c = 1%nat
  → Nat.gcd a (b * c) = 1%nat.
...
    apply Nat_gcd_1_mul_r. {
      rewrite Nat.gcd_comm.
      rewrite Nat.gcd_add_mult_diag_r.
...
      apply Nat_gcd_1_mul_r; [ now rewrite Nat.gcd_comm | ].
Search (Nat.gcd _ _ = 1)%nat.
...
      rewrite <- (Nat.mul_1_r (ad + 1)) at 1.
Search (Nat.gcd (_ * _)).
      rewrite Nat.gcd_mul_mono_l.
Search (Nat.gcd _ (_ - _)).
      rewrite <- Nat.gcd_sub_diag_r.
....
    replace 1%pos with (Pos.of_nat 1) by easy.
...
    rewrite <- ggcd_gcd in Hap, Hbp |-*.
    specialize (ggcd_correct_divisors (va + 1) (ad + 1)) as Ha.
    remember (ggcd (va + 1) (ad + 1)) as ga eqn:Hga.
    symmetry in Hga.
    destruct ga as (g, (a1, a2)).
    cbn in Hap; subst g.
    do 2 rewrite Nat.mul_1_l in Ha.
    destruct Ha; subst a1 a2.
progress unfold ggcd in Hga.
...
    progress unfold Pos.add, Pos.mul.
    cbn.
    cbn.
... ...
    rewrite Nat_compare_sub_mono_r; [ | easy | easy ].
...
progress unfold Z.gcd.
remember (an * _ + _)%Z as ab eqn:Hab.
symmetry in Hab.
destruct ab as [| sab vab]. {
  cbn - [ Pos.mul ].
  rewrite Pos2Nat.inj_mul.
  rewrite Nat2Z.inj_mul.
  progress unfold Z.gcd in Hap, Hbp.
  destruct an as [| sa va]. {
    cbn in Hap.
    rewrite Hap, Z.mul_1_l.
    now destruct bn.
  }
  remember (Z.of_pos ad) as zad eqn:Hzad.
  symmetry in Hzad.
  destruct zad as [| sza vza]; [ easy | ].
  injection Hap; clear Hap; intros H1.
  apply Nat.sub_0_le in H1.
  apply Nat.le_1_r in H1.
  destruct H1 as [H1| H1]. {
    apply Nat.gcd_eq_0_l in H1.
    now apply Pos.to_nat_neq_0 in H1.
  }
  destruct bn as [| sb vb]; [ easy | ].
  remember (Z.of_pos bd) as zbd eqn:Hzbd.
  destruct zbd as [| szb vzb]; [ easy | ].
  injection Hbp; clear Hbp; intros H2.
  apply Nat.sub_0_le in H2.
  apply Nat.le_1_r in H2.
  destruct H2 as [H2| H2]. {
    apply Nat.gcd_eq_0_l in H2.
    now apply Pos.to_nat_neq_0 in H2.
  }
  do 2 rewrite Z.pos_nat.
  cbn.
  progress f_equal.
  rewrite <- Hzad, Hzbd in Hab.
  apply Pos.eq_mul_1.
  destruct sa. {
    destruct sb; [ easy | ].
    cbn - [ Pos.mul ] in Hab.
    remember (va * bd ?= vb * ad)%pos as ab eqn:Hvab.
    symmetry in Hvab.
    destruct ab; [ clear Hab | easy | easy ].
    apply Pos.compare_eq_iff in Hvab.
(**)
    apply (f_equal Pos.of_nat) in H1, H2.
    assert (H : Pos.gcd va vza = 1%pos) by easy.
    clear H1; rename H into H1.
    assert (H : Pos.gcd vb vzb = 1%pos) by easy.
    clear H2; rename H into H2.
    destruct sza; [ | easy ].
    destruct szb; [ | easy ].
    symmetry in Hzad.
    injection Hzad; clear Hzad; intros; subst.
    injection Hzbd; clear Hzbd; intros; subst.
    destruct ad as (ad).
    destruct bd as (bd).
    destruct va as (va).
    destruct vb as (vb).
    destruct ad. {
      split; [ easy | ].
      destruct bd; [ easy | ].
      exfalso.
      rewrite Pos.mul_1_r in Hvab.
      progress unfold Pos.mul in Hvab.
      cbn in Hvab.
      injection Hvab; clear Hvab; intros; subst vb.
      progress unfold Pos.gcd in H2.
      cbn in H2.
      rewrite Nat.sub_add in H2; [ | flia ].
      do 2 rewrite Nat.add_1_r in H2.
      cbn - [ Nat.modulo ] in H2.
      destruct va. {
        rewrite Nat.add_0_r in H2.
        now rewrite Nat.Div0.mod_same in H2.
      }
      rewrite Nat.mod_small in H2; [ | flia ].
      rewrite <- Nat.gcd_sub_diag_r in H2; [ | flia ].
      do 2 rewrite <- Nat.add_succ_l in H2.
      rewrite Nat.add_comm, Nat.add_sub in H2.
      rewrite <- (Nat.mul_1_l (S (S bd))) in H2 at 1.
      rewrite Nat.gcd_mul_mono_r in H2.
      rewrite Pos.of_nat_mul in H2; [ | easy | easy ].
      now apply Pos.eq_mul_1 in H2.
    }
    exfalso.
...
Search (Pos.of_nat (Nat.gcd _ _)).
rewrite Pos.fold_gcd in H1.
    apply (f_equal Pos.to_nat) in Hvab.
    do 2 rewrite Pos2Nat.inj_mul in Hvab.
    destruct sza; [ | easy ].
    destruct szb; [ | easy ].
    injection Hzad; clear Hzad; intros; subst vza.
    injection Hzbd; clear Hzbd; intros; subst vzb.
    enough (H : Pos.to_nat ad = 1%nat ∧ Pos.to_nat bd = 1%nat). {
      destruct H as (H3, H4).
      replace 1%nat with (Pos.to_nat 1) in H3, H4 by easy.
      now apply Pos2Nat.inj in H3, H4.
    }
...
    remember (Pos.to_nat ad) as a; clear ad Heqa.
    remember (Pos.to_nat bd) as b; clear bd Heqb.
    remember (Pos.to_nat va) as c; clear va Heqc.
    remember (Pos.to_nat vb) as d; clear vb Heqd.
    generalize H1; intros H3.
    generalize H2; intros H4.
    apply (Nat.gauss c a d) in H1. 2: {
      exists b.
      now rewrite (Nat.mul_comm a), (Nat.mul_comm b).
    }
    apply (Nat.gauss d b c) in H2. 2: {
      exists a.
      now rewrite (Nat.mul_comm a), (Nat.mul_comm b).
    }
    apply Nat.divide_antisym in H1; [ subst | easy ].
...
    apply (f_equal Z.of_pos) in Hvab.
    do 2 rewrite Pos2Z.inj_mul in Hvab.
    rewrite Hzad, <- Hzbd in Hvab.
Search (Nat.gcd _ _ = 1%nat).
...
...
Search (Nat.gcd _ _ = 0%nat).
  apply Nat.gcd_eq_0_l in H1.
Search Pos.gcd.
Print Pos.gcd.
Print Z.gcd.
Search Z.gcd.
Search Pos.gcd.
...
*)

Definition add a b :=
  let n := q_num a * q_Den b + q_num b * q_Den a in
  let d := q_Den a * q_Den b in
  mk_q (n / Z.gcd n d) (Z.to_pos (d / Z.gcd n d)) (add_prop a b).

Definition add a b :=
  let n := q_num a * q_Den b + q_num b * q_Den a in
  let d := Pos.mul (q_den a) (q_den b) in
  mk_q (n / Z.gcd n (z_pos d)) (d / Pos.gcd n d) true.

Definition opp a := mk_q (- q_num a) (q_den a).
Definition sub a b := add a (opp b).

Definition mul a b :=
  mk_q (q_num a * q_num b) (Pos.mul (q_den a) (q_den b)).

Definition inv a :=
  mk_q (Z.sgn (q_num a) * q_Den a) (Z.to_pos (Z.abs (q_num a))).

Definition div a b := mul a (inv b).

Definition compare a b :=
  q_num a * q_Den b ?= q_num b * q_Den a.

Definition eq a b := Q.compare a b = Eq.
Definition le a b := Q.compare a b ≠ Gt.
Definition lt a b := Q.compare a b = Lt.

Definition of_number (n : Number.int) : option Q :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos n => Some (mk_q (Z.of_nat (Nat.of_uint n)) 1)
      | Decimal.Neg n => Some (mk_q (- Z.of_nat (Nat.of_uint n)) 1)
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (a : Q) : option Number.int :=
  match q_den a with
  | 1%pos => Some (Z.to_number (q_num a))
  | _ => None
  end.

Number Notation Q of_number to_number : Q_scope.

Notation "a == b" := (Q.eq a b) (at level 70) : Q_scope.
Notation "a + b" := (Q.add a b) : Q_scope.
Notation "a - b" := (Q.sub a b) : Q_scope.
Notation "a * b" := (Q.mul a b) : Q_scope.
Notation "a / b" := (Q.div a b) : Q_scope.
Notation "- a" := (Q.opp a) : Q_scope.
Notation "a '⁻¹'" := (Q.inv a) (at level 1, format "a ⁻¹") : Q_scope.
Notation "a ≤ b" := (Q.le a b) : Q_scope.
Notation "a < b" := (Q.lt a b) : Q_scope.
Notation "a ?= b" := (Q.compare a b) : Q_scope.
Notation "a # b" := (mk_q a b) (at level 55) : Q_scope.

Theorem q_Den_mul : ∀ a b, q_Den (a * b) = (q_Den a * q_Den b)%Z.
Proof. easy. Qed.

Theorem eq_refl : ∀ a, (a == a)%Q.
Proof.
now intros; apply Z.compare_eq_iff.
Qed.

Theorem eq_symm : ∀ a b, (a == b → b == a)%Q.
Proof.
intros * H.
apply Z.compare_eq_iff in H.
apply Z.compare_eq_iff.
easy.
Qed.

Theorem eq_trans : ∀ a b c, (a == b → b == c → a == c)%Q.
Proof.
intros * Hab Hbc.
progress unfold eq in Hab, Hbc |-*.
apply Z.compare_eq_iff in Hab, Hbc.
apply Z.compare_eq_iff.
apply (f_equal (Z.mul (q_Den c))) in Hab.
apply (f_equal (Z.mul (q_Den a))) in Hbc.
do 2 rewrite (Z.mul_comm (q_Den c)) in Hab.
rewrite (Z.mul_comm (q_num b)) in Hab.
rewrite (Z.mul_comm (q_num c)) in Hbc.
do 2 rewrite Z.mul_assoc in Hbc.
rewrite Hbc in Hab.
do 2 rewrite <- (Z.mul_mul_swap _ _ (q_Den b)) in Hab.
rewrite (Z.mul_comm (q_Den a)) in Hab.
now apply Z.mul_cancel_r in Hab.
Qed.

Add Parametric Relation : Q Q.eq
  reflexivity proved by Q.eq_refl
  symmetry proved by Q.eq_symm
  transitivity proved by Q.eq_trans
  as eq_rel.

Theorem add_comm : ∀ a b, (a + b)%Q = (b + a)%Q.
Proof.
intros.
progress unfold add.
rewrite Z.add_comm.
rewrite Pos.mul_comm.
easy.
Qed.

Theorem add_assoc : ∀ a b c, (a + (b + c))%Q = ((a + b) + c)%Q.
Proof.
intros.
progress unfold Q.add.
cbn.
do 2 rewrite q_Den_num_den.
rewrite Pos.mul_assoc.
progress f_equal.
do 2 rewrite Pos2Z.inj_mul.
do 3 rewrite fold_q_Den.
do 2 rewrite Z.mul_add_distr_r.
do 2 rewrite Z.mul_assoc.
rewrite <- Z.add_assoc.
progress f_equal.
do 2 rewrite (Z.mul_mul_swap _ _ (q_Den a)).
easy.
Qed.

Theorem add_0_l : ∀ a, (0 + a)%Q = a.
Proof.
intros.
progress unfold add; cbn.
rewrite Z.mul_1_r, Pos.mul_1_l.
now destruct a.
Qed.

Theorem add_0_r : ∀ a, (a + 0)%Q = a.
Proof.
intros.
rewrite add_comm.
apply add_0_l.
Qed.

Theorem mul_comm : ∀ a b, (a * b)%Q = (b * a)%Q.
Proof.
intros.
progress unfold mul.
progress unfold Pos.mul.
now rewrite Z.mul_comm, Nat.mul_comm.
Qed.

Theorem mul_assoc : ∀ a b c, (a * (b * c))%Q = ((a * b) * c)%Q.
Proof.
intros.
progress unfold mul.
progress unfold Pos.mul; cbn.
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
now rewrite Z.mul_assoc, Nat.mul_assoc.
Qed.

Theorem mul_1_l : ∀ a, (1 * a)%Q = a.
Proof.
intros.
progress unfold mul.
rewrite Z.mul_1_l, Pos.mul_1_l.
now destruct a.
Qed.

Theorem mul_1_r : ∀ a, (a * 1)%Q = a.
Proof.
intros.
rewrite mul_comm.
apply mul_1_l.
Qed.

Theorem opp_involutive : ∀ a, (- - a)%Q = a.
Proof.
intros.
progress unfold opp; cbn.
rewrite Z.opp_involutive.
now destruct a.
Qed.

Theorem nle_gt : ∀ a b, ¬ (a ≤ b)%Q ↔ (b < a)%Q.
Proof. intros; apply Z.nle_gt. Qed.

Theorem nlt_ge : ∀ a b, ¬ (a < b)%Q ↔ (b ≤ a)%Q.
Proof. intros; apply Z.nlt_ge. Qed.

Theorem le_antisymm : ∀ a b, (a ≤ b)%Q → (b ≤ a)%Q → (a == b)%Q.
Proof.
intros * Hab Hba.
progress unfold Q.le in Hab, Hba.
progress unfold Q.eq.
apply Z.compare_le_iff in Hab, Hba.
apply Z.compare_eq_iff.
now apply Z.le_antisymm.
Qed.

Theorem le_refl : ∀ a, (a ≤ a)%Q.
Proof. intros; apply Z.le_refl. Qed.

Theorem lt_le_incl : ∀ a b, (a < b)%Q → (a ≤ b)%Q.
Proof. intros * Hab; congruence. Qed.

Theorem mul_opp_l : ∀ x y, ((- x) * y = - (x * y))%Q.
Proof.
intros.
progress unfold "*"%Q.
progress unfold Q.opp.
progress f_equal.
apply Z.mul_opp_l.
Qed.

Theorem mul_opp_r : ∀ x y, (x * - y = - (x * y))%Q.
Proof.
intros.
do 2 rewrite (Q.mul_comm x).
apply Q.mul_opp_l.
Qed.

Theorem order_eq_le_l : ∀ a b c, (a == b → c ≤ b → c ≤ a)%Q.
Proof.
intros * Heq Hle.
apply Z.compare_eq_iff in Heq.
apply Z.compare_le_iff in Hle.
apply Z.compare_le_iff.
apply (Z.mul_le_mono_pos_r (q_Den b)); [ easy | ].
rewrite (Z.mul_comm (q_num a)), <- (Z.mul_assoc (q_Den c)), Heq.
rewrite Z.mul_mul_swap, Z.mul_assoc.
rewrite (Z.mul_comm (q_Den c)).
now apply Z.mul_le_mono_pos_r.
Qed.

Theorem order_eq_le_r : ∀ a b c, (a == b → b ≤ c → a ≤ c)%Q.
Proof.
intros * Heq Hle.
apply Z.compare_eq_iff in Heq.
apply Z.compare_le_iff in Hle.
apply Z.compare_le_iff.
apply (Z.mul_le_mono_pos_r (q_Den b)); [ easy | ].
rewrite (Z.mul_comm (q_num a)), <- (Z.mul_assoc (q_Den c)), Heq.
rewrite Z.mul_mul_swap, Z.mul_assoc.
rewrite (Z.mul_comm (q_Den c)).
now apply Z.mul_le_mono_pos_r.
Qed.

Theorem sub_diag : ∀ a, (a - a == 0)%Q.
Proof.
intros.
apply Z.compare_eq_iff; cbn.
progress unfold q_Den; cbn.
rewrite Z.mul_1_r.
rewrite Z.mul_opp_l.
apply Z.add_opp_diag_r.
Qed.

Theorem add_opp_diag_l : ∀ a, (-a + a == 0)%Q.
Proof.
intros.
rewrite Q.add_comm.
apply Q.sub_diag.
Qed.

Theorem add_compat_l_if : ∀ a b c, (b == c → a + b == a + c)%Q.
Proof.
intros * Heq.
apply Z.compare_eq_iff in Heq.
apply Z.compare_eq_iff.
cbn.
do 2 rewrite (Z.mul_comm (_ + _)).
do 2 rewrite (Z.add_comm (q_num a * _)).
progress unfold Q.add.
do 2 rewrite q_Den_num_den.
do 2 rewrite Pos2Z.inj_mul.
do 3 rewrite fold_q_Den.
do 2 rewrite <- Z.mul_assoc.
progress f_equal.
do 2 rewrite Z.mul_add_distr_l.
do 4 rewrite Z.mul_assoc.
rewrite (Z.mul_comm (q_Den c)), Heq.
rewrite (Z.mul_comm (q_num c)).
progress f_equal.
rewrite Z.mul_comm, <- Z.mul_assoc.
progress f_equal.
apply Z.mul_comm.
Qed.

Theorem add_compat_r_if : ∀ a b c, (a == b → a + c == b + c)%Q.
Proof.
intros * Heq.
do 2 rewrite (Q.add_comm _ c).
now apply Q.add_compat_l_if.
Qed.

Theorem mul_compat_l : ∀ a b c, (b == c → a * b == a * c)%Q.
Proof.
intros * Heq.
apply Z.compare_eq_iff in Heq.
apply Z.compare_eq_iff; cbn.
do 2 rewrite Q.q_Den_mul.
do 2 rewrite <- Z.mul_assoc.
progress f_equal.
do 2 rewrite (Z.mul_comm (q_num _)).
do 2 rewrite <- Z.mul_assoc.
progress f_equal.
do 2 rewrite (Z.mul_comm _ (q_num _)).
easy.
Qed.

Theorem mul_compat_r : ∀ a b c, (a == b → a * c == b * c)%Q.
Proof.
intros * Heq.
do 2 rewrite (Q.mul_comm _ c).
now apply Q.mul_compat_l.
Qed.

Theorem lt_le_dec: ∀ a b, ({a < b} + {b ≤ a})%Q.
Proof.
intros.
progress unfold Q.lt, Q.le.
apply Z.lt_le_dec.
Qed.

Global Instance add_morph : Proper (Q.eq ==> Q.eq ==> Q.eq) Q.add.
Proof.
intros a b Hab c d Hcd.
transitivity (a + d)%Q.
now apply Q.add_compat_l_if.
now apply Q.add_compat_r_if.
Qed.

Global Instance opp_morph : Proper (Q.eq ==> Q.eq) Q.opp.
Proof.
intros a b Hab.
apply Z.compare_eq_iff in Hab.
apply Z.compare_eq_iff.
progress unfold Q.opp; cbn.
do 2 rewrite q_Den_num_den.
do 2 rewrite Z.mul_opp_l.
now f_equal.
Qed.

Theorem add_compat_l : ∀ a b c, (b == c ↔ a + b == a + c)%Q.
Proof.
intros.
split; intros Hbc; [ now apply Q.add_compat_l_if | ].
apply (Q.add_compat_l_if (-a)) in Hbc.
do 2 rewrite Q.add_assoc in Hbc.
rewrite Q.add_opp_diag_l in Hbc.
now do 2 rewrite Q.add_0_l in Hbc.
Qed.

Theorem add_compat_r : ∀ a b c, (a == b ↔ a + c == b + c)%Q.
Proof.
intros.
do 2 rewrite (Q.add_comm _ c).
now apply Q.add_compat_l.
Qed.

Theorem sub_compat_l : ∀ a b c, (b == c → a - b == a - c)%Q.
Proof.
intros * Heq.
progress unfold Q.sub.
apply Q.add_compat_l.
now rewrite Heq.
Qed.

Theorem sub_compat_r : ∀ a b c, (a == b → a - c == b - c)%Q.
Proof.
intros * Heq.
progress unfold Q.sub.
do 2 rewrite (Q.add_comm _ (- c)).
now apply Q.add_compat_l.
Qed.

Global Instance sub_morph : Proper (Q.eq ==> Q.eq ==> Q.eq) Q.sub.
Proof.
intros a b Hab c d Hcd.
transitivity (a - d)%Q.
now apply Q.sub_compat_l.
now apply Q.sub_compat_r.
Qed.

Global Instance mul_morph : Proper (Q.eq ==> Q.eq ==> Q.eq) Q.mul.
Proof.
intros a b Hab c d Hcd.
transitivity (a * d)%Q.
now apply Q.mul_compat_l.
now apply Q.mul_compat_r.
Qed.

Global Instance inv_morph : Proper (Q.eq ==> Q.eq) Q.inv.
Proof.
intros a b Hab.
apply Z.compare_eq_iff in Hab.
apply Z.compare_eq_iff; cbn.
progress unfold Q.inv; cbn.
do 2 rewrite q_Den_num_den.
destruct (Z.eq_dec (q_num a) 0) as [Haz| Haz]. {
  rewrite Haz in Hab |-*.
  cbn in Hab |-*.
  symmetry in Hab.
  apply Z.integral in Hab.
  cbn in Hab.
  destruct Hab as [Hab| Hab]; [ now rewrite Hab | easy ].
}
destruct (Z.eq_dec (q_num b) 0) as [Hbz| Hbz]. {
  rewrite Hbz in Hab |-*.
  cbn in Hab |-*.
  apply Z.integral in Hab.
  cbn in Hab.
  destruct Hab as [Hab| Hab]; [ now rewrite Hab | easy ].
}
rewrite Z2Pos.id. 2: {
  destruct (q_num b) as [| sb vb]; [ easy | cbn ].
  replace 1 with (Z.of_nat 1) by easy.
  apply Nat2Z.inj_le.
  progress unfold Pos.to_nat.
  apply Nat.le_add_l.
}
rewrite Z2Pos.id. 2: {
  destruct (q_num a) as [| sa va]; [ easy | cbn ].
  replace 1 with (Z.of_nat 1) by easy.
  apply Nat2Z.inj_le.
  progress unfold Pos.to_nat.
  apply Nat.le_add_l.
}
(**)
do 2 rewrite <- Z.mul_assoc.
f_equal. {
  apply (f_equal Z.sgn) in Hab.
  do 2 rewrite Z.sgn_mul in Hab.
  progress unfold q_Den in Hab.
  now do 2 rewrite Z.mul_1_r in Hab.
}
do 2 rewrite (Z.mul_comm (q_Den _)).
symmetry.
destruct (Z.le_dec (q_num a) 0) as [Haz1| Haz1]. {
  rewrite (Z.abs_nonpos_eq (q_num a)); [ | easy ].
  rewrite Z.mul_opp_l.
  destruct (Z.le_dec (q_num b) 0) as [Hbz1| Hbz1]. {
    rewrite (Z.abs_nonpos_eq (q_num b)); [ | easy ].
    rewrite Z.mul_opp_l.
    now f_equal.
  } {
    exfalso.
    apply Z.nle_gt in Hbz1.
    apply Z.nlt_ge in Haz1.
    apply Haz1; clear Haz1.
    apply (Z.mul_lt_mono_pos_r (q_Den b)); [ easy | ].
    rewrite Hab; cbn.
    now apply Z.mul_pos_pos.
  }
}
destruct (Z.le_dec (q_num b) 0) as [Hbz1| Hbz1]. {
  exfalso.
  apply Haz1; clear Haz1.
  apply (Z.mul_le_mono_pos_r (q_Den b)); [ easy | ].
  rewrite Hab; cbn.
  apply Z.mul_nonpos_nonneg; [ easy | apply q_Den_nonneg ].
}
apply Z.nle_gt, Z.lt_le_incl in Haz1, Hbz1.
rewrite Z.abs_nonneg_eq; [ | easy ].
rewrite Z.abs_nonneg_eq; [ | easy ].
easy.
Qed.

Global Instance div_morph : Proper (Q.eq ==> Q.eq ==> Q.eq) Q.div.
Proof.
intros a b Hab c d Hcd.
progress unfold Q.div.
transitivity (a * d⁻¹)%Q; [ | now apply Q.mul_compat_r ].
rewrite Hcd.
apply Q.mul_compat_l.
apply Q.eq_refl.
Qed.

Global Instance le_morph : Proper (Q.eq ==> Q.eq ==> iff) Q.le.
Proof.
intros a b Hab c d Hcd.
move c before b; move d before c.
split; intros Hac. {
  apply (@Q.order_eq_le_l _ c); [ now symmetry | ].
  now apply (@Q.order_eq_le_r _ a).
} {
  apply (@Q.order_eq_le_r _ b); [ easy | ].
  now apply (@Q.order_eq_le_l _ d).
}
Qed.

Theorem lt_iff : ∀ a b, (a < b)%Q ↔ (a ≤ b)%Q ∧ ¬ (a == b)%Q.
Proof.
intros.
split. {
  intros Hlt.
  split; [ now apply Q.lt_le_incl | ].
  intros H.
  apply Q.nle_gt in Hlt.
  apply Hlt; clear Hlt.
  rewrite H.
  apply Q.le_refl.
} {
  intros (Hle, Heq).
  apply Q.nle_gt.
  intros H; apply Heq; clear Heq.
  now apply Q.le_antisymm.
}
Qed.

Theorem order_eq_lt_l : ∀ a b c, (a == b → c < b → c < a)%Q.
Proof.
intros * Heq Hlt.
generalize Hlt; intros Hle.
apply Q.lt_le_incl in Hle.
apply Q.lt_iff.
split; [ now apply (Q.order_eq_le_l _ b) | ].
intros H.
rewrite <- H in Heq.
clear a H Hle.
apply Q.nle_gt in Hlt.
apply Hlt; clear Hlt.
rewrite Heq.
apply Q.le_refl.
Qed.

Theorem order_eq_lt_r : ∀ a b c, (a == b → b < c → a < c)%Q.
Proof.
intros * Heq Hlt.
generalize Hlt; intros Hle.
apply Q.lt_le_incl in Hle.
apply Q.lt_iff.
split; [ now apply (Q.order_eq_le_r _ b) | ].
intros H.
rewrite H in Heq.
clear a H Hle.
apply Q.nle_gt in Hlt.
apply Hlt; clear Hlt.
rewrite Heq.
apply Q.le_refl.
Qed.

Theorem compare_eq_iff : ∀ a b, (a ?= b)%Q = Eq ↔ (a == b)%Q.
Proof. easy. Qed.

Theorem compare_lt_iff : ∀ a b, (a ?= b)%Q = Lt ↔ (a < b)%Q.
Proof. easy. Qed.

Theorem compare_le_iff : ∀ a b, (a ?= b)%Q ≠ Gt ↔ (a ≤ b)%Q.
Proof. easy. Qed.

Theorem compare_gt_iff : ∀ a b, (a ?= b)%Q = Gt ↔ (b < a)%Q.
Proof. intros; apply Z.compare_gt_iff. Qed.

Global Instance lt_morph : Proper (Q.eq ==> Q.eq ==> iff) Q.lt.
Proof.
intros a b Hab c d Hcd.
move c before b; move d before c.
split; intros Hac. {
  apply (@Q.order_eq_lt_l _ c); [ now symmetry | ].
  now apply (@Q.order_eq_lt_r _ a).
} {
  apply (@Q.order_eq_lt_r _ b); [ easy | ].
  now apply (@Q.order_eq_lt_l _ d).
}
Qed.

Global Instance compare_morph : Proper (Q.eq ==> Q.eq ==> Logic.eq) Q.compare.
Proof.
intros a b Hab c d Hcd.
move c before b; move d before c.
remember (b ?= d)%Q as e eqn:He.
symmetry in He.
destruct e. {
  apply Q.compare_eq_iff in He.
  apply Q.compare_eq_iff.
  transitivity b; [ easy | ].
  transitivity d; [ easy | ].
  easy.
} {
  apply -> Q.compare_lt_iff in He.
  apply Q.compare_lt_iff.
  now rewrite Hab, Hcd.
} {
  apply Q.compare_gt_iff in He.
  apply Q.compare_gt_iff.
  now rewrite Hab, Hcd.
}
Qed.

Theorem le_trans : ∀ a b c, (a ≤ b → b ≤ c → a ≤ c)%Q.
Proof.
intros * Hle1 Hle2.
apply (Z.mul_le_mono_pos_r (q_Den b)); [ easy | ].
rewrite Z.mul_mul_swap.
apply (Z.le_trans _ (q_num b * q_Den a * q_Den c)). {
  now apply Z.mul_le_mono_pos_r.
}
do 2 rewrite (Z.mul_mul_swap _ (q_Den a)).
now apply Z.mul_le_mono_pos_r.
Qed.

Theorem lt_trans : ∀ a b c, (a < b → b < c → a < c)%Q.
Proof.
intros * Hab Hbc.
apply (Z.mul_lt_mono_pos_r (q_Den b)); [ easy | ].
rewrite Z.mul_mul_swap.
apply (Z.lt_trans _ (q_num b * q_Den a * q_Den c)). {
  now apply Z.mul_lt_mono_pos_r.
}
do 2 rewrite (Z.mul_mul_swap _ (q_Den a)).
now apply Z.mul_lt_mono_pos_r.
Qed.

Theorem lt_le_trans : ∀ a b c, (a < b → b ≤ c → a < c)%Q.
Proof.
intros * Hab Hbc.
apply (Z.mul_lt_mono_pos_r (q_Den b)); [ easy | ].
rewrite Z.mul_mul_swap.
apply (Z.lt_le_trans _ (q_num b * q_Den a * q_Den c)). {
  now apply Z.mul_lt_mono_pos_r.
}
do 2 rewrite (Z.mul_mul_swap _ (q_Den a)).
now apply Z.mul_le_mono_pos_r.
Qed.

Theorem le_lt_trans : ∀ a b c, (a ≤ b → b < c → a < c)%Q.
Proof.
intros * Hab Hbc.
apply (Z.mul_lt_mono_pos_r (q_Den b)); [ easy | ].
rewrite Z.mul_mul_swap.
apply (Z.le_lt_trans _ (q_num b * q_Den a * q_Den c)). {
  now apply Z.mul_le_mono_pos_r.
}
do 2 rewrite (Z.mul_mul_swap _ (q_Den a)).
now apply Z.mul_lt_mono_pos_r.
Qed.

Add Parametric Relation : Q Q.le
  reflexivity proved by Q.le_refl
  transitivity proved by Q.le_trans
  as le_rel.

Add Parametric Relation : Q Q.lt
  transitivity proved by Q.lt_trans
  as lt_rel.

Theorem compare_add_mono_l : ∀ a b c, (a + b ?= a + c)%Q = (b ?= c)%Q.
Proof.
intros.
progress unfold Q.compare.
progress unfold Q.add; cbn.
do 2 rewrite q_Den_num_den.
do 2 rewrite Pos2Z.inj_mul.
do 3 rewrite fold_q_Den.
do 2 rewrite (Z.mul_comm (q_Den a)).
do 2 rewrite Z.mul_assoc.
rewrite Z.compare_mul_mono_pos_r; [ | easy ].
do 2 rewrite Z.mul_add_distr_r.
rewrite Z.mul_mul_swap.
rewrite Z.compare_add_mono_l.
do 2 rewrite (Z.mul_mul_swap _ (q_Den a)).
now apply Z.compare_mul_mono_pos_r.
Qed.

Theorem compare_add_mono_r : ∀ a b c, (a + c ?= b + c)%Q = (a ?= b)%Q.
Proof.
intros.
do 2 rewrite (Q.add_comm _ c).
apply Q.compare_add_mono_l.
Qed.

Theorem add_le_mono_l : ∀ a b c, (b ≤ c ↔ a + b ≤ a + c)%Q.
Proof.
intros.
split; intros H. {
  apply Q.compare_le_iff in H.
  apply -> Q.compare_le_iff.
  intros H1; apply H; clear H.
  rewrite <- H1; symmetry.
  apply Q.compare_add_mono_l.
} {
  apply Q.compare_le_iff in H.
  apply -> Q.compare_le_iff.
  intros H1; apply H; clear H.
  rewrite <- H1.
  apply Q.compare_add_mono_l.
}
Qed.

Theorem add_le_mono_r : ∀ a b c, (a ≤ b ↔ a + c ≤ b + c)%Q.
Proof.
intros.
do 2 rewrite (Q.add_comm _ c).
now apply Q.add_le_mono_l.
Qed.

Theorem add_le_compat : ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%Q.
Proof.
intros * Hle1 Hle2.
apply (Q.le_trans _ (a + d)).
apply Q.add_le_mono_l, Hle2.
apply Q.add_le_mono_r, Hle1.
Qed.

Theorem add_lt_mono_l : ∀ a b c, (b < c ↔ a + b < a + c)%Q.
Proof.
intros.
split; intros H. {
  apply Q.compare_lt_iff in H.
  apply -> Q.compare_lt_iff.
  rewrite <- H.
  apply Q.compare_add_mono_l.
} {
  apply Q.compare_lt_iff in H.
  apply -> Q.compare_lt_iff.
  rewrite <- H; symmetry.
  apply Q.compare_add_mono_l.
}
Qed.

Theorem add_lt_mono_r : ∀ a b c, (a < b ↔ a + c < b + c)%Q.
Proof.
intros.
do 2 rewrite (Q.add_comm _ c).
apply Q.add_lt_mono_l.
Qed.

Theorem add_lt_le_compat : ∀ a b c d, (a < b → c ≤ d → a + c < b + d)%Q.
Proof.
intros * Hab Hcd.
apply (Q.lt_le_trans _ (b + c)).
now apply Q.add_lt_mono_r.
now apply Q.add_le_mono_l.
Qed.

Theorem lt_irrefl : ∀ a, ¬ (a < a)%Q.
Proof. intros; apply Z.lt_irrefl. Qed.

(* Some theorems working with syntactic equality,
   not only with equivalence relation in Q *)

Theorem add_sub_assoc : ∀ x y z, (x + (y - z))%Q = ((x + y) - z)%Q.
Proof.
intros.
apply Q.add_assoc.
Qed.

Theorem add_sub_swap : ∀ x y z, (x + y - z)%Q = (x - z + y)%Q.
Proof.
intros.
rewrite Q.add_comm.
rewrite <- Q.add_sub_assoc.
apply Q.add_comm.
Qed.

Theorem fold_sub : ∀ a b, (a + - b)%Q = (a - b)%Q.
Proof. easy. Qed.

Theorem opp_add_distr : ∀ a b, (- (a + b))%Q = (- a - b)%Q.
Proof.
intros.
progress unfold Q.sub.
progress unfold Q.add.
progress unfold Q.opp.
do 2 rewrite q_Den_num_den.
cbn.
rewrite (Pos.mul_comm (q_den a)).
progress f_equal.
do 2 rewrite Z.mul_opp_l.
rewrite Z.add_opp_r.
apply Z.opp_add_distr.
Qed.

Theorem opp_sub_distr : ∀ a b, (- (a - b))%Q = (b - a)%Q.
Proof.
intros.
progress unfold Q.sub.
progress unfold Q.add.
progress unfold Q.opp.
do 2 rewrite q_Den_num_den.
cbn.
rewrite (Pos.mul_comm (q_den a)).
progress f_equal.
do 2 rewrite Z.mul_opp_l.
do 2 rewrite Z.add_opp_r.
apply Z.opp_sub_distr.
Qed.

Theorem sub_sub_distr : ∀ a b c, (a - (b - c))%Q = ((a - b) + c)%Q.
Proof.
intros.
progress unfold Q.sub at 1.
rewrite Q.opp_sub_distr.
progress unfold Q.sub.
rewrite <- Q.add_assoc.
progress f_equal.
apply Q.add_comm.
Qed.

Theorem add_add_swap : ∀ a b c, (a + b + c)%Q = (a + c + b)%Q.
Proof.
intros.
do 2 rewrite <- Q.add_assoc.
progress f_equal.
apply Q.add_comm.
Qed.

Theorem mul_div_assoc : ∀ a b c, (a * (b / c))%Q = ((a * b) / c)%Q.
Proof. intros; apply Q.mul_assoc. Qed.

Theorem mul_div_swap : ∀ a b c, (a / b * c)%Q = (a * c / b)%Q.
Proof.
intros.
progress unfold Q.div.
do 2 rewrite <- Q.mul_assoc.
progress f_equal.
apply Q.mul_comm.
Qed.

Theorem opp_0 : (- 0)%Q = 0%Q.
Proof. easy. Qed.

Theorem sub_0_r : ∀ a, (a - 0)%Q = a.
Proof.
intros.
progress unfold Q.sub.
rewrite Q.opp_0.
apply Q.add_0_r.
Qed.

(* *)

Theorem add_sub: ∀ a b, (a + b - b == a)%Q.
Proof.
intros.
rewrite <- Q.add_sub_assoc.
rewrite Q.sub_diag.
now rewrite Q.add_0_r.
Qed.

Theorem sub_add : ∀ a b, (a - b + b == a)%Q.
Proof.
intros.
rewrite <- Q.add_sub_swap.
apply Q.add_sub.
Qed.

Theorem le_0_sub : ∀ a b, (0 ≤ b - a ↔ a ≤ b)%Q.
Proof.
intros.
specialize Q.add_le_compat as H1.
split; intros Hab. {
  specialize (H1 0 (b - a) a a Hab (Q.le_refl _))%Q.
  rewrite Q.sub_add in H1.
  now rewrite Q.add_0_l in H1.
} {
  specialize (H1 a b (- a) (- a) Hab (Q.le_refl _))%Q.
  rewrite Q.fold_sub in H1.
  now rewrite Q.sub_diag in H1.
}
Qed.

Theorem sub_move_0_r : ∀ a b, (a - b == 0 ↔ a == b)%Q.
Proof.
intros.
split; intros Hab; [ | rewrite Hab; apply Q.sub_diag ].
apply (Q.add_compat_r _ _ b) in Hab.
rewrite Q.sub_add in Hab.
now rewrite Q.add_0_l in Hab.
Qed.

Theorem lt_0_sub : ∀ a b, (0 < b - a ↔ a < b)%Q.
Proof.
intros.
split; intros Hab. {
  apply Q.lt_iff in Hab.
  apply Q.lt_iff.
  destruct Hab as (Hab, Habz).
  split; [ now apply Q.le_0_sub | ].
  intros H; apply Habz.
  rewrite H.
  now rewrite Q.sub_diag.
} {
  apply Q.lt_iff in Hab.
  apply Q.lt_iff.
  destruct Hab as (Hab, Habz).
  split; [ now apply Q.le_0_sub | ].
  intros H; apply Habz; clear Habz.
  symmetry in H.
  now apply -> Q.sub_move_0_r in H.
}
Qed.

Theorem add_opp_diag_r : ∀ a, (a + - a == 0)%Q.
Proof. apply Q.sub_diag. Qed.

Theorem add_move_l : ∀ a b c, (c + a == b ↔ a == b - c)%Q.
Proof.
intros.
split; intros Heq. {
  rewrite <- Heq, Q.add_comm; symmetry.
  apply Q.add_sub.
} {
  rewrite Heq, Q.add_comm.
  apply Q.sub_add.
}
Qed.

Theorem add_move_r : ∀ a b c, (a + c == b ↔ a == b - c)%Q.
Proof.
intros.
rewrite Q.add_comm.
apply Q.add_move_l.
Qed.

Definition Q1 x := (q_Den x # q_den x)%Q.

Theorem mul_add_distr_l' : ∀ x y z, (x * (y + z) * Q1 x = x * y + x * z)%Q.
Proof.
intros.
progress unfold Q.add.
progress unfold Q.mul.
cbn.
do 2 rewrite q_Den_num_den.
do 2 rewrite Pos.mul_assoc.
rewrite Pos.mul_mul_swap.
progress f_equal.
do 2 rewrite Pos2Z.inj_mul.
do 3 rewrite fold_q_Den.
do 3 rewrite <- Z.mul_assoc.
rewrite <- Z.mul_add_distr_l.
f_equal.
do 2 rewrite Z.mul_assoc.
do 2 rewrite (Z.mul_mul_swap _ (q_Den x)).
apply Z.mul_add_distr_r.
Qed.

Theorem mul_add_distr_r' : ∀ x y z, ((x + y) * z * Q1 z = x * z + y * z)%Q.
Proof.
intros.
rewrite (Q.mul_comm (_ + _)).
rewrite Q.mul_add_distr_l'.
now do 2 rewrite (Q.mul_comm z).
Qed.

Theorem mul_Q1_r : ∀ x y, (x * Q1 y == x)%Q.
Proof.
intros.
apply Z.compare_eq_iff; cbn.
rewrite <- Z.mul_assoc.
progress f_equal.
rewrite Z.mul_comm.
symmetry.
now rewrite q_Den_mul.
Qed.

(* *)

Theorem mul_add_distr_l : ∀ a b c, (a * (b + c) == a * b + a * c)%Q.
Proof.
intros.
rewrite <- Q.mul_add_distr_l'.
symmetry.
apply Q.mul_Q1_r.
Qed.

Theorem mul_add_distr_r : ∀ x y z, ((x + y) * z == x * z + y * z)%Q.
Proof.
intros.
rewrite (Q.mul_comm (_ + _)).
rewrite Q.mul_add_distr_l.
now do 2 rewrite (Q.mul_comm z).
Qed.

Theorem mul_sub_distr_l : ∀ x y z, (x * (y - z) == x * y - x * z)%Q.
Proof.
intros.
progress unfold Q.sub.
rewrite Q.mul_add_distr_l.
apply Q.add_compat_l.
now rewrite Q.mul_opp_r.
Qed.

Theorem mul_sub_distr_r : ∀ x y z, ((x - y) * z == x * z - y * z)%Q.
Proof.
intros.
rewrite (Q.mul_comm (_ - _)).
rewrite Q.mul_sub_distr_l.
now do 2 rewrite (Q.mul_comm z).
Qed.

Theorem lt_sub_lt_add_l : ∀ a b c, (a - b < c ↔ a < b + c)%Q.
Proof.
intros.
split; intros H. {
  apply (Q.add_lt_mono_r _ _ b) in H.
  rewrite Q.sub_add in H.
  now rewrite Q.add_comm in H.
} {
  apply (Q.add_lt_mono_r _ _ b).
  rewrite Q.sub_add.
  now rewrite Q.add_comm.
}
Qed.

Theorem lt_sub_lt_add_r : ∀ a b c, (a - c < b ↔ a < b + c)%Q.
Proof.
intros.
rewrite Q.add_comm.
apply Q.lt_sub_lt_add_l.
Qed.

Theorem lt_add_lt_sub_l : ∀ a b c, (a + b < c ↔ b < c - a)%Q.
Proof.
intros.
rewrite Q.add_comm.
split; intros Hlt. {
  apply (Q.add_lt_mono_r _ _ a).
  now rewrite Q.sub_add.
} {
  apply (Q.add_lt_mono_r _ _ a) in Hlt.
  now rewrite Q.sub_add in Hlt.
}
Qed.

Theorem lt_add_lt_sub_r : ∀ a b c, (a + b < c ↔ a < c - b)%Q.
Proof.
intros.
rewrite Q.add_comm.
apply Q.lt_add_lt_sub_l.
Qed.

Theorem mul_inv_diag_l : ∀ a, (¬ a == 0 → a⁻¹ * a == 1)%Q.
Proof.
intros * Hnz.
apply Z.compare_eq_iff.
apply Z.compare_neq_iff in Hnz.
rewrite Z.mul_1_r.
rewrite Z.mul_1_l.
progress unfold q_Den; cbn.
rewrite Z.mul_mul_swap.
rewrite <- Z.abs_sgn.
rewrite Pos2Z.inj_mul.
f_equal.
symmetry.
apply Z2Pos.id.
destruct a as (an, ad).
cbn in Hnz |-*.
rewrite Z.mul_1_r in Hnz.
clear ad.
apply Z.divide_pos_le. 2: {
  exists (Z.abs an); symmetry.
  apply Z.mul_1_r.
}
now apply Z.abs_pos.
Qed.

Theorem mul_inv_diag_r : ∀ a, (¬ a == 0 → a * a⁻¹ == 1)%Q.
Proof.
intros * Hnz.
rewrite Q.mul_comm.
now apply Q.mul_inv_diag_l.
Qed.

Theorem div_same : ∀ a, (¬ a == 0 → a / a == 1)%Q.
Proof. apply Q.mul_inv_diag_r. Qed.

Theorem mul_div : ∀ a b, (¬ b == 0 → a * b / b == a)%Q.
Proof.
intros * Hz.
progress unfold Q.div.
rewrite <- Q.mul_assoc.
rewrite <- (Q.mul_1_r a) at 2.
apply Q.mul_compat_l.
now apply Q.mul_inv_diag_r.
Qed.

Theorem mul_move_l : ∀ a b c, (¬ c == 0 → c * a == b ↔ a == b / c)%Q.
Proof.
intros * Hnz.
split; intros H. {
  rewrite <- H; symmetry.
  rewrite Q.mul_comm.
  now apply Q.mul_div.
} {
  rewrite H, Q.mul_comm.
  rewrite Q.mul_div_swap.
  now apply Q.mul_div.
}
Qed.

Theorem mul_move_r : ∀ a b c, (¬ c == 0 → a * c == b ↔ a == b / c)%Q.
Proof.
intros * Hnz.
rewrite Q.mul_comm.
now apply Q.mul_move_l.
Qed.

Theorem inv_add_distr : ∀ a b c, (a + b # c == (a # c) + (b # c))%Q.
Proof.
intros.
apply Z.compare_eq_iff.
progress unfold Q.add; cbn.
do 4 rewrite q_Den_num_den.
rewrite <- Z.mul_add_distr_r.
rewrite Pos2Z.inj_mul.
apply Z.mul_assoc.
Qed.

Theorem inv_sub_distr : ∀ a b c, (a - b # c == (a # c) - (b # c))%Q.
Proof.
intros.
progress unfold Z.sub.
now rewrite Q.inv_add_distr.
Qed.

Theorem apart_0_1: ¬ (1 == 0)%Q.
Proof. easy. Qed.

Theorem eq_dec : ∀ a b, ({a == b} + {¬ a == b})%Q.
Proof.
intros.
progress unfold Q.eq.
remember (a ?= b)%Q as ab eqn:Hab.
symmetry in Hab.
now destruct ab; [ left | right | right ].
Qed.

(* min/max *)

Definition min x y := if Q.lt_le_dec x y then x else y.

Theorem min_dec : ∀ n m, {Q.min n m = n} + {Q.min n m = m}.
Proof.
intros n m.
unfold Q.min.
destruct (Q.lt_le_dec n m); [ left | right ]; reflexivity.
Qed.

Theorem min_comm : ∀ n m, (Q.min n m == Q.min m n)%Q.
Proof.
intros n m.
unfold Q.min.
destruct (Q.lt_le_dec n m) as [H₁| H₁]. {
  destruct (Q.lt_le_dec m n) as [H₂| H₂]; [ idtac | reflexivity ].
  apply Q.lt_le_incl in H₂.
  now apply Q.nle_gt in H₁.
}
destruct (Q.lt_le_dec m n) as [H₂| H₂]; [ reflexivity | idtac ].
apply Q.le_antisymm; assumption.
Qed.

Theorem min_l : ∀ n m, (n ≤ m)%Q → (Q.min n m == n)%Q.
Proof.
intros n m H.
unfold Q.min.
destruct (Q.lt_le_dec n m) as [| Hge]; [ reflexivity | idtac ].
apply Q.le_antisymm; assumption.
Qed.

Theorem den_cancel : ∀ a b c, (a # c == b # c)%Q ↔ a = b.
Proof.
intros.
split; intros Hab; [ | now subst ].
progress unfold Q.eq in Hab.
progress unfold Q.compare in Hab.
cbn in Hab.
do 2 rewrite q_Den_num_den in Hab.
apply Z.compare_eq_iff in Hab.
now apply Z.mul_cancel_r in Hab.
Qed.

Theorem mul_0_l : ∀ a, (0 * a == 0)%Q.
Proof. easy. Qed.

Theorem mul_0_r : ∀ a, (a * 0 == 0)%Q.
Proof. now intros; rewrite Q.mul_comm. Qed.

End Q.

Number Notation Q Q.of_number Q.to_number : Q_scope.

Notation "a == b" := (Q.eq a b) (at level 70) : Q_scope.
Notation "a + b" := (Q.add a b) : Q_scope.
Notation "a - b" := (Q.sub a b) : Q_scope.
Notation "a * b" := (Q.mul a b) : Q_scope.
Notation "a / b" := (Q.div a b) : Q_scope.
Notation "a <= b" := (Q.le a b) : Q_scope.
Notation "a ≤ b" := (Q.le a b) : Q_scope.
Notation "a < b" := (Q.lt a b) : Q_scope.
Notation "- a" := (Q.opp a) : Q_scope.
Notation "a '⁻¹'" := (Q.inv a) (at level 1, format "a ⁻¹") : Q_scope.
Notation "a ?= b" := (Q.compare a b) : Q_scope.
Notation "a # b" := (mk_q a b) (at level 55) : Q_scope.

Notation "a ≤ b ≤ c" := (Q.le a b ∧ Q.le b c) : Q_scope.

Theorem eq_qeq : ∀ a b, a = b → (a == b)%Q.
Proof. now intros; subst. Qed.

Definition Q_ring_theory : ring_theory 0%Q 1%Q Q.add Q.mul Q.sub Q.opp Q.eq :=
  {| Radd_0_l a := eq_qeq _ _ (Q.add_0_l a);
     Radd_comm a b := eq_qeq _ _ (Q.add_comm a b);
     Radd_assoc a b c := eq_qeq _ _ (Q.add_assoc a b c);
     Rmul_1_l a := eq_qeq _ _ (Q.mul_1_l a);
     Rmul_comm a b := eq_qeq _ _ (Q.mul_comm a b);
     Rmul_assoc a b c := eq_qeq _ _ (Q.mul_assoc a b c);
     Rdistr_l := Q.mul_add_distr_r;
     Rsub_def a b := reflexivity (a + - b)%Q;
     Ropp_def := Q.add_opp_diag_r |}.

From Stdlib Require Import Ring.
Add Ring Q_ring : Q_ring_theory.

From Stdlib Require Import Field_theory.

Definition Q_field_theory :
  field_theory 0%Q 1%Q Q.add Q.mul Q.sub Q.opp Q.div Q.inv Q.eq :=
  {| F_R := Q_ring_theory;
     F_1_neq_0 := Q.apart_0_1;
     Fdiv_def a b := reflexivity _;
     Finv_l := Q.mul_inv_diag_l |}.

From Stdlib Require Import Field.
Add Field Q_field : Q_field_theory.
