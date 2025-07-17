(* integer to rational making all rationals which are always reduced
   inspired from Farey sequences *)

(*
ℕ to ℚ⁺

      | (0, 1)       if n = 0
f n = | (b, a + b)   if n even and f (n / 2) = (a, b)
      | (a + b, b)   if n odd and f (n / 2) = (a, b)

ℚ⁺ to ℕ

           | 0                    if b = 0
g (a, b) = | 2 g (b - a, a)       if a < b
           | 2 g (a - b, b) + 1   otherwise
*)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Psatz.
Import List.ListNotations.
Import Init.Nat.

Fixpoint f_aux it n :=
  match it with
  | 0 => (0, 0)
  | S it' =>
      if Nat.eq_dec n 0 then (0, 1)
      else
        let (a, b) := f_aux it' (n / 2) in
        if Nat.even n then (b, a + b)
        else (a + b, b)
  end.

Fixpoint g_aux it a b :=
  match it with
  | 0 => 0
  | S it' =>
      if Nat.eq_dec b 0 then 0
      else if lt_dec a b then 2 * g_aux it' (b - a) a
      else 2 * g_aux it' (a - b) b + 1
  end.

Definition f n := f_aux (S n) n.
Definition g '(a, b) := g_aux (max a b) a b.

Theorem g_aux_0_r : ∀ it a, g_aux it a 0 = 0.
Proof. now intros; destruct it. Qed.

Theorem g_aux_0_l : ∀ it a, g_aux it 0 a = 0.
Proof.
intros.
induction it; [ easy | ].
destruct a; [ easy | ].
cbn - [ Nat.mul ].
now rewrite g_aux_0_r.
Qed.

Theorem f_aux_f : ∀ it n, n < it → f_aux it n = f n.
Proof.
intros * Hit.
progress unfold f.
remember (S n) as it' eqn:Hit'.
assert (H : n < it') by lia.
clear Hit'; move it' before it; rename H into Hit'.
revert n it' Hit Hit'.
induction it; intros; [ easy | ].
destruct it'; [ easy | ].
cbn - [ Nat.div ].
destruct n; [ easy | ].
cbn - [ Nat.div Nat.even ].
apply Nat.succ_lt_mono in Hit, Hit'.
rewrite (IHit (S n / 2) it'); [ easy | | ].
apply Nat.Div0.div_lt_upper_bound; lia.
apply Nat.Div0.div_lt_upper_bound; lia.
Qed.

Theorem g_aux_g : ∀ it a b, max a b ≤ it → g_aux it a b = g (a, b).
Proof.
intros * Hit.
progress unfold g.
rename it into it1.
remember (max a b) as it2.
assert (Hit1 : max a b ≤ it1) by lia.
assert (Hit2 : max a b ≤ it2) by lia.
clear Heqit2 Hit.
revert a b it2 Hit1 Hit2.
induction it1; intros. {
  generalize Hit1; intros H.
  apply Nat.max_lub_l in Hit1.
  apply Nat.max_lub_r in H.
  apply Nat.le_0_r in Hit1, H; subst.
  now destruct it2.
}
destruct it2. {
  generalize Hit2; intros H.
  apply Nat.max_lub_l in Hit2.
  apply Nat.max_lub_r in H.
  now apply Nat.le_0_r in Hit2, H; subst.
}
cbn - [ Nat.div Nat.mul ].
destruct b; [ easy | ].
cbn - [ Nat.mul Nat.sub ].
destruct a. {
  cbn - [ Nat.mul ].
  f_equal.
  cbn in Hit1, Hit2.
  apply Nat.succ_le_mono in Hit1, Hit2.
  destruct it2; [ | now destruct it1 ].
  apply Nat.le_0_r in Hit2; subst.
  now destruct it1.
}
cbn in Hit1, Hit2.
apply Nat.succ_le_mono in Hit1, Hit2.
cbn - [ Nat.mul ].
destruct (lt_dec (S a) (S b)) as [Hab| Hab]. {
  apply Nat.succ_lt_mono in Hab.
  rewrite max_r in Hit1; [ | now apply Nat.lt_le_incl ].
  rewrite max_r in Hit2; [ | now apply Nat.lt_le_incl ].
  f_equal.
  destruct it2; [ lia | ].
  cbn - [ Nat.mul Nat.sub ].
  remember (b - a) as ba eqn:Hba.
  symmetry in Hba.
  destruct ba; [ lia | ].
  assert (H : b = a + S ba) by lia.
  clear Hba; subst b.
  cbn - [ Nat.mul ].
  clear Hab.
  destruct (lt_dec (S ba) (S a)) as [Hbaa| Hbaa]. {
    apply Nat.succ_lt_mono in Hbaa.
    destruct it1; [ lia | ].
    cbn - [ Nat.mul ].
    destruct (lt_dec (S ba) (S a)) as [Hbaa'| Hbaa']; [ | lia ].
    f_equal.
    rewrite <- (IHit1 _ _ it2); [ | lia | lia ].
    symmetry.
    apply IHit1; lia.
  }
  apply Nat.nlt_ge in Hbaa.
  apply Nat.succ_le_mono in Hbaa.
  rewrite (IHit1 _ _ (S it2)); [ | lia | lia ].
  cbn - [ Nat.mul ].
  destruct (lt_dec (S ba) (S a)) as [Hbaa'| Hbaa']; [ lia | easy ].
} {
  apply Nat.nlt_ge in Hab.
  apply Nat.succ_le_mono in Hab.
  f_equal; f_equal.
  rewrite max_l in Hit1; [ | easy ].
  rewrite max_l in Hit2; [ | easy ].
  destruct it2. {
    apply Nat.le_0_r in Hit2; subst a.
    apply Nat.le_0_r in Hab; subst b.
    cbn; clear.
    destruct it1; [ easy | now destruct it1 ].
  }
  cbn - [ Nat.mul Nat.sub ].
  remember (a - b) as ab eqn:Hab'.
  symmetry in Hab'.
  destruct ab. {
    cbn - [ Nat.mul ].
    now rewrite g_aux_0_l, g_aux_0_r.
  }
  assert (H : a = b + S ab) by lia.
  clear Hab'; subst a.
  cbn - [ Nat.mul ].
  clear Hab.
  destruct (lt_dec (S ab) (S b)) as [Habb| Habb]. {
    apply Nat.succ_lt_mono in Habb.
    destruct it1; [ lia | ].
    cbn - [ Nat.mul ].
    destruct (lt_dec (S ab) (S b)) as [Habb'| Habb']; [ | lia ].
    f_equal.
    rewrite <- (IHit1 _ _ it2); [ | lia | lia ].
    symmetry.
    apply IHit1; lia.
  }
  apply Nat.nlt_ge in Habb.
  apply Nat.succ_le_mono in Habb.
  rewrite (IHit1 _ _ (S it2)); [ | lia | lia ].
  cbn - [ Nat.mul ].
  destruct (lt_dec (S ab) (S b)) as [Habb'| Habb']; [ lia | easy ].
}
Qed.

Theorem eq_f_aux_0_r : ∀ it n a, f_aux it n = (a, 0) → it ≤ n.
Proof.
intros * Hit.
revert a n Hit.
induction it; intros; [ apply Nat.le_0_l | ].
cbn - [ Nat.div ] in Hit.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ easy | ].
remember (f_aux it (n / 2)) as ab eqn:Hab.
symmetry in Hab.
destruct ab as (a', b).
remember (Nat.even n) as en eqn:Hen.
symmetry in Hen.
destruct en. {
  injection Hit; clear Hit; intros H1 H2; subst b.
  apply Nat.eq_add_0 in H1; destruct H1; subst a a'.
  destruct it; [ now apply Nat.neq_0_lt_0 | ].
  apply IHit in Hab.
  clear IHit Hnz Hen.
  destruct n; [ easy | ].
  apply -> Nat.succ_le_mono.
  etransitivity; [ apply Hab | ].
  clear Hab.
  destruct n; [ easy | ].
  apply Nat.Div0.div_le_upper_bound; lia.
} {
  injection Hit; clear Hit; intros H1 H2; subst b.
  rewrite Nat.add_0_r in H2; subst a.
  destruct n; [ easy | clear Hnz ].
  apply -> Nat.succ_le_mono.
  rewrite Nat.even_succ in Hen.
  apply IHit in Hab.
  etransitivity; [ apply Hab | clear ].
  destruct n; [ easy | ].
  apply Nat.Div0.div_le_upper_bound; lia.
}
Qed.

Theorem eq_f_aux_0_l : ∀ it n a, f_aux it n = (0, a) → n = 0 ∨ it ≤ n.
Proof.
intros * Hit.
revert a n Hit.
induction it; intros; [ right; apply Nat.le_0_l | ].
cbn - [ Nat.div ] in Hit.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now left | right ].
remember (f_aux it (n / 2)) as ab eqn:Hab.
symmetry in Hab.
destruct ab as (a', b).
remember (Nat.even n) as en eqn:Hen.
symmetry in Hen.
destruct en. {
  injection Hit; clear Hit; intros; subst.
  rename a' into a.
  apply eq_f_aux_0_r in Hab.
  apply Nat.even_EvenT in Hen.
  destruct Hen as (n', H); subst n.
  rewrite Nat.mul_comm, Nat.div_mul in Hab; [ lia | easy ].
} {
  injection Hit; clear Hit; intros H1 H2; subst.
  apply Nat.eq_add_0 in H2.
  destruct H2; subst.
  apply eq_f_aux_0_r in Hab.
  destruct n; [ easy | ].
  apply -> Nat.succ_le_mono.
  rewrite Nat.even_succ in Hen.
  apply (f_equal negb) in Hen; cbn in Hen.
  rewrite Nat.negb_odd in Hen.
  apply Nat.even_EvenT in Hen.
  destruct Hen as (n', H); subst n.
  rewrite <- Nat.add_1_l in Hab.
  rewrite Nat.mul_comm, Nat.div_add in Hab; [ | easy ].
  cbn in Hab; lia.
}
Qed.

Theorem eq_g_aux_0 :
  ∀ it a b, g_aux it a b = 0 → a = 0 ∨ b = 0 ∨ it < max a b.
Proof.
intros * Hab.
revert a b Hab.
induction it; intros; cbn. {
  destruct a; [ now left | right ].
  destruct b; [ now left | right ].
  cbn; apply Nat.lt_0_succ.
}
cbn - [ Nat.mul ] in Hab.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now right; left | ].
destruct (lt_dec a b) as [Hlab| Hlab]; [ | lia ].
apply Nat.eq_mul_0_r in Hab; [ | easy ].
destruct a; [ now left | right; right ].
rewrite Nat.max_r; [ | now apply Nat.lt_le_incl ].
apply IHit in Hab; lia.
Qed.

Theorem f_aux_eq_g_aux_eq : ∀ n a b itf itg,
  n < itf
  → max a b ≤ itg
  → f_aux itf n = (a, b)
  → g_aux itg a b = n.
Proof.
intros * Hitf Hitg Hfab.
revert n a b itg Hitf Hitg Hfab.
induction itf; intros; [ easy | ].
cbn - [ Nat.div ] in Hfab.
destruct n. {
  cbn in Hfab.
  injection Hfab; clear Hfab; intros; subst; cbn.
  apply g_aux_0_l.
}
apply Nat.succ_lt_mono in Hitf.
cbn - [ Nat.div Nat.even ] in Hfab.
remember (Nat.even (S n)) as en eqn:Hen.
symmetry in Hen.
destruct en. {
  apply Nat.even_EvenT in Hen.
  destruct Hen as (n', Hn).
  remember (f_aux itf (S n / 2)) as ab' eqn:Hab'.
  symmetry in Hab'.
  destruct ab' as (a', b').
  injection Hfab; clear Hfab; intros; subst a b.
  rename a' into a; rename b' into b.
  destruct itg. {
    exfalso.
    generalize Hitg; intros H1.
    apply Nat.max_lub_l in Hitg.
    apply Nat.max_lub_r in H1.
    apply Nat.le_0_r in Hitg; subst b.
    rewrite Nat.add_0_r in H1.
    apply Nat.le_0_r in H1; subst a.
    apply eq_f_aux_0_r in Hab'.
    apply Nat.nle_gt in Hitf.
    apply Hitf; clear Hitf.
    etransitivity; [ apply Hab' | ].
    clear.
    destruct n; [ easy | ].
    apply Nat.Div0.div_le_upper_bound; lia.
  }
  cbn - [ Nat.mul ].
  rewrite Nat.add_sub.
  rewrite Nat.add_comm.
  rewrite Nat.sub_add_distr, Nat.sub_diag.
  cbn - [ Nat.mul ].
  destruct b. {
    exfalso.
    apply eq_f_aux_0_r in Hab'.
    apply Nat.nle_gt in Hitf.
    apply Hitf; clear Hitf.
    etransitivity; [ apply Hab' | ].
    clear.
    destruct n; [ easy | ].
    apply Nat.Div0.div_le_upper_bound; lia.
  }
  cbn - [ Nat.mul ].
  rewrite Hn, Nat.mul_comm, Nat.div_mul in Hab'; [ | easy ].
  destruct (lt_dec (S b) (S (b + a))) as [Hbba| Hbba]. {
    rewrite Hn.
    f_equal.
    apply IHitf; [ lia | lia | easy ].
  }
  exfalso.
  apply Nat.nlt_ge in Hbba.
  assert (Haz : a = 0) by lia.
  subst a; clear Hbba.
  destruct itf; [ easy | ].
  cbn - [ Nat.div ] in Hab'.
  destruct n'; [ easy | ].
  cbn - [ Nat.div Nat.sub ] in Hab'.
  remember (f_aux itf (S n' / 2)) as ab eqn:Hab.
  symmetry in Hab.
  destruct ab as (a, b').
  destruct n'. {
    injection Hab'; clear Hab'; intros; subst; lia.
  }
  remember (Nat.even n') as en eqn:Hen.
  symmetry in Hen.
  destruct en. {
    injection Hab'; clear Hab'; intros H1 H2; subst b'.
    progress replace (S (S n')) with (n' + 1 * 2) in Hab by lia.
    rewrite Nat.div_add in Hab; [ | easy ].
    rewrite Nat.add_1_r in Hab.
    destruct itf. {
      cbn in Hab.
      now injection Hab; clear Hab; intros; subst a.
    }
    apply eq_f_aux_0_r in Hab.
    apply Nat.succ_le_mono in Hab.
    apply (Nat.mul_le_mono_l _ _ 2) in Hab.
    rewrite <- Nat.Lcm0.divide_div_mul_exact in Hab. 2: {
      apply Nat.even_EvenT in Hen.
      destruct Hen as (c, Hc); subst n'.
      exists c.
      apply Nat.mul_comm.
    }
    rewrite (Nat.mul_comm _ n'), Nat.div_mul in Hab; [ lia | easy ].
  }
  injection Hab'; clear Hab'; intros H1 H2; subst b'; lia.
}
destruct itg. {
  exfalso.
  generalize Hitg; intros H.
  apply Nat.max_lub_l in Hitg.
  apply Nat.max_lub_r in H.
  apply Nat.le_0_r in Hitg, H; subst.
  remember (f_aux itf (S n / 2)) as ab eqn:Hab.
  symmetry in Hab.
  destruct ab as (a, b).
  injection Hfab; clear Hfab; intros H1 H2; subst b.
  rewrite Nat.add_0_r in H2; subst a.
  apply eq_f_aux_0_r in Hab.
  apply Nat.nle_gt in Hitf.
  apply Hitf; clear Hitf.
  etransitivity; [ apply Hab | ].
  destruct n; [ easy | ].
  progress replace (S (S n)) with (n + 1 * 2) by lia.
  rewrite Nat.div_add; [ | easy ].
  rewrite Nat.add_1_r.
  apply -> Nat.succ_le_mono.
  apply Nat.Div0.div_le_upper_bound; lia.
}
remember (f_aux itf (S n / 2)) as ab eqn:Hab.
symmetry in Hab.
destruct ab as (a', b').
injection Hfab; clear Hfab; intros H1 H2; subst b' a.
rename a' into a.
cbn - [ Nat.mul ].
destruct b. {
  exfalso.
  apply eq_f_aux_0_r in Hab.
  apply Nat.nle_gt in Hitf.
  apply Hitf; clear Hitf.
  etransitivity; [ apply Hab | ].
  destruct n; [ easy | ].
  progress replace (S (S n)) with (n + 1 * 2) by lia.
  rewrite Nat.div_add; [ | easy ].
  rewrite Nat.add_1_r.
  apply -> Nat.succ_le_mono.
  apply Nat.Div0.div_le_upper_bound; lia.
}
cbn - [ Nat.mul ].
rewrite Nat.add_succ_r.
rewrite Nat.add_comm, Nat.sub_add_distr, Nat.sub_diag.
rewrite <- Nat.add_succ_l, (Nat.add_comm (S b)), Nat.add_sub.
cbn - [ Nat.mul ].
destruct (lt_dec (a + S b) (S b)) as [Hasb| Hasb]; [ lia | ].
clear Hasb.
rewrite Nat.add_1_r.
progress f_equal.
rewrite Nat.even_succ in Hen.
apply (f_equal negb) in Hen; cbn in Hen.
rewrite Nat.negb_odd in Hen.
apply Nat.even_EvenT in Hen.
destruct Hen as (n', H); subst n.
progress f_equal.
destruct a. {
  rewrite g_aux_0_l.
  destruct n'; [ easy | exfalso ].
  rewrite <- Nat.add_1_l in Hab.
  rewrite Nat.mul_comm, Nat.div_add in Hab; [ | easy ].
  cbn in Hab.
  apply eq_f_aux_0_l in Hab.
  destruct Hab as [Hab| Hab]; [ easy | lia ].
}
apply IHitf; [ lia | lia | ].
rewrite <- Nat.add_1_l in Hab.
now rewrite Nat.mul_comm, Nat.div_add in Hab.
Qed.

Theorem g_aux_eq_f_aux_eq : ∀ n a b itf itg,
  b ≠ 0
  → n < itf
  → max a b ≤ itg
  → g_aux itg a b = n
  → f_aux itf n = (a / Nat.gcd a b, b / Nat.gcd a b).
Proof.
intros * Hbz Hitf Hitg Hab.
revert n a b Hbz itf Hitf Hitg Hab.
induction itg; intros. {
  cbn in Hab; subst n.
  apply Nat.max_lub_r in Hitg.
  now apply Nat.le_0_r in Hitg.
}
cbn - [ Nat.mul ] in Hab.
destruct (Nat.eq_dec b 0) as [H| H]; [ easy | clear H ].
destruct (lt_dec a b) as [Hlab| Hlab]. {
  rewrite Nat.max_r in Hitg; [ | now apply Nat.lt_le_incl ].
  destruct itf; [ easy | ].
  cbn - [ Nat.div ].
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    move Hnz at top; subst n.
    clear Hitf.
    apply Nat.mul_eq_0_r in Hab; [ | easy ].
    apply eq_g_aux_0 in Hab.
    destruct Hab as [Hab| Hab]; [ lia | ].
    destruct Hab as [Hab| Hab]. {
      subst a; cbn.
      rewrite Nat.Div0.div_0_l.
      f_equal; symmetry.
      now apply Nat.div_same.
    }
    destruct (le_dec (b - a) a) as [Hbba| Hbba]; [ lia | ].
    apply Nat.nle_gt in Hbba.
    rewrite Nat.max_l in Hab; [ | now apply Nat.lt_le_incl ].
    destruct a; [ | lia ].
    cbn.
    rewrite Nat.Div0.div_0_l.
    f_equal; symmetry.
    now apply Nat.div_same.
  }
  remember (f_aux itf (n / 2)) as ab eqn:Hab'.
  symmetry in Hab'.
  destruct ab as (a', b').
  remember (Nat.even n) as en eqn:Hen.
  symmetry in Hen.
  destruct en. {
    apply Nat.even_EvenT in Hen.
    destruct Hen as (n', H).
    move H at top; subst n; rename n' into n.
    apply Nat.mul_reg_l in Hab; [ | easy ].
    apply Nat.neq_mul_0 in Hnz.
    destruct Hnz as (_, Hnz).
    rewrite Nat.mul_comm, Nat.div_mul in Hab'; [ | easy ].
    destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
      subst a; cbn.
      now rewrite g_aux_0_r in Hab; symmetry in Hab.
    }
    apply IHitg with (itf := itf) in Hab; [ | easy | lia | lia ].
    rewrite Nat.gcd_comm in Hab.
    rewrite Nat.gcd_sub_diag_r in Hab; [ | now apply Nat.lt_le_incl ].
    rewrite Hab in Hab'.
    injection Hab'; clear Hab'; intros; subst a' b'.
    progress f_equal.
    specialize (Nat.gcd_divide_l a b) as H1.
    specialize (Nat.gcd_divide_r a b) as H2.
    destruct H1 as (a', Ha).
    destruct H2 as (b', Hb).
    rewrite Ha at 1 3.
    rewrite Nat.div_mul; [ | now intros H; apply Nat.gcd_eq_0_l in H ].
    rewrite Hb at 1 4.
    rewrite Nat.div_mul; [ | now intros H; apply Nat.gcd_eq_0_l in H ].
    rewrite <- Nat.mul_sub_distr_r.
    rewrite Nat.div_mul; [ | now intros H; apply Nat.gcd_eq_0_l in H ].
    apply Nat.sub_add.
    apply (Nat.mul_le_mono_pos_r _ _ (Nat.gcd a b)); [ | lia ].
    apply Nat.neq_0_lt_0.
    now intros H; apply Nat.gcd_eq_0_l in H.
  }
  destruct n; [ easy | clear Hnz ].
  rewrite Nat.even_succ in Hen.
  apply (f_equal negb) in Hen; cbn in Hen.
  rewrite Nat.negb_odd in Hen.
  apply Nat.even_EvenT in Hen.
  destruct Hen as (n', H); subst n.
  lia.
}
apply Nat.nlt_ge in Hlab.
rewrite Nat.max_l in Hitg; [ | easy ].
destruct n; [ lia | ].
rewrite Nat.add_1_r in Hab.
apply Nat.succ_inj in Hab.
destruct itf; [ easy | ].
apply Nat.succ_lt_mono in Hitf.
destruct n. {
  apply Nat.eq_mul_0_r in Hab; [ | easy ].
  apply eq_g_aux_0 in Hab.
  destruct Hab as [Hab| Hab]. {
    replace b with a in * by lia.
    clear Hlab Hab.
    rewrite Nat.gcd_diag.
    rewrite Nat.div_same; [ | easy ].
    now destruct itf.
  }
  destruct Hab as [Hab| Hab]; [ easy | ].
  destruct (le_dec (a - b) b) as [Habb| Habb]; [ | lia ].
  rewrite Nat.max_r in Hab; [ | easy ].
  replace b with a in * by lia.
  clear Hlab Habb.
  rewrite Nat.gcd_diag.
  rewrite Nat.div_same; [ | easy ].
  now destruct itf.
}
cbn - [ Nat.div ].
remember (f_aux itf (S (S n) / 2)) as ab eqn:Hab'.
symmetry in Hab'.
destruct ab as (a', b').
remember (Nat.even n) as en eqn:Hen.
symmetry in Hen.
destruct en. {
  apply Nat.even_EvenT in Hen.
  destruct Hen as (n', H); lia.
}
destruct n; [ easy | ].
rewrite Nat.even_succ in Hen.
apply (f_equal negb) in Hen; cbn in Hen.
rewrite Nat.negb_odd in Hen.
apply Nat.even_EvenT in Hen.
destruct Hen as (n', H); subst n; rename n' into n.
replace (S (S (2 * n))) with (2 * (S n)) in Hab by lia.
apply Nat.mul_reg_l in Hab; [ | easy ].
replace (S (S (S (2 * n)))) with (1 + S n * 2) in Hab' by lia.
rewrite Nat.div_add in Hab'; [ | easy ].
cbn in Hab'.
destruct (Nat.eq_dec b (S itg)) as [Hbitg| Hbitg]. {
  rewrite <- Hbitg in Hitg.
  apply Nat.le_antisymm in Hlab; [ | easy ].
  subst b; clear Hitg.
  rewrite Nat.sub_diag in Hab.
  now rewrite g_aux_0_l in Hab.
}
apply IHitg with (itf := itf) in Hab; [ | easy | lia | lia ].
rewrite Nat.gcd_comm in Hab.
rewrite Nat.gcd_sub_diag_r in Hab; [ | easy ].
rewrite Hab in Hab'.
injection Hab'; clear Hab'; intros; subst.
rewrite (Nat.gcd_comm b).
progress f_equal.
specialize (Nat.gcd_divide_l a b) as H1.
specialize (Nat.gcd_divide_r a b) as H2.
destruct H1 as (a', Ha).
destruct H2 as (b', Hb).
rewrite Hb at 1 3.
rewrite Nat.div_mul; [ | now intros H; apply Nat.gcd_eq_0_r in H ].
rewrite Ha at 1 4.
rewrite Nat.div_mul; [ | now intros H; apply Nat.gcd_eq_0_r in H ].
rewrite <- Nat.mul_sub_distr_r.
rewrite Nat.div_mul; [ | now intros H; apply Nat.gcd_eq_0_r in H ].
apply Nat.sub_add.
apply (Nat.mul_le_mono_pos_r _ _ (Nat.gcd a b)); [ | lia ].
apply Nat.neq_0_lt_0.
now intros H; apply Nat.gcd_eq_0_r in H.
Qed.

Theorem f_eq_g_eq : ∀ n a b,
  f n = (a, b)
  → g (a, b) = n.
Proof.
intros * Hfab.
apply (f_aux_eq_g_aux_eq _ _ _ (S n)); [ lia | easy | easy ].
Qed.

Theorem g_eq_f_eq : ∀ n a b,
  b ≠ 0
  → g (a, b) = n
  → f n = (a / Nat.gcd a b, b / Nat.gcd a b).
Proof.
intros * Hbz Hfab.
now apply (g_aux_eq_f_aux_eq _ _ _ _ (max a b)); [ | lia | | ].
Qed.

Theorem f_g : ∀ n, g (f n) = n.
Proof.
intros.
progress unfold f, g.
remember (f_aux (S n) n) as ab eqn:Hab.
symmetry in Hab.
destruct ab as (a, b).
now apply f_eq_g_eq.
Qed.

Theorem g_f :
  ∀ a b,
  f (g (a, b)) =
    if Nat.eq_dec b 0 then (0, 1) else (a / Nat.gcd a b, b / Nat.gcd a b).
Proof.
intros.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  subst.
  progress unfold g.
  now rewrite g_aux_0_r.
}
progress unfold f, g.
remember (g_aux (max a b) a b) as n eqn:Hn.
symmetry in Hn.
now apply g_eq_f_eq.
Qed.
