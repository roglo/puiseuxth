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

Theorem f_g_1 : ∀ n a b itf itg,
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
Search (Nat.even (S _)).
rewrite Nat.even_succ in Hen.
apply (f_equal negb) in Hen; cbn in Hen.
rewrite Nat.negb_odd in Hen.
apply Nat.even_EvenT in Hen.
destruct Hen as (n', H); subst n.
progress f_equal.
destruct a. {
  rewrite g_aux_0_l.
...
apply IHitf; [ lia | | ]. {
...
destruct n. {
  cbn in Hab.
  destruct itf; [ easy | ].
  cbn in Hab.
  injection Hab; clear Hab; intros; subst.
  apply Nat.eq_mul_0; right.
  apply g_aux_0_l.
}
rewrite Nat.even_succ_succ in Hen.
...
specialize (IHitf n a b itg) as H1.
...
eapply IHitf in Hab.
assert (H : Nat.even n = true). {
  rewrite Nat.even_succ in Hen.
  clear - Hen.
  apply Nat.EvenT_even.
  apply Nat.OddT_S_EvenT.
  apply Nat.odd_OddT.
...
  induction n; [ easy | ].
  rewrite Nat.odd_succ in Hen.
  rewrite Nat.even_succ.
  cbn.
  destruct n; [ easy | ].
  rewrite Nat.even_succ in Hen, IHn.
  rewrite Nat.odd_succ in IHn |-*.


...
specialize (IHitf (n / 2) a (S b)) as H1.
...
Print f_aux.
  destruct itf; [ easy | ].
...
  apply eq_f_aux_0_r in Hab.
lia.
...

Search (_ ≤ _ / _).
...

Theorem f_eq_g_eq : ∀ n a b,
  f n = (a, b)
  → g (a, b) = n.
Proof.
intros * Hfab.
progress unfold f in Hfab.
progress unfold g.
remember (S n) as itf.
remember (max a b) as itg.
assert (Hitf : n < itf) by lia.
assert (Hitg : max a b ≤ itg) by lia.
clear Heqitf Heqitg.
move itg before itf.
move Hfab at bottom.
...

Theorem f_g : ∀ n, g (f n) = n.
Proof.
intros.
progress unfold f, g.
remember (f_aux (S n) n) as ab eqn:Hab.
symmetry in Hab.
destruct ab as (a, b).
rewrite g_aux_g; [ | easy ].
rewrite f_aux_f in Hab; [ | lia ].
...
cbn.
induction n; [ easy | ].
cbn - [ Nat.div ].
...
