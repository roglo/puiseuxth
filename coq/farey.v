(* integer to rational making all rationals which are always reduced
   inspired from Farey sequences *)

(*
      | (0, 1)       if n = 0
f n = | (b, a + b)   if n even and f (n / 2) = (a, b)
      | (a + b, b)   if n odd and f (n / 2) = (a, b)
*)

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
      match a with
      | 0 => 0
      | S a' =>
          match b with
          | 0 => 0
          | S b' =>
              if lt_dec a b then 2 * g_aux it' (b - a) a
              else 2 * g_aux it' (a - b) b + 1
          end
      end
  end.

Definition f n := f_aux (S n) n.
Definition g '(a, b) := g_aux (max a b) a b.

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
destruct a; [ easy | ].
destruct b; [ easy | ].
cbn in Hit1, Hit2.
apply Nat.succ_le_mono in Hit1, Hit2.
cbn - [ Nat.mul ].
destruct (lt_dec (S a) (S b)) as [Hab| Hab]. {
  apply Nat.succ_lt_mono in Hab.
  rewrite max_r in Hit1; [ | now apply Nat.lt_le_incl ].
  rewrite max_r in Hit2; [ | now apply Nat.lt_le_incl ].
  f_equal.
  destruct it2; [ lia | ].
  cbn - [ Nat.mul ].
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
    now destruct it1.
  }
  cbn - [ Nat.mul ].
  remember (a - b) as ab eqn:Hab'.
  symmetry in Hab'.
  destruct ab; [ now destruct it1 | ].
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

Definition maxf n := max (fst (f n)) (snd (f n)).

(**)
Theorem f_g_1 : ∀ it it' n,
  n < it
  → (let '(a, b) := f n in max a b) ≤ it'
  → (let '(a, b) := f_aux it n in g_aux it' a b) = n.
Proof.
Admitted. (*
(*
intros * Hit Hit'.
rewrite f_aux_f; [ | easy ].
remember (f n) as ab eqn:Hab.
symmetry in Hab.
destruct ab as (a, b).
...
*)
intros * Hit Hit'.
revert n it' Hit Hit'.
induction it; intros; [ easy | ].
cbn - [ Nat.div ].
destruct n; [ now destruct it' | ].
apply Nat.succ_lt_mono in Hit.
cbn - [ Nat.div ].
destruct n. {
  cbn in Hit' |-*.
  destruct it; [ easy | ].
  destruct it'; [ easy | ].
  now destruct it'.
}
...
destruct n; [ now rewrite f_aux_f | ].
rewrite f_aux_f. 2: {
  apply Nat.Div0.div_lt_upper_bound; lia.
}
specialize (IHit (S (S n) / 2)) as H1.
assert (H : S (S n) / 2 < it). {
  apply Nat.Div0.div_lt_upper_bound; lia.
}
specialize (H1 H); clear H.
rewrite f_aux_f in H1. 2: {
  apply Nat.Div0.div_lt_upper_bound; lia.
}
remember (f (S (S n) / 2)) as x eqn:Hx.
symmetry in Hx.
destruct x as (a, b).
remember (Nat.even n) as en eqn:Hen.
symmetry in Hen.
destruct en. {
  apply Nat.even_EvenT in Hen.
  destruct Hen as (n', Hn); subst n.
...
*)

Theorem f_g : ∀ n, g (f n) = n.
Proof.
intros.
progress unfold f, g.
...
(*
remember (f_aux (S n) n) as ab eqn:Hab.
symmetry in Hab.
destruct ab as (a, b).
rewrite g_aux_g; [ | easy ].
rewrite f_aux_f in Hab; [ | lia ].
*)
...
cbn.
induction n; [ easy | ].
cbn - [ Nat.div ].
...
