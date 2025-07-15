(* integer to rational making all rationals which are always reduced
   inspired from Farey sequences *)

(*
      | (0, 1)       if n = 0
f n = | (b, a + b)   if n even and f (n / 2) = (a, b)
      | (a + b, b)   if n odd and f (n / 2) = (a, b)
*)

From Stdlib Require Import Utf8 Arith Psatz.
Import List.ListNotations.

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

Theorem f_enough_iter :
  ∀ it1 it2 n,
  n < it1
  → n < it2
  → f_aux it1 n = f_aux it2 n.
Proof.
intros * Hit1 Hit2.
revert n it2 Hit1 Hit2.
induction it1; intros; [ easy | ].
destruct it2; [ easy | ].
cbn - [ Nat.div ].
destruct n; [ easy | ].
cbn - [ Nat.div Nat.even ].
apply Nat.succ_lt_mono in Hit1, Hit2.
rewrite (IHit1 (S n / 2) it2); [ easy | | ].
apply Nat.Div0.div_lt_upper_bound; lia.
apply Nat.Div0.div_lt_upper_bound; lia.
Qed.

Theorem f_aux_f : ∀ it n, n < it → f_aux it n = f n.
Proof.
intros * Hit.
progress unfold f.
apply f_enough_iter; [ easy | ].
apply Nat.lt_succ_diag_r.
Qed.

(*
Theorem g_aux_g : ∀ it a b, max a b < it → g_aux it a b = g (a, b).
...
*)

Theorem f_g_1 : ∀ it it' n,
  n < it
  → (let '(a, b) := f n in max a b) ≤ it'
  → (let '(a, b) := f_aux it n in g_aux it' a b) = n.
Proof.
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
cbn.
induction n; [ easy | ].
cbn - [ Nat.div ].
...
