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
rewrite (IHit1 (S n / 2) it2); [ easy | | ]. {
  eapply (Nat.le_lt_trans _ n); [ | easy ].
  clear Hit1 Hit2.
  induction n; [ easy | ].
...
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  now rewrite (IHit1 0 it2).
}
rewrite (IHit1 (S n / 2) it2).

specialize (IHit1 (S n / 2) it2) as H1.
assert (H : S n / 2 < it1). {
  transitivity n; [ | easy ].

...
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst; destruct it | ].
revert n Hit Hnz.
induction it; intros; cbn - [ Nat.div ]; [ easy | ].
destruct n; [ easy | clear Hnz ].
cbn - [ Nat.div Nat.even ].
...

Theorem f_g : ∀ n, g (f n) = n.
Proof.
intros.
progress unfold f, g.
...
cbn.
induction n; [ easy | ].
cbn - [ Nat.div ].
...
