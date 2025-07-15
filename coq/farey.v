(* integer to rational making all rationals which are always reduced
   inspired from Farey sequences *)

(*
      | (0, 1)       if n = 0
f n = | (b, a + b)   if n even and f (n / 2) = (a, b)
      | (a + b, b)   if n odd and f (n / 2) = (a, b)
*)

From Stdlib Require Import Utf8 Arith.
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

Definition f n := f_aux n n.
Definition g '(a, b) := g_aux (max a b) a b.

Theorem f_g : ∀ n, g (f n) = n.
Proof.
intros.
cbn.
induction n; [ easy | ].
cbn - [ Nat.div ].
...
