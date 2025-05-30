Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

(*
  3  is represented by mk_z true 3
  0  is represented by mk_z true 0
  -1 is represented by mk_z false 0
  -5 is represented by mk_z false 4

i.e.
  mk_z s n = n       if s = true
          = -n-1     if s = false
*)
Record Z := mk_z { z_sign : bool; z_val : nat }.

Declare Scope Z_scope.
Delimit Scope Z_scope with Z.
Bind Scope Z_scope with Z.

(* misc theorems *)

Theorem Bool_eqb_comm : ∀ a b, Bool.eqb a b = Bool.eqb b a.
Proof.
intros.
progress unfold Bool.eqb.
now destruct a, b.
Qed.

(* to be removed if RingLike included *)
Theorem if_ltb_lt_dec : ∀ A i j (a b : A),
  (if i <? j then a else b) = (if lt_dec i j then a else b).
Proof.
intros.
destruct (lt_dec i j) as [H1| H1]. {
  now apply Nat.ltb_lt in H1; rewrite H1.
}
now apply Nat.ltb_nlt in H1; rewrite H1.
Qed.

(* to be removed if RingLike included *)
Theorem if_leb_le_dec : ∀ A i j (a b : A),
  (if i <=? j then a else b) = (if le_dec i j then a else b).
Proof.
intros.
destruct (le_dec i j) as [H1| H1]. {
  now apply Nat.leb_le in H1; rewrite H1.
}
now apply Nat.leb_nle in H1; rewrite H1.
Qed.

(* to be removed if RingLike included *)
Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

(* end misc theorems *)

Module Z.

Definition of_nat := mk_z true.

Definition abs_nat a :=
  match z_sign a with
  | true => z_val a
  | false => z_val a + 1
  end.

Definition add a b :=
  match z_sign a with
  | true =>
      match z_sign b with
      | true => mk_z true (z_val a + z_val b)
      | false =>
          if z_val b <? z_val a then mk_z true (z_val a - z_val b - 1)
          else mk_z false (z_val b - z_val a)
       end
  | false =>
      match z_sign b with
      | true =>
          if z_val a <? z_val b then mk_z true (z_val b - z_val a - 1)
          else mk_z false (z_val a - z_val b)
      | false => mk_z false (z_val a + z_val b + 1)
      end
  end.

Definition opp a :=
  match z_sign a with
  | true => if z_val a =? 0 then a else mk_z false (z_val a - 1)
  | false => mk_z true (z_val a + 1)
  end.

Definition mul a b :=
  let v := abs_nat a * abs_nat b in
  if Nat.eq_dec v 0 then
    mk_z true 0
  else if Bool.bool_dec (z_sign a) (z_sign b) then
    mk_z true v
  else
    mk_z false (v - 1).

Definition compare a b :=
  if z_sign a then
    if z_sign b then z_val a ?= z_val b else Gt
  else
    if z_sign b then Lt else z_val b ?= z_val a.

Theorem add_comm : ∀ a b, add a b = add b a.
Proof.
intros.
progress unfold add.
rewrite (Nat.add_comm (z_val b)).
destruct (z_sign a); [ now destruct (z_sign b) | easy ].
Qed.

(*
Theorem mul_comm : ∀ a b, mul a b = mul b a.
Proof.
intros.
destruct a as (sa, va).
destruct b as (sb, vb).
progress unfold mul.
cbn.
rewrite Bool_eqb_comm.
rewrite Nat.mul_comm.
easy.
Qed.
*)

Theorem mul_add_distr_l : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c).
Proof.
intros.
destruct a as (sa, va).
destruct b as (sb, vb).
destruct c as (sc, vc).
progress unfold add.
progress unfold mul.
do 4 rewrite if_ltb_lt_dec.
cbn.
destruct sa; cbn - [ Nat.eq_dec Bool.bool_dec ]. {
  destruct sb; cbn - [ Nat.eq_dec Bool.bool_dec ]. {
    destruct sc; cbn - [ Nat.eq_dec Bool.bool_dec ]. {
      cbn.
      rewrite Nat.mul_add_distr_l.
      destruct (Nat.eq_dec (va * vb + va * vc) 0) as [Hvvz| Hvvz]. {
        apply Nat.eq_add_0 in Hvvz.
        destruct Hvvz as (H1, H2).
        now rewrite H1, H2.
      }
      destruct (Nat.eq_dec (va * vb) 0) as [Habz| Habz]. {
        rewrite Habz; cbn.
        destruct (Nat.eq_dec (va * vc) 0) as [Hacz| Hacz]; [ | easy ].
        now rewrite Hacz.
      }
      destruct (Nat.eq_dec (va * vc) 0) as [Hacz| Hacz]; [ | easy ].
      now rewrite Hacz.
    }
    destruct (lt_dec vc vb) as [Hcb| Hcb]. {
      cbn.
      destruct (Nat.eq_dec (va * (vb - vc - 1)) 0) as [Hvvz| Hvvz]. {
        apply Nat.eq_mul_0 in Hvvz.
        destruct Hvvz as [Hvvz| Hvvz]; [ now subst va | cbn ].
        apply Nat.sub_0_le in Hvvz.
        apply Nat.le_sub_le_add_r in Hvvz.
        apply Nat.le_antisymm in Hvvz; [ | easy ].
        rewrite Nat.add_comm in Hvvz.
        rewrite Hvvz.
        destruct (Nat.eq_dec (va * vb) 0) as [Habz| Habz]; [ easy | cbn ].
        rewrite Nat_sub_sub_swap, Nat.sub_diag.
        rewrite Nat_sub_sub_swap, Nat.sub_diag.
        destruct (lt_dec (va * vb - 1) (va * vb)) as [Hab| Hab]; [ easy | ].
        exfalso; apply Hab; clear Hab.
        apply Nat.sub_lt; [ | apply Nat.lt_0_1 ].
        now apply Nat.neq_0_lt_0.
      }
      cbn.
      destruct (Nat.eq_dec (va * vb) 0) as [Habz| Habz]. {
        apply Nat.eq_mul_0 in Habz.
        destruct Habz; [ now subst va | now subst vb ].
      }
      cbn.
      destruct (Nat.eq_dec (va * (vc + 1)) 0) as [Hac| Hac]. {
        cbn.
        apply Nat.eq_mul_0 in Hac.
        rewrite Nat.add_comm in Hac.
        destruct Hac; [ now subst va | easy ].
      }
      cbn.
      destruct (lt_dec (va * (vc + 1) - 1) (va * vb)) as [Hv| Hv]. {
        progress f_equal.
        rewrite Nat.mul_sub_distr_l.
        rewrite Nat.sub_sub_distr; cycle 1. {
          now apply Nat.neq_0_lt_0.
        } {
          apply Nat.lt_sub_lt_add_l in Hv.
          now apply Nat.succ_le_mono in Hv.
        }
        rewrite Nat.add_sub.
        rewrite Nat.mul_sub_distr_l.
        rewrite Nat.mul_add_distr_l.
        now rewrite Nat.sub_add_distr.
      }
...

... ...
Theorem mul_add_distr_r : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c).
...
*)

End Z.

Definition of_number (n : Number.int) : option Z :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos n => Some (mk_z true (Nat.of_uint n))
      | Decimal.Neg n => Some (mk_z false (Nat.of_uint n - 1))
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (n : Z) : option Number.int :=
  if z_sign n then
    Some (Number.IntDecimal (Decimal.Pos (Nat.to_uint (z_val n))))
  else
    Some (Number.IntDecimal (Decimal.Neg (Nat.to_uint (z_val n + 1)))).

Number Notation Z of_number to_number : Z_scope.

Notation "a + b" := (Z.add a b) : Z_scope.
Notation "- a" := (Z.opp a) : Z_scope.
Notation "a * b" := (Z.mul a b) : Z_scope.
Notation "a ?= b" := (Z.compare a b) : Z_scope.

Open Scope Z_scope.

Module Nat2Z.

Theorem inj_mul: ∀ a b : nat, Z.of_nat (a * b) = Z.of_nat a * Z.of_nat b.
Proof.
intros.
progress unfold Z.mul.
progress unfold Z.of_nat.
cbn - [ Nat.eq_dec ].
destruct (Nat.eq_dec (a * b) 0) as [Habz| Habz]; [ | easy ].
now rewrite Habz.
Qed.

End Nat2Z.
