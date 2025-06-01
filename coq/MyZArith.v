Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Psatz.

Inductive Z :=
  | z_zero : Z
  | z_val : bool → nat → Z.

Declare Scope Z_scope.
Delimit Scope Z_scope with Z.
Bind Scope Z_scope with Z.

(* misc theorems *)

(* to be removed if RingLike included *)
(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Theorem Bool_eqb_comm : ∀ a b, Bool.eqb a b = Bool.eqb b a.
Proof.
intros.
progress unfold Bool.eqb.
now destruct a, b.
Qed.

Theorem Nat_compare_sub_add_l : ∀ a b c, b ≤ a → (a - b ?= c) = (a ?= b + c).
Proof.
intros * Hba.
do 2 rewrite nat_compare_equiv.
progress unfold nat_compare_alt.
destruct (lt_eq_lt_dec (a - b) c) as [[H1| H1]| H1]. {
  destruct (lt_eq_lt_dec a (b + c)) as [[H2| H2]| H2].
  easy.
  flia H1 H2.
  flia H1 H2.
} {
  destruct (lt_eq_lt_dec a (b + c)) as [[H2| H2]| H2].
  flia Hba H1 H2.
  easy.
  flia H1 H2.
} {
  destruct (lt_eq_lt_dec a (b + c)) as [[H2| H2]| H2].
  flia H1 H2.
  flia H1 H2.
  easy.
}
Qed.

Theorem Nat_compare_sub_add_r : ∀ a b c, b ≤ a → (a - b ?= c) = (a ?= c + b).
Proof.
intros * Hba.
rewrite Nat.add_comm.
now apply Nat_compare_sub_add_l.
Qed.

Theorem if_eqb_bool_dec : ∀ A i j (a b : A),
  (if Bool.eqb i j then a else b) = (if Bool.bool_dec i j then a else b).
Proof. now intros; destruct i, j. Qed.

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

Definition of_nat n :=
  match n with
  | 0 => z_zero
  | S n' => z_val true n'
  end.

Definition abs_nat a :=
  match a with
  | z_zero => 0
  | z_val _ n => S n
  end.

Definition add a b :=
  match a with
  | z_zero => b
  | z_val sa va =>
      match b with
      | z_zero => a
      | z_val sb vb =>
          if Bool.eqb sa sb then z_val sa (va + vb + 1)
          else
            match va ?= vb with
            | Eq => z_zero
            | Lt => z_val sb (vb - va - 1)
            | Gt => z_val sa (va - vb - 1)
            end
      end
  end.

Definition opp a :=
  match a with
  | z_zero => z_zero
  | z_val s v => z_val (negb s) v
  end.

Definition mul a b :=
  match a with
  | z_zero => z_zero
  | z_val sa va =>
      match b with
      | z_zero => z_zero
      | z_val sb vb => z_val (Bool.eqb sa sb) ((va + 1) * (vb + 1) - 1)
      end
  end.

Definition compare a b :=
  match a with
  | z_zero =>
      match b with
      | z_zero => Eq
      | z_val sb _ => if sb then Lt else Gt
      end
  | z_val sa va =>
      match b with
      | z_zero => if sa then Gt else Lt
      | z_val sb vb =>
          match sa with
          | true =>
              match sb with
              | true => va ?= vb
              | false => Gt
              end
          | false =>
              match sb with
              | true => Lt
              | false => vb ?= va
              end
          end
      end
  end.

Theorem add_comm : ∀ a b, add a b = add b a.
Proof.
intros.
progress unfold add.
destruct a as [| sa va]; [ now destruct b | ].
destruct b as [| sb vb]; [ easy | ].
move sb before sa.
rewrite (Nat.add_comm vb).
rewrite (Bool_eqb_comm sb).
do 2 rewrite if_eqb_bool_dec.
destruct (Bool.bool_dec sa sb) as [Hab| Hab]; [ now subst sb | ].
rewrite (Nat.compare_antisym va).
now destruct (va ?= vb).
Qed.

Theorem add_0_l : ∀ a, add z_zero a = a.
Proof. now intros; destruct a. Qed.

Theorem add_0_r : ∀ a, add a z_zero = a.
Proof. now intros; destruct a. Qed.

Notation "a + b" := (add a b) : Z_scope.
Notation "a * b" := (mul a b) : Z_scope.

Theorem add_add_swap : ∀ a b c, add (add a b) c = add (add a c) b.
Proof.
intros.
destruct a as [| sa va]; [ do 2 rewrite add_0_l; apply add_comm | ].
destruct b as [| sb vb]; [ now do 2 rewrite add_0_r | ].
destruct c as [| sc vc]; [ now do 2 rewrite add_0_r | ].
move sb before sa; move sc before sb.
destruct (Bool.bool_dec sa sb) as [H1| H1]. {
  subst sb; cbn.
  rewrite Bool.eqb_reflx; cbn.
  do 2 rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec sa sc) as [H2| H2]. {
    cbn; subst sc.
    rewrite Bool.eqb_reflx.
    f_equal; flia.
  }
  apply Bool.eqb_false_iff in H2.
  do 2 rewrite nat_compare_equiv.
  progress unfold nat_compare_alt.
  destruct (lt_eq_lt_dec va vc) as [[H1| H1]| H1]. {
    cbn.
    rewrite (Bool_eqb_comm sc), H2.
    rewrite Nat_compare_sub_add_r; [ | flia H1 ].
    rewrite Nat_compare_sub_add_l; [ | flia H1 ].
    rewrite Nat.add_assoc.
    rewrite Nat.compare_antisym.
    rewrite nat_compare_equiv.
    progress unfold nat_compare_alt.
    destruct (lt_eq_lt_dec (va + vb + 1) vc) as [[H3| H3]| H3].
    cbn; f_equal; flia.
    easy.
    cbn; f_equal; flia H1.
  } {
    cbn.
    destruct (lt_eq_lt_dec (va + vb + 1) vc) as [[H3| H3]| H3].
    flia H1 H3.
    flia H1 H3.
    cbn; f_equal; flia H1.
  } {
    cbn.
    rewrite Bool.eqb_reflx.
    destruct (lt_eq_lt_dec (va + vb + 1) vc) as [[H3| H3]| H3].
    flia H1 H3.
    flia H1 H3.
    cbn; f_equal; flia H1.
  }
}
destruct (Bool.bool_dec sa sc) as [H2| H2]. {
  subst sc; cbn.
  rename H1 into H2.
  rewrite Bool.eqb_reflx; cbn.
  apply Bool.eqb_false_iff in H2.
  rewrite H2, nat_compare_equiv.
  progress unfold nat_compare_alt.
  destruct (lt_eq_lt_dec va vb) as [[H1| H1]| H1]. {
    cbn.
    rewrite (Bool_eqb_comm sb), H2.
    rewrite Nat_compare_sub_add_r; [ | flia H1 ].
    rewrite Nat_compare_sub_add_l; [ | flia H1 ].
    rewrite Nat.add_assoc.
    rewrite Nat.compare_antisym.
    rewrite nat_compare_equiv.
    progress unfold nat_compare_alt.
    destruct (lt_eq_lt_dec (va + vc + 1) vb) as [[H3| H3]| H3].
    cbn; f_equal; flia.
    easy.
    cbn; f_equal; flia H1.
  } {
    cbn.
    rewrite nat_compare_equiv.
    progress unfold nat_compare_alt.
    destruct (lt_eq_lt_dec (va + vc + 1) vb) as [[H3| H3]| H3].
    flia H1 H3.
    flia H1 H3.
    cbn; f_equal; flia H1.
  } {
    cbn.
    rewrite Bool.eqb_reflx.
    rewrite nat_compare_equiv.
    progress unfold nat_compare_alt.
    destruct (lt_eq_lt_dec (va + vc + 1) vb) as [[H3| H3]| H3].
    flia H1 H3.
    flia H1 H3.
    cbn; f_equal; flia H1.
  }
}
assert (sb = sc) by now destruct sa, sb, sc.
subst sc; clear H2.
cbn.
apply Bool.eqb_false_iff in H1.
rewrite H1.
do 2 rewrite nat_compare_equiv.
progress unfold nat_compare_alt.
destruct (lt_eq_lt_dec va vb) as [[H2| H2]| H2]. {
  cbn; rewrite Bool.eqb_reflx.
  destruct (lt_eq_lt_dec va vc) as [[H3| H3]| H3]. {
    cbn; rewrite Bool.eqb_reflx.
    f_equal; flia H2 H3.
  } {
    cbn; f_equal; flia H2 H3.
  } {
    cbn; rewrite H1.
    rewrite nat_compare_equiv.
    progress unfold nat_compare_alt.
    destruct (lt_eq_lt_dec (va - vc - 1) vb) as [[H4| H4]| H4].
    f_equal; flia H2 H3.
    exfalso; flia H2 H4.
    exfalso; flia H2 H4.
  }
} {
  subst vb; cbn.
  destruct (lt_eq_lt_dec va vc) as [[H3| H3]| H3]. {
    cbn; rewrite Bool.eqb_reflx.
    f_equal; flia H3.
  } {
    now subst vc.
  } {
    cbn; rewrite H1.
    rewrite nat_compare_equiv.
    progress unfold nat_compare_alt.
    destruct (lt_eq_lt_dec (va - vc - 1) va) as [[H4| H4]| H4].
    f_equal; flia H3.
    exfalso; flia H3 H4.
    exfalso; flia H3 H4.
  }
}
destruct (lt_eq_lt_dec va vc) as [[H3| H3]| H3]. {
  cbn; rewrite Bool.eqb_reflx, H1.
  rewrite nat_compare_equiv.
  progress unfold nat_compare_alt.
  destruct (lt_eq_lt_dec (va - vb - 1) vc) as [[H4| H4]| H4].
  f_equal; flia H2 H3.
  exfalso; flia H3 H4.
  exfalso; flia H3 H4.
} {
  subst vc; cbn; rewrite H1.
  rewrite nat_compare_equiv.
  progress unfold nat_compare_alt.
  destruct (lt_eq_lt_dec (va - vb - 1) va) as [[H3| H3]| H3].
  f_equal; flia H2 H3.
  exfalso; flia H2 H3.
  exfalso; flia H2 H3.
}
cbn; rewrite H1.
rewrite Nat_compare_sub_add_r; [ | flia H2 ].
rewrite Nat_compare_sub_add_l; [ | flia H2 ].
rewrite Nat_compare_sub_add_r; [ | flia H3 ].
rewrite Nat_compare_sub_add_l; [ | flia H3 ].
do 2 rewrite Nat.add_assoc.
rewrite (Nat.add_comm vc).
rewrite nat_compare_equiv.
progress unfold nat_compare_alt.
destruct (lt_eq_lt_dec va (vb + vc + 1)) as [[H4| H4]| H4].
cbn; f_equal; flia H2 H3.
easy.
cbn; f_equal; flia.
Qed.

Theorem add_assoc : ∀ a b c, add a (add b c) = add (add a b) c.
Proof.
intros.
rewrite add_comm.
rewrite add_add_swap.
progress f_equal.
apply add_comm.
Qed.

Theorem mul_comm : ∀ a b, mul a b = mul b a.
Proof.
intros.
destruct a as [| sa va]; [ now destruct b | ].
destruct b as [| sb vb]; [ easy | ].
cbn.
rewrite (Nat.mul_comm (vb + 1)).
f_equal.
now destruct sa, sb.
Qed.

Theorem add_move_0_r : ∀ a b, add a b = z_zero ↔ a = opp b.
Proof.
intros.
split; intros Hab. {
  progress unfold add in Hab.
  progress unfold opp.
  destruct a as [| sa va]; [ now subst b | ].
  destruct b as [| sb vb]; [ easy | ].
  rewrite if_eqb_bool_dec in Hab.
  destruct (Bool.bool_dec sa sb) as [Hsab| Hsab]; [ easy | ].
  rewrite nat_compare_equiv in Hab.
  progress unfold nat_compare_alt in Hab.
  destruct (lt_eq_lt_dec va vb) as [[H1| H1]| H1]; [ easy | | easy ].
  now subst vb; destruct sa, sb.
}
subst a.
progress unfold add.
progress unfold opp.
destruct b as [| sb vb]; [ easy | ].
rewrite Bool.eqb_negb1.
now rewrite Nat.compare_refl.
Qed.

Theorem mul_add_distr_l : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c).
Proof.
intros.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | ].
destruct c as [| sc vc]; [ easy | ].
move sb before sa; move sc before sb.
destruct (Bool.bool_dec sb sc) as [Hsbc| Hsbc]. {
  subst sc; cbn.
  do 2 rewrite Bool.eqb_reflx.
  f_equal; flia.
}
cbn - [ mul "<?" ].
rewrite if_eqb_bool_dec.
destruct (Bool.bool_dec _ _) as [Hsaa| Hsaa]; [ now destruct sb, sc | ].
clear Hsaa.
...
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec vb vc) as [Hbc| Hbc]. 2: {
  apply Nat.nlt_ge in Hbc.
  destruct (lt_dec vc vb) as [Hcb| Hcb]. 2: {
    apply Nat.nlt_ge in Hcb.
    apply Nat.le_antisymm in Hcb; [ subst vc | easy ].
    clear Hbc.
    progress unfold mul at 1.
    symmetry.
    cbn - [ add ].
    apply add_move_0_r.
    remember (_ - 1) as x.
    cbn.
    progress f_equal.
    now destruct sa, sb, sc.
  }
  clear Hbc.
  cbn - [ "<?" ].
  rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec _ _) as [Hsaa| Hsaa]; [ now destruct sa, sb, sc | ].
  clear Hsaa.
  rewrite Nat.sub_add; [ | flia Hcb ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec _ _) as [Hsaa| Hsaa]. {
    exfalso.
    apply Nat.nle_gt in Hsaa.
    apply Hsaa; clear Hsaa.
    apply Nat.sub_le_mono_r.
    apply Nat.mul_le_mono_l.
    apply Nat.add_le_mono_r.
    now apply Nat.lt_le_incl.
  }
  rewrite if_ltb_lt_dec.
  destruct (lt_dec _ _) as [Habc| Habc]. {
    progress f_equal.
    rewrite Nat.mul_sub_distr_l.
    flia.
  }
  exfalso.
  apply Nat.nlt_ge in Hsaa, Habc.
  apply Nat.le_sub_le_add_r in Hsaa, Habc.
  rewrite Nat.sub_add in Hsaa; [ | flia ].
  rewrite Nat.sub_add in Habc; [ | flia ].
  apply Nat.mul_le_mono_pos_l in Hsaa; [ | flia ].
  apply Nat.mul_le_mono_pos_l in Habc; [ | flia ].
  flia Hcb Hsaa Habc.
} {
  cbn - [ "<?" ].
  rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec _ _) as [Hsaa| Hsaa]; [ now destruct sa, sb, sc | ].
  clear Hsaa.
  rewrite Nat.sub_add; [ | flia Hbc ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec _ _) as [Hsaa| Hsaa]. {
    progress f_equal.
    flia Hbc Hsaa.
  }
  exfalso.
  apply Nat.nlt_ge in Hsaa.
  apply Nat.le_sub_le_add_r in Hsaa.
  rewrite Nat.sub_add in Hsaa; [ | flia ].
  apply Nat.mul_le_mono_pos_l in Hsaa; [ | flia ].
  flia Hbc Hsaa.
}
Qed.

Theorem mul_add_distr_r : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c).
Proof.
intros.
rewrite mul_comm.
do 2 rewrite (mul_comm _ c).
apply mul_add_distr_l.
Qed.

End Z.

Definition of_number (n : Number.int) : option Z :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos (Decimal.D0 Decimal.Nil) => Some z_zero
      | Decimal.Pos n => Some (z_val true (Nat.of_uint n - 1))
      | Decimal.Neg n => Some (z_val false (Nat.of_uint n - 1))
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (a : Z) : Number.int :=
  match a with
  | z_zero => Number.IntDecimal (Decimal.Pos (Nat.to_uint 0))
  | z_val true v => Number.IntDecimal (Decimal.Pos (Nat.to_uint (v + 1)))
  | z_val false v => Number.IntDecimal (Decimal.Neg (Nat.to_uint (v + 1)))
  end.

Definition to_number' (a : Z) : option (Number.int) := None.

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
destruct a; [ easy | ].
rewrite Nat.mul_comm.
destruct b; [ easy | cbn ].
f_equal; flia.
Qed.

End Nat2Z.

(*
Compute (5 ?= 3).
Compute (5 ?= 4).
Compute (5 ?= 5).
Compute (5 ?= 6).
Compute (5 ?= 7).

Compute (5 ?= -3).
Compute (5 ?= -4).
Compute (5 ?= -5).
Compute (5 ?= -6).
Compute (5 ?= -7).

Compute (-5 ?= -3).
Compute (-5 ?= -4).
Compute (-5 ?= -5).
Compute (-5 ?= -6).
Compute (-5 ?= -7).

Compute (-5 ?= 3).
Compute (-5 ?= 4).
Compute (-5 ?= 5).
Compute (-5 ?= 6).
Compute (-5 ?= 7).

Compute (0 ?= 5).
Compute (5 ?= 0).
Compute (0 ?= -5).
Compute (-5 ?= 0).
Compute (0 ?= 0).
*)

(*
........................
previous version
........................

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
(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

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
move sb before sa; move sc before sb.
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
        replace (vc + 1) with vb by flia Hcb Hvvz.
        destruct (Nat.eq_dec (va * vb) 0) as [Habz| Habz]; [ easy | cbn ].
        rewrite Nat_sub_sub_swap, Nat.sub_diag.
        rewrite Nat_sub_sub_swap, Nat.sub_diag.
        destruct (lt_dec (va * vb - 1) (va * vb)) as [Hab| Hab]; [ easy | ].
        exfalso; flia Habz Hab.
      }
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
        flia Hvvz Hac Hv.
      }
      rewrite <- Nat.sub_add_distr in Hvvz.
      exfalso; flia Hvvz Hv.
    }
    cbn.
    apply Nat.nlt_ge in Hcb.
    destruct (Nat.eq_dec (va * (vc - vb + 1)) 0) as [Hvvz| Hvvz]. {
      cbn.
      apply Nat.eq_mul_0 in Hvvz.
      destruct Hvvz as [Hvvz| Hvvz]; [ now subst va | cbn ].
      flia Hcb Hvvz.
    }
    destruct (Nat.eq_dec (va * vb) 0) as [Habz| Habz]. {
      cbn.
      apply Nat.eq_mul_0 in Habz.
      destruct Habz; [ now subst va | subst vb ].
      rewrite Nat.sub_0_r in Hvvz |-*.
      destruct (Nat.eq_dec (va * (vc + 1)) 0) as [Hacz| Hacz]; [ easy | ].
      now rewrite Nat.sub_0_r.
    }
    cbn.
    destruct (Nat.eq_dec (va * (vc + 1)) 0) as [Hacz| Hacz]. {
      exfalso; flia Hvvz Hacz.
    }
    cbn.
    rewrite <- Nat.add_sub_swap in Hvvz; [ | easy ].
    destruct (lt_dec (va * (vc + 1) - 1) (va * vb)) as [Hac| Hac]. {
      exfalso; flia Hvvz Hac.
    }
    f_equal.
    rewrite <- Nat.add_sub_swap; [ flia Hvvz | easy ].
  }
  destruct sc; cbn - [ Nat.eq_dec Bool.bool_dec ]. {
    cbn.
    destruct (lt_dec vb vc) as [Hbc| Hbc]. {
      cbn.
      destruct (Nat.eq_dec (va * (vc - vb - 1)) 0) as [Hvvz| Hvvz]. {
        cbn.
        apply Nat.eq_mul_0 in Hvvz.
        destruct Hvvz as [Hvvz| Hvvz]; [ now subst va | cbn ].
        replace (vb + 1) with vc by flia Hbc Hvvz.
        destruct (Nat.eq_dec (va * vc) 0) as [Hacz| Hacz]; [ easy | cbn ].
        rewrite Nat_sub_sub_swap, Nat.sub_diag.
        rewrite Nat_sub_sub_swap, Nat.sub_diag.
        destruct (lt_dec (va * vc - 1) (va * vc)) as [Hac| Hac]; [ easy | ].
        exfalso; flia Hacz Hac.
      }
      destruct (Nat.eq_dec (va * (vb + 1)) 0) as [Hab| Hab]. {
        progress cbn.
        apply Nat.eq_mul_0 in Hab.
        rewrite Nat.add_comm in Hab.
        destruct Hab; [ now subst va | easy ].
      }
      cbn.
      rewrite <- Nat.sub_add_distr in Hvvz.
      destruct (Nat.eq_dec (va * vc) 0) as [Hacz| Hacz]. {
        exfalso; flia Hvvz Hacz.
      }
      cbn.
      destruct (lt_dec (va * (vb + 1) - 1) (va * vc)) as [Hv| Hv]. {
        progress f_equal.
        flia Hvvz Hab Hv.
      }
      exfalso; flia Hvvz Hv.
    }
    apply Nat.nlt_ge in Hbc.
    cbn.
    destruct (Nat.eq_dec (va * (vb - vc + 1)) 0) as [Hvvz| Hvvz]. {
      apply Nat.eq_mul_0 in Hvvz.
      destruct Hvvz as [Hvvz| Hvvz]; [ now subst va | cbn ].
      flia Hbc Hvvz.
    }
...

... ...
Theorem mul_add_distr_r : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c).
...

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
*)
