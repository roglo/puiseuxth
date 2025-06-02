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

Theorem Nat_compare_mul_cancel_l :
  ∀ a b c, a ≠ 0 → (a * b ?= a * c) = (b ?= c).
Proof.
intros * Haz.
do 2 rewrite nat_compare_equiv.
progress unfold nat_compare_alt.
destruct (lt_eq_lt_dec (a * b) (a * c)) as [[H1| H1]| H1]. {
  destruct (lt_eq_lt_dec b c) as [[H2| H2]| H2].
  easy.
  flia H1 H2.
  apply Nat.mul_lt_mono_pos_l in H1; [ | flia Haz ].
  now apply Nat.lt_asymm in H1.
} {
  destruct (lt_eq_lt_dec b c) as [[H2| H2]| H2].
  apply Nat.mul_cancel_l in H1; [ flia H1 H2 | easy ].
  easy.
  apply Nat.mul_cancel_l in H1; [ flia H1 H2 | easy ].
} {
  destruct (lt_eq_lt_dec b c) as [[H2| H2]| H2].
  apply Nat.mul_lt_mono_pos_l in H1; [ flia H1 H2 | flia Haz ].
  now subst c; apply Nat.lt_irrefl in H1.
  easy.
}
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

Definition sub a b := add a (opp b).

Definition mul a b :=
  match a with
  | z_zero => z_zero
  | z_val sa va =>
      match b with
      | z_zero => z_zero
      | z_val sb vb => z_val (Bool.eqb sa sb) ((va + 1) * (vb + 1) - 1)
      end
  end.

Definition z_pos_div_eucl a b :=
  let a' := (a + 1)%nat in
  let b' := (b + 1)%nat in
  (Z.of_nat (a' / b'), Z.of_nat (a' mod b')).

Definition div_eucl (a b : Z) :=
  match a with
  | z_zero => (z_zero, z_zero)
  | z_val sa a' =>
      match b with
      | z_zero => (z_zero, a)
      | z_val sb b' =>
          let (q', r') := z_pos_div_eucl a' b' in
          let q :=
            if Bool.eqb sa sb then q'
            else
              match r' with
              | z_zero => opp q'
              | _ => opp (add q' (z_val true 0))
              end
          in
          let r :=
            let r1 := if sa then r' else opp r' in
            if Bool.eqb sa sb then r1
            else
              match r1 with
              | z_zero => z_zero
              | _ => add b r1
              end
          in
          (q, r)
      end
  end.

Definition div a b := fst (div_eucl a b).

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

Number Notation Z of_number to_number : Z_scope.

Notation "a + b" := (add a b) : Z_scope.
Notation "a - b" := (sub a b) : Z_scope.
Notation "a * b" := (mul a b) : Z_scope.
Notation "a / b" := (div a b) : Z_scope.
Notation "- a" := (opp a) : Z_scope.

Theorem add_comm : ∀ a b, (a + b)%Z = (b + a)%Z.
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

Theorem add_0_l : ∀ a, (0 + a)%Z = a.
Proof. now intros; destruct a. Qed.

Theorem add_0_r : ∀ a, (a + 0)%Z = a.
Proof. now intros; destruct a. Qed.

Theorem add_add_swap : ∀ a b c, (a + b + c)%Z = (a + c + b)%Z.
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

Theorem add_assoc : ∀ a b c, (a + (b + c))%Z = ((a + b) + c)%Z.
Proof.
intros.
rewrite add_comm.
rewrite add_add_swap.
progress f_equal.
apply add_comm.
Qed.

Theorem mul_comm : ∀ a b, (a * b)%Z = (b * a)%Z.
Proof.
intros.
destruct a as [| sa va]; [ now destruct b | ].
destruct b as [| sb vb]; [ easy | ].
cbn.
rewrite (Nat.mul_comm (vb + 1)).
f_equal.
now destruct sa, sb.
Qed.

Theorem add_move_0_r : ∀ a b, (a + b)%Z = 0%Z ↔ a = (- b)%Z.
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

Theorem mul_0_l : ∀ a, (0 * a)%Z = 0%Z.
Proof. easy. Qed.

Theorem mul_0_r : ∀ a, (a * 0)%Z = 0%Z.
Proof. now intros; rewrite mul_comm. Qed.

Theorem mul_1_l : ∀ a, (1 * a)%Z = a.
Proof.
intros.
cbn.
destruct a as [| sa va]; [ easy | ].
rewrite Nat.add_0_r, Nat.add_sub.
now f_equal; destruct sa.
Qed.

Theorem mul_1_r : ∀ a, (a * 1)%Z = a.
Proof. intros; rewrite mul_comm; apply mul_1_l. Qed.

Theorem mul_mul_swap : ∀ a b c, (a * b * c)%Z = (a * c * b)%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ now do 2 rewrite mul_0_r | ].
destruct c as [| sc vc]; [ now do 2 rewrite mul_0_r | ].
move sb before sa; move sc before sb.
cbn.
f_equal; [ now destruct sa, sb, sc | ].
rewrite Nat.sub_add; [ | flia ].
rewrite Nat.sub_add; [ | flia ].
flia.
Qed.

Theorem mul_assoc : ∀ a b c, (a * (b * c))%Z = ((a * b) * c)%Z.
Proof.
intros.
rewrite mul_comm.
rewrite mul_mul_swap.
progress f_equal.
apply mul_comm.
Qed.

Theorem mul_add_distr_l : ∀ a b c, (a * (b + c))%Z = (a * b + a * c)%Z.
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
rewrite nat_compare_equiv.
progress unfold nat_compare_alt.
destruct (lt_eq_lt_dec vb vc) as [[Hbc| Hbc]| Hbc]. {
  cbn.
  rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec _ _) as [Hsaa| Hsaa]; [ now destruct sa, sb, sc | ].
  clear Hsaa.
  rewrite Nat.sub_add; [ | flia Hbc ].
  rewrite Nat_compare_sub_add_r; [ | flia ].
  rewrite Nat.sub_add; [ | flia ].
  rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_comm ].
  (* lemma to do *)
  rewrite <- Nat_compare_sub_add_r; [ | flia ].
  rewrite Nat.add_sub.
  apply Nat.compare_lt_iff in Hbc; rewrite Hbc.
  apply Nat.compare_lt_iff in Hbc.
  progress f_equal.
  flia Hbc.
} {
  cbn - [ "<?" ]; subst vc.
  rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec _ _) as [Hsaa| Hsaa]; [ now destruct sa, sb, sc | ].
  now rewrite Nat.compare_refl.
} {
  cbn - [ "<?" ].
  rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec _ _) as [Hsaa| Hsaa]; [ now destruct sa, sb, sc | ].
  clear Hsaa.
  rewrite Nat.sub_add; [ | flia Hbc ].
  rewrite Nat_compare_sub_add_r; [ | flia ].
  rewrite Nat.sub_add; [ | flia ].
  rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_comm ].
  (* lemma to do *)
  rewrite <- Nat_compare_sub_add_r; [ | flia ].
  rewrite Nat.add_sub.
  apply Nat.compare_gt_iff in Hbc; rewrite Hbc.
  apply Nat.compare_gt_iff in Hbc.
  progress f_equal.
  flia Hbc.
}
Qed.

Theorem mul_add_distr_r : ∀ a b c, ((a + b) * c)%Z = (a * c + b * c)%Z.
Proof.
intros.
rewrite mul_comm.
do 2 rewrite (mul_comm _ c).
apply mul_add_distr_l.
Qed.

Theorem opp_add_distr : ∀ a b, (- (a + b))%Z = (- a - b)%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | cbn ].
replace (Bool.eqb (negb _) _) with (Bool.eqb sa sb) by now destruct sa, sb.
do 2 rewrite if_eqb_bool_dec.
destruct (Bool.bool_dec sa sb) as [H1| H1]; [ now subst sb | ].
rewrite nat_compare_equiv.
progress unfold nat_compare_alt.
now destruct (lt_eq_lt_dec va vb) as [[| ]| ].
Qed.

Theorem opp_involutive : ∀ a, (- - a)%Z = a.
Proof.
intros.
destruct a as [| s v]; [ easy | cbn ].
now rewrite Bool.negb_involutive.
Qed.

Theorem mul_opp_l : ∀ a b, (- a * b)%Z = (- (a * b))%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | cbn ].
now destruct sa, sb.
Qed.

End Z.

Number Notation Z Z.of_number Z.to_number : Z_scope.

Notation "a + b" := (Z.add a b) : Z_scope.
Notation "a - b" := (Z.sub a b) : Z_scope.
Notation "- a" := (Z.opp a) : Z_scope.
Notation "a * b" := (Z.mul a b) : Z_scope.
Notation "a / b" := (Z.div a b) : Z_scope.
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
