(** * A ℤ arithmetics *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Psatz.
Import ListDef.

Require Import A_PosArith.

Inductive Z :=
| z_zero : Z
| z_val : bool → pos → Z.

Declare Scope Z_scope.
Delimit Scope Z_scope with Z.
Bind Scope Z_scope with Z.

Definition z_pos a := z_val true a.
Definition z_neg a := z_val false a.

(* misc theorems *)

Theorem Bool_eqb_comm : ∀ a b, Bool.eqb a b = Bool.eqb b a.
Proof.
intros.
progress unfold Bool.eqb.
now destruct a, b.
Qed.

Theorem if_eqb_bool_dec : ∀ A i j (a b : A),
  (if Bool.eqb i j then a else b) = (if Bool.bool_dec i j then a else b).
Proof. now intros; destruct i, j. Qed.

(* to be removed if ring-like misc included *)
Theorem Nat_sub_succ_1 : ∀ n, S n - 1 = n.
Proof. now intros; rewrite Nat.sub_succ, Nat.sub_0_r. Qed.

(* to be removed if ring-like misc included *)
Global Hint Resolve Nat.le_0_l : core.
Global Hint Resolve Nat.lt_0_succ : core.

(* end misc theorems *)

Module Z.

Definition of_number (n : Number.int) : option Z :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos (Decimal.D0 Decimal.Nil) => Some z_zero
      | Decimal.Pos n => Some (z_val true (Pos.of_nat (Nat.of_uint n)))
      | Decimal.Neg n => Some (z_val false (Pos.of_nat (Nat.of_uint n)))
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (a : Z) : Number.int :=
  match a with
  | z_zero => Number.IntDecimal (Decimal.Pos (Nat.to_uint 0))
  | z_val true v =>
      Number.IntDecimal (Decimal.Pos (Nat.to_uint (Pos.to_nat v)))
  | z_val false v =>
      Number.IntDecimal (Decimal.Neg (Nat.to_uint (Pos.to_nat v)))
  end.

Number Notation Z Z.of_number Z.to_number : Z_scope.

Definition of_nat n :=
  match n with
  | 0 => z_zero
  | S _ => z_val true (Pos.of_nat n)
  end.

Definition to_nat a :=
  match a with
  | z_val true n => Pos.to_nat n
  | _ => 0
  end.

Definition of_pos (a : pos) := z_val true a.

Definition to_pos a :=
  match a with
  | z_val true n => n
  | _ => 1%pos
  end.

Definition add a b :=
  match a with
  | z_zero => b
  | z_val sa va =>
      match b with
      | z_zero => a
      | z_val sb vb =>
          if Bool.eqb sa sb then z_val sa (Pos.add va vb)
          else
            match Pos.compare va vb with
            | Eq => z_zero
            | Lt => z_val sb (Pos.sub vb va)
            | Gt => z_val sa (Pos.sub va vb)
            end
      end
  end.

Definition mul a b :=
  match a with
  | z_zero => z_zero
  | z_val sa va =>
      match b with
      | z_zero => z_zero
      | z_val sb vb => z_val (Bool.eqb sa sb) (va * vb)
      end
  end.

Definition opp a :=
  match a with
  | z_zero => z_zero
  | z_val s v => z_val (negb s) v
  end.

Definition sub a b := Z.add a (Z.opp b).

Definition z_pos_div_eucl (a b : pos) :=
  let a' := Pos.to_nat a in
  let b' := Pos.to_nat b in
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
              | z_zero => Z.opp q'
              | _ => Z.opp (Z.add q' (z_val true 1))
              end
          in
          let r :=
            let r1 := if sa then r' else Z.opp r' in
            if Bool.eqb sa sb then r1
            else
              match r1 with
              | z_zero => z_zero
              | _ => Z.add b r1
              end
          in
          (q, r)
      end
  end.

Definition div a b := fst (div_eucl a b).

Definition sgn a :=
  match a with
  | z_zero => 0%Z
  | z_val true _ => 1%Z
  | z_val false _ => (-1)%Z
  end.

Definition pos_abs a :=
  match a with
  | z_zero => 1%pos
  | z_val _ v => v
  end.

Definition abs a :=
  match a with
  | z_zero => 0%Z
  | z_val _ v => Z.of_nat (Pos.to_nat v)
  end.

Theorem eq_dec : ∀ a b : Z, {a = b} + {a ≠ b}.
Proof.
intros.
destruct a as [| sa va]. {
  now destruct b; [ left | right ].
} {
  destruct b as [| sb vb]; [ now right | ].
  destruct (Bool.bool_dec sa sb) as [Hsab| Hsab]. {
    subst sb.
    destruct (Pos.eq_dec va vb) as [Hvab| Hvab]; [ now subst vb; left | ].
    right.
    intros H; apply Hvab.
    now injection H.
  }
  right.
  intros H; apply Hsab.
  now injection H.
}
Qed.

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
              | true => (va ?= vb)%pos
              | false => Gt
              end
          | false =>
              match sb with
              | true => Lt
              | false => (vb ?= va)%pos
              end
          end
      end
  end.

Definition le a b := compare a b ≠ Gt.
Definition lt a b := compare a b = Lt.

Definition leb a b :=
  match Z.compare a b with
  | Eq | Lt => true
  | Gt => false
  end.

Definition eqb a b :=
  match a with
  | z_zero =>
      match b with
      | z_zero => true
      | _ => false
      end
  | z_val sa va =>
      match b with
      | z_val sb vb => (Bool.eqb sa sb && (va =? vb)%pos)%bool
      | _ => false
      end
  end.

Definition divide x y := ∃ z, y = Z.mul z x.

Notation "a + b" := (Z.add a b) : Z_scope.
Notation "a - b" := (Z.sub a b) : Z_scope.
Notation "a * b" := (Z.mul a b) : Z_scope.
Notation "a / b" := (Z.div a b) : Z_scope.
Notation "- a" := (Z.opp a) : Z_scope.
Notation "a ≤ b" := (Z.le a b) : Z_scope.
Notation "a < b" := (Z.lt a b) : Z_scope.
Notation "a ?= b" := (Z.compare a b) : Z_scope.
Notation "a =? b" := (Z.eqb a b) : Z_scope.
Notation "a ≤? b" := (Z.leb a b) (at level 70) : Z_scope.
Notation "a ≤ b ≤ c" := (Z.le a b ∧ Z.le b c) : Z_scope.
Notation "( x | y )" := (Z.divide x y) : Z_scope.

(*
Instance ring_like_op : ring_like_op Z :=
  {| rngl_zero := z_zero;
    rngl_add := Z.add;
    rngl_mul := Z.mul;
    rngl_opt_one := Some (z_val true 1);
    rngl_opt_opp_or_subt := Some (inl Z.opp);
    rngl_opt_inv_or_quot := Some (inr Z.div);
    rngl_opt_is_zero_divisor := None;
    rngl_opt_eq_dec := Some Z.eq_dec;
    rngl_opt_leb := Some Z.leb |}.
*)

Theorem opp_involutive : ∀ a, (- - a)%Z = a.
Proof.
  intros.
  destruct a as [| s v]; [ easy | cbn ].
  now rewrite Bool.negb_involutive.
Qed.

Theorem add_comm : ∀ a b, (a + b)%Z = (b + a)%Z.
Proof.
intros.
progress unfold add.
destruct a as [| sa va]; [ now destruct b | ].
destruct b as [| sb vb]; [ easy | ].
move sb before sa.
rewrite (Pos.add_comm vb).
rewrite (Bool_eqb_comm sb).
do 2 rewrite if_eqb_bool_dec.
destruct (Bool.bool_dec sa sb) as [Hab| Hab]; [ now subst sb | ].
rewrite (Pos.compare_antisym vb).
now destruct (va ?= vb)%pos.
Qed.

Theorem add_0_l : ∀ a, (0 + a)%Z = a.
Proof. now intros; destruct a. Qed.

Theorem add_0_r : ∀ a, (a + 0)%Z = a.
Proof. now intros; destruct a. Qed.

Theorem add_add_swap : ∀ a b c, (a + b + c)%Z = (a + c + b)%Z.
Proof.
intros.
destruct a as [| sa va]; [ do 2 rewrite Z.add_0_l; apply Z.add_comm | ].
destruct b as [| sb vb]; [ now do 2 rewrite Z.add_0_r | ].
destruct c as [| sc vc]; [ now do 2 rewrite Z.add_0_r | ].
move sb before sa; move sc before sb.
destruct va as (va).
destruct vb as (vb).
destruct vc as (vc).
cbn.
rewrite if_eqb_bool_dec.
destruct (Bool.bool_dec sa sb) as [H1| H1]. {
  subst sb; cbn.
  do 2 rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec sa sc) as [H2| H2]. {
    cbn; subst sc.
    rewrite Bool.eqb_reflx.
    f_equal; apply Pos.add_add_swap.
  }
  apply Bool.eqb_false_iff in H2.
  do 2 rewrite nat_compare_equiv.
  progress unfold nat_compare_alt.
  destruct (lt_eq_lt_dec va vc) as [[H1| H1]| H1]; cbn. {
    rewrite (Bool_eqb_comm sc), H2.
    rewrite Nat_compare_sub_add_r; [ | flia H1 ].
    rewrite Nat_compare_sub_add_l; [ | flia H1 ].
    rewrite Nat.add_assoc.
    rewrite Nat.compare_antisym.
    rewrite nat_compare_equiv.
    progress unfold nat_compare_alt.
    destruct (lt_eq_lt_dec _ _) as [[H3| H3]| H3].
    cbn; unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia.
    easy.
    cbn; unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H1.
  } {
    subst vc.
    destruct (lt_eq_lt_dec _ _) as [[H3| H3]| H3].
    flia H3.
    flia H3.
    now rewrite Pos.add_comm, Pos.add_sub.
  } {
    cbn.
    rewrite Bool.eqb_reflx.
    destruct (lt_eq_lt_dec (va + vb + 1) vc) as [[H3| H3]| H3].
    flia H1 H3.
    flia H1 H3.
    unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H1.
  }
}
rewrite if_eqb_bool_dec.
destruct (Bool.bool_dec sa sc) as [H2| H2]. {
  subst sc; cbn.
  rename H1 into H2.
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
    unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia.
    easy.
    unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H1.
  } {
    cbn.
    subst vb.
    rewrite nat_compare_equiv.
    progress unfold nat_compare_alt.
    destruct (lt_eq_lt_dec (va + vc + 1) va) as [[H3| H3]| H3].
    flia H3.
    flia H3.
    unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia.
  } {
    cbn.
    rewrite Bool.eqb_reflx.
    rewrite nat_compare_equiv.
    progress unfold nat_compare_alt.
    destruct (lt_eq_lt_dec (va + vc + 1) vb) as [[H3| H3]| H3].
    flia H1 H3.
    flia H1 H3.
    unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H1.
  }
}
assert (sb = sc) by now destruct sa, sb, sc.
subst sc; clear H2.
cbn.
apply Bool.eqb_false_iff in H1.
do 2 rewrite nat_compare_equiv.
progress unfold nat_compare_alt.
destruct (lt_eq_lt_dec va vb) as [[H2| H2]| H2]. {
  cbn; rewrite Bool.eqb_reflx.
  destruct (lt_eq_lt_dec va vc) as [[H3| H3]| H3]. {
    cbn; rewrite Bool.eqb_reflx.
    unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H2 H3.
  } {
    unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H2 H3.
  } {
    cbn.
    rewrite H1.
    rewrite nat_compare_equiv.
    progress unfold nat_compare_alt.
    destruct (lt_eq_lt_dec (va - vc - 1) vb) as [[H4| H4]| H4].
    unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H2 H3.
    exfalso; flia H2 H4.
    exfalso; flia H2 H4.
  }
} {
  subst vb; cbn.
  destruct (lt_eq_lt_dec va vc) as [[H3| H3]| H3]. {
    cbn; rewrite Bool.eqb_reflx.
    unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H3.
  } {
    now subst vc.
  } {
    cbn; rewrite H1.
    rewrite nat_compare_equiv.
    progress unfold nat_compare_alt.
    destruct (lt_eq_lt_dec (va - vc - 1) va) as [[H4| H4]| H4].
    unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H3.
    exfalso; flia H3 H4.
    exfalso; flia H3 H4.
  }
}
cbn.
rewrite H1.
destruct (lt_eq_lt_dec va vc) as [[H3| H3]| H3]. {
  cbn; rewrite Bool.eqb_reflx.
  rewrite nat_compare_equiv.
  progress unfold nat_compare_alt.
  destruct (lt_eq_lt_dec (va - vb - 1) vc) as [[H4| H4]| H4].
  unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H2 H3.
  exfalso; flia H3 H4.
  exfalso; flia H3 H4.
} {
  subst vc; cbn.
  rewrite nat_compare_equiv.
  progress unfold nat_compare_alt.
  destruct (lt_eq_lt_dec (va - vb - 1) va) as [[H3| H3]| H3].
  unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H2 H3.
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
unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia H2 H3.
easy.
unfold Pos.sub, Pos.add; cbn; f_equal; f_equal; flia.
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
destruct b as [| sb vb]; [ easy | cbn ].
rewrite (Pos.mul_comm vb).
f_equal.
now destruct sa, sb.
Qed.

Theorem mul_0_l : ∀ a, (0 * a)%Z = 0%Z.
Proof. easy. Qed.

Theorem mul_0_r : ∀ a, (a * 0)%Z = 0%Z.
Proof. now intros; rewrite mul_comm. Qed.

Theorem mul_mul_swap : ∀ a b c, (a * b * c)%Z = (a * c * b)%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ now do 2 rewrite Z.mul_0_r | ].
destruct c as [| sc vc]; [ now do 2 rewrite Z.mul_0_r | ].
move sb before sa; move sc before sb.
cbn.
f_equal; [ now destruct sa, sb, sc | ].
apply Pos.mul_mul_swap.
Qed.

Theorem mul_assoc : ∀ a b c, (a * (b * c))%Z = ((a * b) * c)%Z.
Proof.
intros.
rewrite Z.mul_comm.
rewrite Z.mul_mul_swap.
progress f_equal.
apply Z.mul_comm.
Qed.

Theorem mul_1_l : ∀ a, (1 * a)%Z = a.
Proof.
intros.
cbn.
destruct a as [| sa va]; [ easy | ].
rewrite Pos.mul_1_l.
now destruct sa.
Qed.

Theorem mul_1_r : ∀ a, (a * 1)%Z = a.
Proof. intros; rewrite Z.mul_comm; apply Z.mul_1_l. Qed.

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
  f_equal; apply Pos.mul_add_distr_l.
}
cbn - [ mul "<?" ].
rewrite if_eqb_bool_dec.
destruct (Bool.bool_dec _ _) as [Hsaa| Hsaa]; [ now destruct sb, sc | ].
clear Hsaa.
rewrite Pos.compare_match_dec.
destruct (lt_eq_lt_dec _ _) as [[Hbc| Hbc]| Hbc]. {
  cbn.
  rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec _ _) as [Hsaa| Hsaa]; [ now destruct sa, sb, sc | ].
  clear Hsaa.
  rewrite Nat_compare_sub_mono_r; [ | easy | easy ].
  rewrite Nat_compare_mul_mono_l; [ | now rewrite Nat.add_1_r ].
  rewrite Nat_compare_add_mono_r.
  generalize Hbc; intros H.
  apply Nat.compare_lt_iff in H; rewrite H; f_equal; clear H.
  now apply Pos.mul_sub_distr_l.
} {
  cbn.
  apply Pos.nat_inj in Hbc; subst vc.
  rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec _ _) as [Hsaa| Hsaa]; [ now destruct sa, sb, sc | ].
  now rewrite Nat.compare_refl.
} {
  cbn.
  rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec _ _) as [Hsaa| Hsaa]; [ now destruct sa, sb, sc | ].
  clear Hsaa.
  rewrite Nat_compare_sub_mono_r; [ | easy | easy ].
  rewrite Nat_compare_mul_mono_l; [ | now rewrite Nat.add_1_r ].
  rewrite Nat_compare_add_mono_r.
  generalize Hbc; intros H.
  apply Nat.compare_gt_iff in H; rewrite H; f_equal; clear H.
  now apply Pos.mul_sub_distr_l.
}
Qed.

Theorem mul_add_distr_r : ∀ a b c, ((a + b) * c)%Z = (a * c + b * c)%Z.
Proof.
intros.
rewrite Z.mul_comm.
do 2 rewrite (Z.mul_comm _ c).
apply Z.mul_add_distr_l.
Qed.

Theorem add_opp_diag_l : ∀ a : Z, (- a + a)%Z = 0%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | cbn ].
now destruct sa; rewrite Pos.compare_refl.
Qed.

Theorem add_opp_r : ∀ a b, (a + - b = a - b)%Z.
Proof. easy. Qed.

Theorem mul_div : ∀ a b, b ≠ 0%Z → (a * b / b)%Z = a.
Proof.
intros * Hbz.
progress unfold mul.
progress unfold div.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | cbn ].
rewrite Nat.sub_add; [ | flia ].
rewrite if_eqb_bool_dec.
rewrite Nat.div_mul; [ | apply Pos.to_nat_neq_0 ].
destruct (Bool.bool_dec (Bool.eqb sa sb) sb) as [H1| H1]. {
  rewrite Nat.add_comm; cbn.
  destruct sa. {
    progress unfold Pos.of_nat.
    rewrite Nat_sub_succ_1.
    now destruct va.
  }
  now exfalso; destruct sb.
} {
  rewrite Nat.Div0.mod_mul; cbn.
  rewrite Nat.add_comm; cbn.
  destruct sa; [ now destruct sb | ].
  progress unfold Pos.of_nat.
  rewrite Nat_sub_succ_1.
  now destruct va.
}
Qed.

Theorem integral :
  ∀ a b : Z,
  (a * b)%Z = 0%Z
  → a = 0%Z ∨ b = 0%Z.
Proof.
intros * Hab; cbn.
destruct a as [| sa va]; [ now left | ].
destruct b as [| sb vb]; [ now right | ].
easy.
Qed.

Theorem compare_antisymm : ∀ a b, CompOpp (a ?= b)%Z = (b ?= a)%Z.
Proof.
intros.
destruct a as [| sa va]. {
  destruct b as [| sb vb]; [ easy | now destruct sb ].
}
destruct b as [| sb vb]; [ now destruct sa | cbn ].
destruct sa. {
  destruct sb; [ | easy ].
  symmetry; apply Nat.compare_antisym.
}
destruct sb; [ easy | ].
symmetry; apply Nat.compare_antisym.
Qed.

Theorem nle_gt : ∀ a b, ¬ (a ≤ b)%Z ↔ (b < a)%Z.
Proof.
intros.
progress unfold Z.le.
progress unfold Z.lt.
rewrite <- Z.compare_antisymm.
destruct (b ?= a)%Z; cbn; [ | easy | ].
split; [ now intros H1; exfalso; apply H1 | easy ].
split; [ now intros H1; exfalso; apply H1 | easy ].
Qed.

Theorem nlt_ge : ∀ a b, ¬ (a < b)%Z ↔ (b ≤ a)%Z.
Proof.
intros.
progress unfold Z.le.
progress unfold Z.lt.
rewrite <- Z.compare_antisymm.
now destruct (b ?= a)%Z.
Qed.

Theorem lt_le_incl : ∀ a b, (a < b)%Z → (a ≤ b)%Z.
Proof. intros * Hab; congruence. Qed.

Theorem lt_irrefl : ∀ a, ¬ (a < a)%Z.
Proof.
intros a Ha.
destruct a as [| sa va]; [ easy | ].
destruct sa. {
  apply Nat.compare_lt_iff in Ha.
  now apply Nat.lt_irrefl in Ha.
} {
  apply Nat.compare_lt_iff in Ha.
  now apply Nat.lt_irrefl in Ha.
}
Qed.

Theorem compare_eq_iff : ∀ a b, (a ?= b)%Z = Eq ↔ a = b.
Proof.
intros.
destruct a as [| sa va]; cbn. {
  destruct b as [| sb vb]; [ easy | now destruct sb ].
}
destruct b as [| sb vb]; [ now destruct sa | ].
destruct sa, sb; [ | easy | easy | ]. {
  rewrite Pos.compare_eq_iff.
  split; intros H; [ now subst vb | ].
  now injection H.
} {
  rewrite Pos.compare_eq_iff.
  split; intros H; [ now subst vb | ].
  now injection H.
}
Qed.

Theorem compare_neq_iff : ∀ a b, (a ?= b)%Z ≠ Eq ↔ a ≠ b.
Proof.
intros.
now split; intros H1 H2; apply H1; apply Z.compare_eq_iff.
Qed.

Theorem compare_lt_iff : ∀ a b, (a ?= b)%Z = Lt ↔ (a < b)%Z.
Proof. easy. Qed.

Theorem compare_le_iff : ∀ a b, (a ?= b)%Z ≠ Gt ↔ (a ≤ b)%Z.
Proof. easy. Qed.

Theorem compare_gt_iff : ∀ a b, (a ?= b)%Z = Gt ↔ (b < a)%Z.
Proof.
intros.
progress unfold Z.lt.
rewrite <- Z.compare_antisymm.
now destruct (b ?= a)%Z.
Qed.

Theorem le_antisymm : ∀ a b, (a ≤ b)%Z → (b ≤ a)%Z → a = b.
Proof.
intros * Hab Hba.
progress unfold le in Hab, Hba.
rewrite <- Z.compare_antisymm in Hba.
progress unfold CompOpp in Hba.
remember (a ?= b)%Z as ab eqn:H1.
symmetry in H1.
destruct ab; [ | easy | easy ].
now apply Z.compare_eq_iff.
Qed.

Theorem lt_iff : ∀ a b, (a < b)%Z ↔ (a ≤ b)%Z ∧ a ≠ b.
Proof.
intros.
split. {
  intros Hab.
  split; [ now apply Z.lt_le_incl | ].
  intros H; subst b.
  now apply Z.lt_irrefl in Hab.
}
intros (H1, H2).
apply nle_gt.
intros H3; apply H2.
now apply le_antisymm.
Qed.

Theorem add_sub_assoc : ∀ a b c, (a + (b - c) = a + b - c)%Z.
Proof.
intros.
progress unfold Z.sub.
apply Z.add_assoc.
Qed.

Theorem add_opp_diag_r : ∀ a, (a + - a = 0)%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | cbn ].
rewrite Bool.eqb_negb2.
now rewrite Pos.compare_refl.
Qed.

Theorem sub_diag : ∀ a, (a - a = 0)%Z.
Proof.
intros.
apply Z.add_opp_diag_r.
Qed.

Theorem add_sub : ∀ a b, (a + b - b = a)%Z.
Proof.
intros.
rewrite <- Z.add_sub_assoc.
rewrite Z.sub_diag.
apply Z.add_0_r.
Qed.

Theorem sub_add : ∀ a b, (a - b + b = a)%Z.
Proof.
intros.
rewrite Z.add_comm.
rewrite Z.add_sub_assoc.
rewrite Z.add_comm.
apply Z.add_sub.
Qed.

Theorem add_move_l : ∀ a b c, (a + b)%Z = c ↔ b = (c - a)%Z.
Proof.
intros.
split; intros Hab. {
  subst c; symmetry.
  rewrite Z.add_comm.
  apply Z.add_sub.
} {
  subst b.
  rewrite Z.add_sub_assoc.
  rewrite Z.add_comm.
  apply Z.add_sub.
}
Qed.

Theorem add_move_r : ∀ a b c, (a + b)%Z = c ↔ a = (c - b)%Z.
Proof.
intros.
rewrite Z.add_comm.
apply Z.add_move_l.
Qed.

Theorem add_move_0_l : ∀ a b, (a + b)%Z = 0%Z ↔ b = (- a)%Z.
Proof.
intros.
apply (Z.add_move_l a b 0).
Qed.

Theorem add_move_0_r : ∀ a b, (a + b)%Z = 0%Z ↔ a = (- b)%Z.
Proof.
intros.
apply (Z.add_move_r a b 0).
Qed.

Theorem sub_move_0_r : ∀ a b, (a - b)%Z = 0%Z ↔ a = b.
Proof.
intros.
progress unfold Z.sub.
rewrite <- (Z.opp_involutive b) at 2.
apply Z.add_move_0_r.
Qed.

Theorem le_trans : ∀ a b c, (a ≤ b → b ≤ c → a ≤ c)%Z.
Proof.
intros * Hab Hbc.
progress unfold Z.le in Hab, Hbc |-*.
progress unfold Z.compare in Hab, Hbc |-*.
destruct a as [| sa va]. {
  destruct c as [| sc vc]; [ easy | ].
  destruct sc; [ easy | exfalso ].
  destruct b as [| sb vb]; [ easy | ].
  now destruct sb.
}
destruct c as [| sc vc]. {
  destruct sa; [ exfalso | easy ].
  destruct b as [| sb vb]; [ easy | ].
  now destruct sb.
}
destruct b as [| sb vb]. {
  destruct sa; [ easy | now destruct sc ].
}
destruct sa. {
  destruct sb; [ | easy ].
  destruct sc; [ | easy ].
  apply Pos.compare_le_iff in Hab, Hbc.
  apply Pos.compare_le_iff.
  now transitivity vb.
}
destruct sc; [ easy | ].
destruct sb; [ easy | ].
apply Pos.compare_le_iff in Hab, Hbc.
apply Pos.compare_le_iff.
now transitivity vb.
Qed.

Add Parametric Relation : _ Z.le
  transitivity proved by Z.le_trans
as le_rel.

Theorem compare_add_mono_l :
  ∀ a b c, (a + b ?= a + c)%Z = (b ?= c)%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]. {
  destruct c as [| sc vc]; [ now rewrite Z.compare_eq_iff | ].
  rewrite Z.add_0_r; cbn.
  rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec sa sc) as [Hsac| Hsac]. {
    subst sc.
    destruct sa.
    apply Nat.compare_lt_iff; cbn; flia.
    apply Nat.compare_gt_iff; cbn; flia.
  }
  remember (va ?= vc)%pos as vac eqn:Hvac.
  symmetry in Hvac.
  destruct sa. {
    destruct sc; [ easy | ].
    destruct vac; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hvac.
    apply Nat.compare_gt_iff.
    cbn; flia Hvac.
  } {
    destruct sc; [ | easy ].
    destruct vac; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hvac.
    apply Nat.compare_lt_iff.
    cbn; flia Hvac.
  }
}
destruct c as [| sc vc]. {
  rewrite Z.add_0_r; cbn.
  rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec sa sb) as [Hsab| Hsab]. {
    subst sb.
    destruct sa.
    apply Nat.compare_gt_iff; cbn; flia.
    apply Nat.compare_lt_iff; cbn; flia.
  }
  remember (va ?= vb)%pos as vab eqn:Hvab.
  symmetry in Hvab.
  destruct sb. {
    destruct sa; [ easy | ].
    destruct vab; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hvab.
    apply Nat.compare_gt_iff.
    cbn; flia Hvab.
  } {
    destruct sa; [ | easy ].
    destruct vab; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hvab.
    apply Nat.compare_lt_iff.
    cbn; flia Hvab.
  }
}
destruct (Bool.bool_dec sa sb) as [Hsab| Hsab]. {
  subst sb.
  cbn; rewrite Bool.eqb_reflx.
  rewrite if_eqb_bool_dec.
  destruct (Bool.bool_dec sa sc) as [Hsac| Hsac]. {
    subst sc.
    destruct sa; cbn. {
      rewrite Nat_compare_add_mono_r.
      rewrite Nat_compare_add_mono_l.
      easy.
    } {
      rewrite Nat_compare_add_mono_r.
      rewrite Nat_compare_add_mono_l.
      easy.
    }
  }
  remember (va ?= vc)%pos as vac eqn:Hvac.
  symmetry in Hvac.
  destruct sa. {
    destruct sc; [ easy | ].
    destruct vac; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hvac.
    apply Nat.compare_gt_iff.
    cbn; flia Hvac.
  } {
    destruct sc; [ | easy ].
    destruct vac; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hvac.
    apply Nat.compare_lt_iff.
    cbn; flia Hvac.
  }
}
destruct (Bool.bool_dec sa sc) as [Hsac| Hsac]. {
  subst sc.
  cbn; rewrite Bool.eqb_reflx.
  rewrite (proj2 (Bool.eqb_false_iff _ _) Hsab).
  remember (va ?= vb)%pos as vab eqn:Hvab.
  symmetry in Hvab.
  destruct sb. {
    destruct sa; [ easy | ].
    destruct vab; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hvab.
    apply Nat.compare_gt_iff.
    cbn; flia Hvab.
  } {
    destruct sa; [ | easy ].
    destruct vab; [ easy | easy | ].
    apply Nat.compare_gt_iff in Hvab.
    apply Nat.compare_lt_iff.
    cbn; flia Hvab.
  }
}
remember (va ?= vb)%pos as vab eqn:Hvab.
remember (va ?= vc)%pos as vac eqn:Hvac.
symmetry in Hvab, Hvac.
destruct sb. {
  destruct sa; [ easy | ].
  destruct sc; [ | easy ].
  cbn; rewrite Hvab, Hvac.
  destruct vab. {
    apply Pos.compare_eq_iff in Hvab; subst vb.
    now destruct vac.
  } {
    apply Pos.compare_lt_iff in Hvab.
    destruct vac. {
      apply Pos.compare_eq_iff in Hvac; subst vc.
      now symmetry; apply Nat.compare_gt_iff.
    } {
      apply Pos.compare_lt_iff in Hvac.
      cbn - [ Pos.sub ].
      now apply Pos.compare_sub_mono_r.
    } {
      apply Pos.compare_gt_iff in Hvac; cbn.
      symmetry; apply Pos.compare_gt_iff.
      now transitivity va.
    }
  } {
    apply Pos.compare_gt_iff in Hvab.
    destruct vac. {
      cbn; symmetry.
      apply Pos.compare_lt_iff.
      now apply Pos.compare_eq_iff in Hvac; subst.
    } {
      apply Pos.compare_lt_iff in Hvac; cbn.
      symmetry; apply Pos.compare_lt_iff.
      now transitivity va.
    } {
      apply Pos.compare_gt_iff in Hvac.
      cbn - [ Pos.sub ].
      now rewrite Pos.compare_sub_mono_l.
    }
  }
}
destruct sa; [ | easy ].
destruct sc; [ easy | ].
cbn - [ Z.add ].
destruct vab. {
  cbn; rewrite Hvab, Hvac.
  apply Pos.compare_eq_iff in Hvab; subst vb.
  destruct vac. {
    apply Pos.compare_eq_iff in Hvac; subst vc.
    now symmetry; apply Nat.compare_eq_iff.
  } {
    apply Pos.compare_lt_iff in Hvac; cbn.
    now symmetry; apply Nat.compare_gt_iff.
  } {
    apply Pos.compare_gt_iff in Hvac; cbn.
    now symmetry; apply Nat.compare_lt_iff.
  }
} {
  cbn; rewrite Hvab, Hvac.
  apply Pos.compare_lt_iff in Hvab.
  destruct vac. {
    apply Pos.compare_eq_iff in Hvac; subst vc.
    now symmetry; apply Nat.compare_lt_iff.
  } {
    progress unfold Pos.lt in Hvab.
    apply Nat.compare_lt_iff in Hvac; cbn.
    rewrite Nat_compare_sub_mono_r; [ | flia Hvac | flia Hvab ].
    apply Nat.lt_le_incl in Hvab, Hvac.
    now rewrite Nat_compare_sub_mono_r.
  } {
    apply Pos.compare_gt_iff in Hvac; cbn.
    symmetry; apply Pos.compare_lt_iff.
    now transitivity va.
  }
} {
  cbn; rewrite Hvab, Hvac.
  apply Pos.compare_gt_iff in Hvab.
  destruct vac. {
    apply Pos.compare_eq_iff in Hvac; subst vc.
    now symmetry; apply Nat.compare_gt_iff.
  } {
    apply Pos.compare_lt_iff in Hvac; cbn.
    symmetry; apply Pos.compare_gt_iff.
    now transitivity va.
  } {
    apply Pos.compare_gt_iff in Hvac.
    cbn - [ Pos.sub ].
    now apply Pos.compare_sub_mono_l.
  }
}
Qed.

Theorem compare_add_mono_r :
  ∀ a b c, (a + c ?= b + c)%Z = (a ?= b)%Z.
Proof.
intros.
do 2 rewrite (Z.add_comm _ c).
apply Z.compare_add_mono_l.
Qed.

Theorem compare_opp : ∀ a b, (- a ?= - b)%Z = (b ?= a)%Z.
Proof.
intros.
destruct a as [| sa va]. {
  destruct b as [| sb vb]; [ easy | now destruct sb ].
}
destruct b as [| sb vb]; [ now destruct sa | ].
now destruct sa, sb; cbn.
Qed.

Theorem compare_sub_mono_l :
  ∀ a b c, (a - b ?= a - c)%Z = (c ?= b)%Z.
Proof.
intros.
progress unfold Z.sub.
rewrite Z.compare_add_mono_l.
apply Z.compare_opp.
Qed.

Theorem compare_sub_mono_r :
  ∀ a b c, (a - c ?= b - c)%Z = (a ?= b)%Z.
Proof.
intros.
progress unfold Z.sub.
now rewrite Z.compare_add_mono_r.
Qed.

Theorem le_add_l : ∀ a b, (0 ≤ a)%Z → (b ≤ a + b)%Z.
Proof.
progress unfold Z.le.
intros * H Hza; apply H; clear H.
rewrite <- Hza.
rewrite <- (Z.add_0_l b) at 1.
symmetry; apply Z.compare_add_mono_r.
Qed.

Theorem le_add_r : ∀ a b, (0 ≤ a)%Z → (b ≤ b + a)%Z.
Proof.
intros * Hza.
rewrite Z.add_comm.
now apply Z.le_add_l.
Qed.

Theorem lt_add_l : ∀ a b, (0 < a)%Z → (b < a + b)%Z.
Proof.
progress unfold Z.lt.
intros * Hza.
rewrite <- Hza.
rewrite <- (Z.add_0_l b) at 1.
apply Z.compare_add_mono_r.
Qed.

Theorem lt_add_r : ∀ a b, (0 < a)%Z → (b < b + a)%Z.
Proof.
intros * Hza.
rewrite Z.add_comm.
now apply Z.lt_add_l.
Qed.

(*
Theorem characteristic_prop : ∀ i : nat, rngl_of_nat (S i) ≠ 0%Z.
Proof.
intros * Hn.
rewrite rngl_of_nat_succ in Hn.
apply Z.add_move_0_l in Hn.
cbn in Hn.
enough (H : (0 ≤ rngl_of_nat i)%Z) by now rewrite Hn in H.
clear Hn.
induction i; [ easy | ].
rewrite rngl_of_nat_succ.
etransitivity; [ apply IHi | ].
now apply Z.le_add_l.
Qed.
*)

Theorem leb_refl : ∀ a, (a ≤? a)%Z = true.
Proof.
intros.
progress unfold Z.leb.
destruct a as [| sa va]; [ easy | cbn ].
now destruct sa; rewrite Pos.compare_refl.
Qed.

Theorem add_le_mono_l_if : ∀ a b c, (a ≤ b)%Z → (c + a ≤ c + b)%Z.
Proof.
intros * Hab.
progress unfold Z.le in Hab |-*.
now rewrite Z.compare_add_mono_l.
Qed.

Theorem add_le_mono_l : ∀ a b c, (b ≤ c)%Z ↔ (a + b ≤ a + c)%Z.
Proof.
intros.
progress unfold Z.le.
now rewrite Z.compare_add_mono_l.
Qed.

Theorem add_le_mono_r : ∀ a b c, (a ≤ b)%Z ↔ (a + c ≤ b + c)%Z.
Proof.
intros.
do 2 rewrite (Z.add_comm _ c).
apply Z.add_le_mono_l.
Qed.

Theorem add_lt_mono_l : ∀ a b c, (b < c)%Z ↔ (a + b < a + c)%Z.
Proof.
intros.
progress unfold Z.lt.
now rewrite Z.compare_add_mono_l.
Qed.

Theorem sub_le_mono_l : ∀ a b c, (c ≤ b)%Z ↔ (a - b ≤ a - c)%Z.
Proof.
intros.
progress unfold Z.le.
now rewrite Z.compare_sub_mono_l.
Qed.

Theorem sub_le_mono_r : ∀ a b c, (a ≤ b)%Z ↔ (a - c ≤ b - c)%Z.
Proof.
intros.
progress unfold Z.le.
now rewrite Z.compare_sub_mono_r.
Qed.

Theorem sub_lt_mono_l : ∀ a b c, (c < b)%Z ↔ (a - b < a - c)%Z.
Proof.
intros.
progress unfold Z.lt.
now rewrite Z.compare_sub_mono_l.
Qed.

Theorem sub_lt_mono_r : ∀ a b c, (a < b)%Z ↔ (a - c < b - c)%Z.
Proof.
intros.
progress unfold Z.lt.
now rewrite Z.compare_sub_mono_r.
Qed.

Theorem compare_mul_mono_pos_l :
  ∀ a b c, (0 < a)%Z → (a * b ?= a * c)%Z = (b ?= c)%Z.
Proof.
intros * Hza.
destruct a as [| sa va]; [ easy | ].
destruct sa; [ clear Hza | easy ].
destruct b as [| sb vb]. {
  destruct c as [| sc vc]; [ easy | now destruct sc ].
}
destruct c as [| sc vc]; [ now destruct sb | ].
destruct sb. {
  destruct sc; [ cbn | easy ].
  rewrite Nat_compare_sub_mono_r; [ | easy | easy ].
  rewrite Nat_compare_mul_mono_l; [ | now rewrite Nat.add_1_r ].
  now rewrite Nat_compare_add_mono_r.
} {
  destruct sc; [ easy | cbn ].
  rewrite Nat_compare_sub_mono_r; [ | easy | easy ].
  rewrite Nat_compare_mul_mono_l; [ | now rewrite Nat.add_1_r ].
  now rewrite Nat_compare_add_mono_r.
}
Qed.

Theorem compare_mul_mono_pos_r :
  ∀ a b c, (0 < c)%Z → (a * c ?= b * c)%Z = (a ?= b)%Z.
Proof.
intros * Hza.
do 2 rewrite (Z.mul_comm _ c).
now apply Z.compare_mul_mono_pos_l.
Qed.

Theorem compare_mul_mono_neg_l :
  ∀ a b c, (a < 0)%Z → (a * b ?= a * c)%Z = (c ?= b)%Z.
Proof.
intros * Hza.
destruct a as [| sa va]; [ easy | ].
destruct sa; [ easy | clear Hza ].
destruct b as [| sb vb]. {
  destruct c as [| sc vc]; [ easy | now destruct sc ].
}
destruct c as [| sc vc]; [ now destruct sb | ].
destruct sb. {
  destruct sc; [ cbn | easy ].
  rewrite Nat_compare_sub_mono_r; [ | easy | easy ].
  rewrite Nat_compare_mul_mono_l; [ | now rewrite Nat.add_1_r ].
  now rewrite Nat_compare_add_mono_r.
} {
  destruct sc; [ easy | cbn ].
  rewrite Nat_compare_sub_mono_r; [ | easy | easy ].
  rewrite Nat_compare_mul_mono_l; [ | now rewrite Nat.add_1_r ].
  now rewrite Nat_compare_add_mono_r.
}
Qed.

Theorem mul_le_mono_nonneg_l :
  ∀ a b c, (0 ≤ a)%Z → (b ≤ c)%Z → (a * b ≤ a * c)%Z.
Proof.
intros * Hza Hbc.
destruct (Z.eq_dec a 0) as [Haz| Haz]; [ now rewrite Haz | ].
progress unfold Z.le.
rewrite Z.compare_mul_mono_pos_l; [ easy | ].
now apply Z.lt_iff.
Qed.

Theorem mul_le_mono_nonneg_r :
  ∀ a b c, (0 ≤ a)%Z → (b ≤ c)%Z → (b * a ≤ c * a)%Z.
Proof.
intros * Hza Hbc.
do 2 rewrite (Z.mul_comm _ a).
now apply Z.mul_le_mono_nonneg_l.
Qed.

Theorem mul_le_mono_nonpos_l :
  ∀ a b c, (a ≤ 0)%Z → (b ≤ c)%Z → (a * c ≤ a * b)%Z.
Proof.
intros * Hza Hbc.
destruct (Z.eq_dec a 0) as [Haz| Haz]; [ now rewrite Haz | ].
progress unfold Z.le in Hbc |-*.
intros H.
apply Hbc; clear Hbc.
rewrite <- H.
symmetry.
apply Z.compare_mul_mono_neg_l.
now apply Z.lt_iff.
Qed.

Theorem mul_le_mono_nonpos_r :
  ∀ a b c, (c ≤ 0)%Z → (b ≤ a)%Z → (a * c ≤ b * c)%Z.
Proof.
intros * Hzc Hba.
do 2 rewrite (Z.mul_comm _ c).
now apply Z.mul_le_mono_nonpos_l.
Qed.

Theorem add_le_compat : ∀ a b c d, (a ≤ b)%Z → (c ≤ d)%Z → (a + c ≤ b + d)%Z.
Proof.
intros * Hab Hcd.
transitivity (a + d)%Z; [ apply Z.add_le_mono_l, Hcd | ].
do 2 rewrite (Z.add_comm _ d).
now apply Z.add_le_mono_l.
Qed.

Theorem mul_opp_l : ∀ a b, (- a * b)%Z = (- (a * b))%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | cbn ].
now destruct sa, sb.
Qed.

Theorem mul_opp_r : ∀ a b, (a * - b)%Z = (- (a * b))%Z.
Proof.
intros.
do 2 rewrite (Z.mul_comm a).
apply Z.mul_opp_l.
Qed.

Theorem mul_le_compat_nonneg :
  ∀ a b c d, (0 ≤ a ≤ c)%Z → (0 ≤ b ≤ d)%Z → (a * b ≤ c * d)%Z.
Proof.
intros * Hac Hbd.
transitivity (a * d)%Z; [ now apply Z.mul_le_mono_nonneg_l | ].
do 2 rewrite (Z.mul_comm _ d).
apply Z.mul_le_mono_nonneg_l; [ | easy ].
now transitivity b.
Qed.

Theorem mul_le_compat_nonpos :
  ∀ a b c d : Z, (c ≤ a ≤ 0)%Z → (d ≤ b ≤ 0)%Z → (a * b ≤ c * d)%Z.
Proof.
intros * Hca Hdb.
transitivity (a * d)%Z; [ now apply Z.mul_le_mono_nonpos_l | ].
do 2 rewrite (Z.mul_comm _ d).
apply Z.mul_le_mono_nonpos_l; [ | easy ].
now transitivity b.
Qed.

Theorem leb_le : ∀ a b, (a ≤? b)%Z = true ↔ (a ≤ b)%Z.
Proof.
intros.
progress unfold Z.leb.
progress unfold Z.le.
now destruct (a ?= b)%Z.
Qed.

Theorem leb_antisymm : ∀ a b, (a ≤? b)%Z = true → (b ≤? a)%Z = true → a = b.
Proof.
intros * Hab Hba.
apply Z.leb_le in Hab, Hba.
now apply (Z.le_antisymm a b).
Qed.

Theorem leb_trans :
  ∀ a b c, (a ≤? b)%Z = true → (b ≤? c)%Z = true → (a ≤? c)%Z = true.
Proof.
intros * Hab Hbc.
apply Z.leb_le in Hab, Hbc.
apply Z.leb_le.
now apply (Z.le_trans a b c).
Qed.

Theorem add_leb_compat :
  ∀ a b c d,
  (a ≤? b)%Z = true
  → (c ≤? d)%Z = true
  → (a + c ≤? b + d)%Z = true.
Proof.
intros * Hab Hcd.
apply Z.leb_le in Hab, Hcd.
apply Z.leb_le.
now apply Z.add_le_compat.
Qed.

Theorem mul_leb_compat_nonneg :
  ∀ a b c d : Z,
  (0 ≤? a)%Z = true ∧ (a ≤? c)%Z = true
  → (0 ≤? b)%Z = true ∧ (b ≤? d)%Z = true
  → (a * b ≤? c * d)%Z = true.
Proof.
intros * (Hza, Hac) (Hzb, Hbd).
apply Z.leb_le in Hza, Hac, Hzb, Hbd.
apply Z.leb_le.
now apply Z.mul_le_compat_nonneg.
Qed.

Theorem mul_leb_compat_nonpos :
  ∀ a b c d : Z,
  (c ≤? a)%Z = true ∧ (a ≤? 0)%Z = true
  → (d ≤? b)%Z = true ∧ (b ≤? 0)%Z = true
  → (a * b ≤? c * d)%Z = true.
Proof.
intros * (Hza, Hac) (Hzb, Hbd).
apply Z.leb_le in Hza, Hac, Hzb, Hbd.
apply Z.leb_le.
now apply Z.mul_le_compat_nonpos.
Qed.

Theorem not_leb : ∀ a b, (a ≤? b)%Z ≠ true → a ≠ b ∧ (b ≤? a)%Z = true.
Proof.
intros * Hab.
progress unfold Z.leb in Hab |-*.
rewrite <- Z.compare_antisymm.
remember (a ?= b)%Z as ab eqn:H1.
symmetry in H1.
destruct ab; [ easy | easy | cbn ].
progress unfold Z.compare in H1.
split; [ | easy ].
intros H; subst b.
destruct a as [| sa va]; [ easy | cbn in H1 ].
now destruct sa; rewrite Pos.compare_refl in H1.
Qed.

(*
Instance ring_like_ord : ring_like_ord Z :=
  {| rngl_ord_le_dec := (λ a b, Bool.bool_dec (a ≤? b)%Z true);
     rngl_ord_le_refl := Z.leb_refl;
     rngl_ord_le_antisymm := Z.leb_antisymm;
     rngl_ord_le_trans := Z.leb_trans;
     rngl_ord_add_le_compat := Z.add_leb_compat;
     rngl_ord_mul_le_compat_nonneg := Z.mul_leb_compat_nonneg;
     rngl_ord_mul_le_compat_nonpos := Z.mul_leb_compat_nonpos;
     rngl_ord_not_le := Z.not_leb |}.

(* borrowed from ring-like, file Z_algebra *)
Theorem rngl_mul_nat_Z : ∀ z n, rngl_mul_nat z n = (Z.of_nat n * z)%Z.
Proof.
intros.
progress unfold rngl_mul_nat.
progress unfold mul_nat; cbn.
induction n; intros; [ easy | ].
cbn - [ "*"%Z ].
rewrite IHn.
rewrite <- (Z.mul_1_l z) at 1.
rewrite <- Z.mul_add_distr_r.
progress f_equal.
progress unfold Z.of_nat.
destruct n; [ easy | cbn; f_equal ].
progress unfold Pos.add; cbn.
progress unfold Pos.of_nat; cbn.
rewrite Nat.sub_0_r.
f_equal.
apply Nat.add_1_r.
Qed.
*)

Theorem nat_archimedean : ∀ a b, (0 < a → ∃ n, b < n * a)%nat.
Proof.
intros * Ha.
exists (S b); simpl.
induction b; [ now rewrite Nat.add_0_r | ].
simpl; rewrite <- Nat.add_1_l.
now apply Nat.add_le_lt_mono.
Qed.

Theorem pos_archimedean : ∀ a b,  ∃ n, (b < Pos.of_nat n * a)%pos.
Proof.
intros.
destruct a as (a).
destruct b as (b).
progress unfold Pos.lt; cbn.
specialize (nat_archimedean (S a) (S b) (Nat.lt_0_succ _)) as H1.
destruct H1 as (n, Hn).
exists n.
rewrite Nat.sub_add; flia Hn.
Qed.

Theorem archimedean : ∀ a b, (0 < a → ∃ n, b < Z.of_nat n * a)%Z.
Proof.
intros * Ha.
destruct b as [| sb vb]; [ now exists 1; rewrite Z.mul_1_l | ].
destruct a as [| sa va]; [ easy | ].
destruct sa; [ | easy ].
specialize (pos_archimedean va vb) as (m, Hm).
destruct m. {
  exists 1.
  destruct sb; [ now apply Pos.compare_lt_iff | easy ].
}
exists (S m); cbn.
destruct sb; [ | easy ].
progress unfold Z.lt; cbn.
now apply Pos.compare_lt_iff.
Qed.

(*
Theorem archimedean_b :
(*
  ∀ a b, (0 < a)%L → ∃ n : nat, (rngl_mul_nat a n ≤? b)%Z = false.
cbn.
Print rngl_lt.
*)
  ∀ a b, (a ≤? 0)%Z = false → ∃ n : nat, (rngl_mul_nat a n ≤? b)%Z = false.
Proof.
intros * Haz.
assert (Ha : (0 < a)%Z). {
  apply Bool.not_true_iff_false in Haz.
  apply Z.not_leb in Haz.
  destruct Haz as (Haz, Hza).
  apply Z.leb_le in Hza.
  destruct a as [| sa va]; [ easy | ].
  now destruct sa.
}
apply (Z.archimedean a b) in Ha.
destruct Ha as (n, Ha).
rewrite <- rngl_mul_nat_Z in Ha.
exists n.
progress unfold Z.lt in Ha.
progress unfold Z.compare in Ha.
destruct b as [| sb vb]. {
  destruct (rngl_mul_nat a n); [ easy | now destruct b ].
}
destruct (rngl_mul_nat a n) as [| sc vc]; [ now destruct sb | ].
destruct sb, sc; [ | easy | easy | ]. {
  rewrite Pos.compare_antisym in Ha.
  progress unfold CompOpp in Ha.
  progress unfold Z.leb; cbn.
  now destruct (vc ?= vb)%pos.
} {
  rewrite Pos.compare_antisym in Ha.
  progress unfold CompOpp in Ha.
  progress unfold Z.leb; cbn.
  now destruct (vb ?= vc)%pos.
}
Qed.

Instance ring_like_prop : ring_like_prop Z :=
  {| rngl_mul_is_comm := true;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Z.add_comm;
     rngl_add_assoc := Z.add_assoc;
     rngl_add_0_l := Z.add_0_l;
     rngl_mul_assoc := Z.mul_assoc;
     rngl_opt_mul_1_l := Z.mul_1_l;
     rngl_mul_add_distr_l := Z.mul_add_distr_l;
     rngl_opt_mul_comm := Z.mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_diag_l := Z.add_opp_diag_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_sub_0_l := NA;
     rngl_opt_mul_inv_diag_l := NA;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := Z.mul_div;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_integral := Z.integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := Z.characteristic_prop;
     rngl_opt_ord := Z.ring_like_ord;
     rngl_opt_archimedean := Z.archimedean_b |}.
*)

Theorem opp_add_distr : ∀ a b, (- (a + b))%Z = (- a - b)%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | ].
destruct sa. {
  destruct sb; [ easy | cbn ].
  now destruct (va ?= vb)%pos.
}
destruct sb; [ now cbn; destruct (va ?= vb)%pos | easy ].
Qed.

Theorem opp_sub_distr : ∀ a b, (- (a - b))%Z = (b - a)%Z.
Proof.
intros.
progress unfold Z.sub.
rewrite Z.opp_add_distr.
progress unfold Z.sub.
rewrite Z.opp_involutive.
apply Z.add_comm.
Qed.

Theorem eqb_refl : ∀ a, (a =? a)%Z = true.
Proof.
intros.
destruct a as [| sa va]; [ easy | cbn ].
rewrite Bool.eqb_reflx.
apply Pos.eqb_refl.
Qed.

Theorem eqb_eq : ∀ a b, (a =? b)%Z = true ↔ a = b.
Proof.
intros.
split; intros Hab; [ | subst b; apply eqb_refl ].
destruct a as [| sa va]; [ now destruct b | ].
destruct b as [| sb vb]; [ easy | ].
cbn in Hab.
apply Bool.andb_true_iff in Hab.
destruct Hab as (H1, H2).
apply Pos.eqb_eq in H2; subst vb.
now destruct sa, sb.
Qed.

Theorem mul_le_mono_pos_l :
  ∀ a b c, (0 < a)%Z → (b ≤ c)%Z ↔ (a * b ≤ a * c)%Z.
Proof.
intros * Hza.
progress unfold Z.le.
now rewrite Z.compare_mul_mono_pos_l.
Qed.

Theorem mul_le_mono_pos_r :
  ∀ a b c, (0 < a)%Z → (b ≤ c)%Z ↔ (b * a ≤ c * a)%Z.
Proof.
intros * Hlt.
do 2 rewrite (Z.mul_comm _ a).
now apply Z.mul_le_mono_pos_l.
Qed.

Theorem mul_lt_mono_pos_l :
  ∀ a b c, (0 < a)%Z → (b < c)%Z ↔ (a * b < a * c)%Z.
Proof.
intros * Hza.
progress unfold Z.lt.
now rewrite Z.compare_mul_mono_pos_l.
Qed.

Theorem mul_lt_mono_pos_r :
  ∀ a b c, (0 < a)%Z → (b < c)%Z ↔ (b * a < c * a)%Z.
Proof.
intros * Hlt.
do 2 rewrite (Z.mul_comm _ a).
now apply Z.mul_lt_mono_pos_l.
Qed.

Theorem mul_cancel_l : ∀ a b c, a ≠ 0%Z → (a * b)%Z = (a * c)%Z → b = c.
Proof.
intros * Haz Habc.
do 2 rewrite (mul_comm a) in Habc.
apply (f_equal (λ x, div x a)) in Habc.
rewrite Z.mul_div in Habc; [ | easy ].
rewrite Z.mul_div in Habc; [ | easy ].
easy.
Qed.

Theorem mul_cancel_r : ∀ a b c, c ≠ 0%Z → (a * c)%Z = (b * c)%Z → a = b.
Proof.
intros * Haz Habc.
do 2 rewrite (mul_comm _ c) in Habc.
now apply mul_cancel_l in Habc.
Qed.

Theorem le_refl : ∀ a, (a ≤ a)%Z.
Proof.
intros a.
destruct a as [| sa va]; [ easy | ].
progress unfold Z.le; cbn.
now destruct sa; apply Nat.compare_le_iff.
Qed.

Theorem mul_nonneg_nonneg : ∀ a b, (0 ≤ a → 0 ≤ b → 0 ≤ a * b)%Z.
Proof.
intros * Hz1 Hz2.
destruct a as [| sa va]; [ apply Z.le_refl | ].
destruct b as [| sb vb]; [ apply Z.le_refl | ].
now destruct sa, sb.
Qed.

Theorem mul_pos_pos : ∀ a b, (0 < a → 0 < b → 0 < a * b)%Z.
Proof.
intros * Hz1 Hz2.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | ].
destruct sa; [ now destruct sb | easy ].
Qed.

Theorem mul_neg_neg : ∀ a b, (a < 0 → b < 0 → 0 < a * b)%Z.
Proof.
intros * Hz1 Hz2.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | ].
destruct sa; [ easy | now destruct sb ].
Qed.

Theorem mul_nonpos_nonneg : ∀ a b, (a ≤ 0 → 0 ≤ b → a * b ≤ 0)%Z.
Proof.
intros * Hle1 Hle2.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | ].
destruct sa; [ easy | now destruct sb ].
Qed.

Theorem of_nat_pos_to_nat : ∀ a, Z.of_nat (Pos.to_nat a) = z_val true a.
Proof.
intros.
progress unfold Z.of_nat.
remember (Pos.to_nat a) as b eqn:Hb.
symmetry in Hb.
destruct b; [ now apply Pos.to_nat_neq_0 in Hb | ].
f_equal.
rewrite <- Hb.
apply Pos.of_nat_to_nat.
Qed.

Theorem sgn_mul : ∀ a b, Z.sgn (a * b) = (Z.sgn a * Z.sgn b)%Z.
Proof.
intros.
progress unfold Z.sgn.
destruct a as [| sa va]; [ easy | ].
destruct sa.
destruct b as [| sb vb]; [ easy | now destruct sb ].
destruct b as [| sb vb]; [ easy | now destruct sb ].
Qed.

Theorem abs_sgn : ∀ a, Z.abs a = (Z.sgn a * a)%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | cbn ].
rewrite Z.of_nat_pos_to_nat.
symmetry.
destruct sa; [ apply Z.mul_1_l | cbn ].
f_equal; apply Pos.mul_1_l.
Qed.

Theorem le_dec : ∀ a b : Z, ({a ≤ b} + {¬ a ≤ b})%Z.
Proof.
intros.
destruct a as [| sa va]. {
  destruct b as [| sb vb]; [ now left | ].
  now destruct sb; [ left | right ].
} {
  destruct b as [| sb vb]. {
    now destruct sa; [ right | left ].
  }
  progress unfold Z.le; cbn.
  destruct sa. {
    destruct sb; [ | now right ].
    now destruct (va ?= vb)%pos; [ left | left | right ].
  }
  destruct sb; [ now left | ].
  now destruct (vb ?= va)%pos; [ left | left | right ].
}
Qed.

Theorem lt_dec : ∀ a b, ({a < b} + {¬ (a < b)})%Z.
Proof.
intros.
destruct (Z.le_dec b a) as [Hba| Hba].
now right; apply Z.nlt_ge.
now left; apply Z.nle_gt in Hba.
Qed.

Theorem lt_le_dec: ∀ a b, ({a < b} + {b ≤ a})%Z.
Proof.
intros.
destruct (Z.le_dec b a) as [Hba| Hba]; [ now right | left ].
now apply Z.nle_gt in Hba.
Qed.

Theorem pos_abs_nonneg : ∀ a, (0 ≤ a)%Z → Z.pos_abs a = Z.to_pos a.
Proof.
intros * Haz.
destruct a as [| sa va]; [ easy | now destruct sa ].
Qed.

Theorem pos_abs_nonpos : ∀ a, (a ≤ 0)%Z → Z.pos_abs a = Z.to_pos (- a).
Proof.
intros * Haz.
destruct a as [| sa va]; [ easy | now destruct sa ].
Qed.

Theorem abs_nonneg_eq : ∀ a, (0 ≤ a)%Z → Z.abs a = a.
Proof.
intros * Haz.
destruct a as [| sa va]; [ easy | ].
destruct sa; [ clear Haz; cbn | easy ].
apply Z.of_nat_pos_to_nat.
Qed.

Theorem abs_nonpos_eq : ∀ a, (a ≤ 0)%Z → Z.abs a = (- a)%Z.
Proof.
intros * Haz.
destruct a as [| sa va]; [ easy | ].
destruct sa; [ easy | clear Haz; cbn ].
apply Z.of_nat_pos_to_nat.
Qed.

Theorem abs_pos : ∀ a, (0 < Z.abs a ↔ a ≠ 0)%Z.
Proof.
intros.
split; intros H; [ now intros H1; subst | ].
destruct a as [| sa va]; [ easy | ].
now destruct sa; cbn; rewrite Z.of_nat_pos_to_nat.
Qed.

Theorem opp_le_compat : ∀ a b, (a ≤ b ↔ - b ≤ - a)%Z.
Proof.
intros.
destruct a as [| sa va]. {
  destruct b as [| sb vb]; [ easy | now destruct sb ].
}
destruct b as [| sb vb]; [ now destruct sa | cbn ].
now destruct sa, sb.
Qed.

Theorem sub_0_r : ∀ a, (a - 0 = a)%Z.
Proof. intros; apply Z.add_0_r. Qed.

Theorem compare_0_sub : ∀ a b, (0 ?= a - b)%Z = (b ?= a)%Z.
Proof.
intros.
destruct a as [| sa va]. {
  destruct b as [| sb vb]; [ easy | now destruct sb ].
}
destruct b as [| sb vb]; [ easy | cbn ].
rewrite Pos.compare_antisym.
destruct sa. {
  destruct sb; [ cbn | easy ].
  now destruct (vb ?= va)%pos.
} {
  destruct sb; [ easy | cbn ].
  now destruct (vb ?= va)%pos.
}
Qed.

Theorem lt_0_sub : ∀ a b, (0 < b - a)%Z ↔ (a < b)%Z.
Proof.
intros.
progress unfold Z.lt.
now rewrite Z.compare_0_sub.
Qed.

Theorem lt_asymm : ∀ a b, (a < b)%Z → ¬ (b < a)%Z.
Proof.
intros * Hab.
now apply Z.nlt_ge, Z.lt_le_incl.
Qed.

Theorem abs_nonneg : ∀ a, (0 ≤ Z.abs a)%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | cbn ].
progress unfold Pos.to_nat.
now rewrite Nat.add_1_r.
Qed.

Theorem Nat2Z_inj_mul :
  ∀ a b, Z.of_nat (a * b) = (Z.of_nat a * Z.of_nat b)%Z.
Proof.
intros.
progress unfold Z.mul.
progress unfold Z.of_nat.
destruct a; [ easy | ].
rewrite Nat.mul_comm.
destruct b; [ easy | cbn ].
rewrite <- Pos.of_nat_mul; [ | easy | easy ].
f_equal; f_equal; flia.
Qed.

Theorem abs_mul : ∀ a b, Z.abs (a * b) = (Z.abs a * Z.abs b)%Z.
Proof.
intros.
destruct a as [| sa va]; [ easy | ].
rewrite (Z.mul_comm _ b), (Z.mul_comm _ (abs b)).
destruct sa; cbn. {
  destruct b as [| sb vb]; [ easy | ].
  destruct sb; cbn. {
    rewrite Nat.sub_add; [ | easy ].
    apply Nat2Z_inj_mul.
  } {
    rewrite Nat.sub_add; [ | easy ].
    apply Nat2Z_inj_mul.
  }
}
destruct b as [| sb vb]; [ easy | cbn ].
rewrite Nat.sub_add; [ | easy ].
apply Nat2Z_inj_mul.
Qed.

(* min & max *)

Definition min a b := if Z.le_dec a b then a else b.
Definition max a b := if Z.le_dec a b then b else a.

Theorem min_l : ∀ a b, (a ≤ b)%Z → Z.min a b = a.
Proof.
intros * Hab.
progress unfold Z.min.
now destruct (Z.le_dec a b).
Qed.

Theorem min_r : ∀ a b, (b ≤ a)%Z → Z.min a b = b.
Proof.
intros * Hab.
progress unfold Z.min.
destruct (Z.le_dec a b); [ | easy ].
now apply Z.le_antisymm.
Qed.

Theorem max_l : ∀ a b, (b ≤ a)%Z → Z.max a b = a.
Proof.
intros * Hab.
progress unfold Z.max.
destruct (Z.le_dec a b); [ | easy ].
now apply Z.le_antisymm.
Qed.

Theorem max_r : ∀ a b, (a ≤ b)%Z → Z.max a b = b.
Proof.
intros * Hab.
progress unfold Z.max.
now destruct (Z.le_dec a b).
Qed.

(* gcd *)

Definition gcd a b :=
  match a with
  | z_zero => Z.abs b
  | z_val sa va =>
      match b with
      | z_zero => Z.abs a
      | z_val sb vb => z_val true (Pos.gcd va vb)
      end
  end.

Theorem gcd_comm : ∀ a b, Z.gcd a b = Z.gcd b a.
Proof.
intros.
destruct a as [| sa va]; [ now destruct b | ].
destruct b as [| sb vb]; [ easy | cbn ].
progress f_equal.
apply Pos.gcd_comm.
Qed.

Theorem gcd_divide_l : ∀ a b : Z, (Z.gcd a b | a)%Z.
Proof.
intros.
progress unfold Z.divide.
destruct a as [| sa va]; [ now exists 0%Z | cbn ].
destruct b as [| sb vb]. {
  destruct sa. {
    exists 1%Z; rewrite Z.mul_1_l.
    progress unfold Pos.to_nat, Z.of_nat, Pos.of_nat.
    rewrite Nat.add_1_r; f_equal.
    rewrite Nat_sub_succ_1.
    now destruct va.
  } {
    exists (-1)%Z.
    progress unfold Z.mul, Pos.to_nat, Z.of_nat, Pos.of_nat.
    rewrite Nat.add_1_r, Nat_sub_succ_1, Pos.mul_1_l.
    now destruct va.
  }
}
specialize (Nat.gcd_divide_l (Pos.to_nat va) (Pos.to_nat vb)) as H1.
destruct H1 as (v, Hv).
destruct va as (a).
destruct vb as (b).
cbn in Hv |-*.
exists (z_val sa (Pos.of_nat v)); cbn.
replace (Bool.eqb sa true) with sa by now destruct sa.
progress unfold Pos.gcd, Pos.of_nat, Pos.mul; cbn.
progress f_equal.
progress f_equal.
rewrite Nat.sub_add. 2: {
  destruct v; [ now rewrite Nat.add_1_r in Hv | ].
  now apply -> Nat.succ_le_mono.
}
rewrite Nat.sub_add. 2: {
  do 2 rewrite Nat.add_1_r.
  apply Nat.neq_0_lt_0.
  intros H.
  apply Nat.gcd_eq_0 in H.
  now destruct H.
}
rewrite <- Hv; symmetry.
apply Nat.add_sub.
Qed.

Theorem gcd_divide_r : ∀ a b : Z, (Z.gcd a b | b)%Z.
Proof.
intros.
rewrite Z.gcd_comm.
apply Z.gcd_divide_l.
Qed.

Theorem gcd_nonneg : ∀ a b, (0 ≤ Z.gcd a b)%Z.
Proof.
intros.
destruct a as [| sa va]; [ apply Z.abs_nonneg | ].
destruct b as [| sb vb]; [ apply Z.abs_nonneg | easy ].
Qed.

Theorem abs_gcd : ∀ a b, Z.abs (Z.gcd a b) = Z.gcd a b.
Proof.
intros.
progress unfold Z.abs.
specialize (Z.gcd_nonneg a b) as H1.
destruct (Z.gcd a b) as [| sg vg]; [ easy | ].
destruct sg; [ | easy ].
apply Z.of_nat_pos_to_nat.
Qed.

Theorem gcd_abs_l : ∀ a b, Z.gcd (Z.abs a) b = Z.gcd a b.
Proof.
intros.
destruct a as [| sa va]; [ easy | ].
cbn; rewrite Z.of_nat_pos_to_nat.
now cbn; rewrite Z.of_nat_pos_to_nat.
Qed.

Theorem gcd_0_l : ∀ a, Z.gcd 0 a = Z.abs a.
Proof. easy. Qed.

Theorem gcd_0_r : ∀ a, Z.gcd a 0 = Z.abs a.
Proof. now intros; rewrite Z.gcd_comm. Qed.

Theorem gcd_eq_0 : ∀ a b, Z.gcd a b = 0%Z ↔ a = 0%Z ∧ b = 0%Z.
Proof.
intros.
split; [ | now intros (Ha, Hb); subst ].
intros Hab.
specialize (Z.gcd_divide_l a b) as H1.
specialize (Z.gcd_divide_r a b) as H2.
rewrite Hab in H1, H2.
destruct H1 as (c, Hc).
destruct H2 as (d, Hd).
now rewrite Z.mul_0_r in Hc, Hd.
Qed.

Theorem gcd_eq_0_l : ∀ a b, Z.gcd a b = 0%Z → a = 0%Z.
Proof. now intros * Hab; apply Z.gcd_eq_0 in Hab. Qed.

Theorem gcd_eq_0_r : ∀ a b, Z.gcd a b = 0%Z → b = 0%Z.
Proof. now intros * Hab; apply Z.gcd_eq_0 in Hab. Qed.

Theorem gcd_assoc : ∀ a b c, Z.gcd a (Z.gcd b c) = Z.gcd (Z.gcd a b) c.
Proof.
intros.
destruct a as [| sa va]. {
  rewrite Z.gcd_abs_l; cbn.
  apply Z.abs_gcd.
}
cbn; rewrite Z.of_nat_pos_to_nat.
destruct b as [| sb vb]. {
  now destruct c; cbn; rewrite Z.of_nat_pos_to_nat.
}
cbn; rewrite Z.of_nat_pos_to_nat.
destruct c as [| sc vc]. {
  rewrite Nat.sub_add. 2: {
    apply Nat.neq_0_lt_0.
    intros H.
    apply Nat.gcd_eq_0_l in H.
    now apply Pos.to_nat_neq_0 in H.
  }
  progress unfold Z.of_nat.
  progress unfold Pos.gcd.
  remember (Nat.gcd _ _) as g eqn:Hg.
  symmetry in Hg.
  destruct g; [ cbn | easy ].
  apply Nat.gcd_eq_0_l in Hg.
  now apply Pos.to_nat_neq_0 in Hg.
}
progress f_equal.
apply Pos.gcd_assoc.
Qed.

(* *)

Theorem divide_div_mul_exact :
  ∀ a b c, b ≠ 0%Z → (b | a)%Z → (c * a / b)%Z = (c * (a / b))%Z.
Proof.
intros * Hbz Hba.
destruct Hba as (d, Hba).
subst a.
rewrite Z.mul_assoc.
rewrite Z.mul_div; [ | easy ].
now rewrite Z.mul_div.
Qed.

Theorem div_same: ∀ a, a ≠ 0%Z → (a / a)%Z = 1%Z.
Proof.
intros * Haz.
destruct a as [| sa va]; [ easy | cbn ].
rewrite Bool.eqb_reflx.
rewrite Nat.div_same; [ easy | ].
apply Pos.to_nat_neq_0.
Qed.

Theorem lt_0_mul :
  ∀ a b, (0 < a * b)%Z ↔ (0 < a)%Z ∧ (0 < b)%Z ∨ (b < 0)%Z ∧ (a < 0)%Z.
Proof.
intros.
split; intros Hab. {
  destruct (Z.lt_dec 0 a) as [Haz| Haz]. {
    left; split; [ easy | ].
    progress unfold Z.lt in Hab.
    progress unfold Z.lt.
    rewrite <- Hab.
    rewrite <- (Z.compare_mul_mono_pos_l a); [ | easy ].
    now rewrite Z.mul_0_r.
  }
  apply Z.nlt_ge in Haz.
  destruct (Z.lt_dec a 0) as [Hza| Hza]. {
    right; split; [ | easy ].
    progress unfold Z.lt in Hab.
    progress unfold Z.lt.
    rewrite <- Hab.
    rewrite <- (Z.compare_mul_mono_neg_l a); [ | easy ].
    now rewrite Z.mul_0_r.
  }
  apply Z.nlt_ge in Hza.
  apply Z.le_antisymm in Hza; [ | easy ].
  subst a.
  now apply Z.lt_irrefl in Hab.
}
destruct Hab as [(Hza, Hzb)| (Hbz, Haz)]. {
  now apply Z.mul_pos_pos.
} {
  now apply Z.mul_neg_neg.
}
Qed.

Theorem divide_pos_le : ∀ a b, (0 < b → (a | b) → a ≤ b)%Z.
Proof.
intros * Hzb Hab.
destruct Hab as (c, Hc); subst b.
apply Z.lt_0_mul in Hzb.
destruct Hzb as [(Hzc, Hza)| (Haz, Hcz)]. {
  rewrite <- (Z.mul_1_l a) at 1.
  apply Z.mul_le_mono_nonneg_r. {
    now apply Z.lt_le_incl.
  }
  destruct c as [| sc vc]; [ easy | ].
  destruct sc; [ | easy ].
  apply Pos.compare_le_iff.
  apply Pos.le_1_l.
} {
  rewrite <- (Z.mul_1_l a) at 1.
  apply Z.mul_le_mono_nonpos_r. {
    now apply Z.lt_le_incl.
  }
  destruct c as [| sc vc]; [ easy | ].
  now destruct sc.
}
Qed.

Theorem lt_eq_cases : ∀ a b, (a ≤ b ↔ a < b ∨ a = b)%Z.
Proof.
intros.
split; intros H. {
  destruct a as [| sa va]. {
    destruct b as [| sb vb]; [ now right | left ].
    now destruct sb.
  }
  destruct b as [| sb vb]. {
    destruct sa; [ easy | now left ].
  }
  destruct sa. {
    destruct sb; [ | easy ].
    progress unfold Z.le in H; cbn in H.
    progress unfold Z.lt; cbn.
    apply Pos.compare_le_iff in H.
    apply Pos.lt_eq_cases in H.
    destruct H; [ now left; apply Nat.compare_lt_iff | ].
    now right; subst.
  } {
    destruct sb; [ now left | ].
    progress unfold Z.le in H; cbn in H.
    progress unfold Z.lt; cbn.
    apply Pos.compare_le_iff in H.
    apply Pos.lt_eq_cases in H.
    destruct H; [ now left; apply Pos.compare_lt_iff | ].
    now right; subst.
  }
}
destruct H as [H| H]; [ | subst; apply Z.le_refl ].
now apply Z.lt_le_incl.
Qed.

End Z.

Number Notation Z Z.of_number Z.to_number : Z_scope.

Notation "a + b" := (Z.add a b) : Z_scope.
Notation "a - b" := (Z.sub a b) : Z_scope.
Notation "- a" := (Z.opp a) : Z_scope.
Notation "a * b" := (Z.mul a b) : Z_scope.
Notation "a / b" := (Z.div a b) : Z_scope.
Notation "a <= b" := (Z.le a b) : Z_scope.
Notation "a ≤ b" := (Z.le a b) : Z_scope.
Notation "a < b" := (Z.lt a b) : Z_scope.
Notation "a ?= b" := (Z.compare a b) : Z_scope.
Notation "a =? b" := (Z.eqb a b) : Z_scope.
Notation "a ≤ b ≤ c" := (Z.le a b ∧ Z.le b c) : Z_scope.
Notation "( x | y )" := (Z.divide x y) : Z_scope.

Module Nat2Z.

Open Scope Z_scope.

Theorem is_nonneg : ∀ a, (0 ≤ Z.of_nat a)%Z.
Proof. now intros; destruct a. Qed.

Theorem eq_0 : ∀ a, Z.of_nat a = 0%Z → a = 0%nat.
Proof. now intros; destruct a. Qed.

Theorem id : ∀ a, Z.to_nat (Z.of_nat a) = a.
Proof.
intros.
destruct a; [ easy | cbn ].
rewrite Nat.sub_0_r.
apply Nat.add_1_r.
Qed.

Theorem inj_succ : ∀ a, Z.of_nat (S a) = Z.of_nat a + 1.
Proof.
intros.
destruct a; [ easy | cbn ].
progress f_equal.
now apply Pos.of_nat_inj_succ.
Qed.

Theorem inj_add : ∀ a b, Z.of_nat (a + b) = Z.of_nat a + Z.of_nat b.
Proof.
intros.
destruct a; [ easy | ].
rewrite Nat.add_comm.
destruct b; [ easy | ].
rewrite Nat.add_comm.
cbn.
rewrite <- Nat.add_succ_l.
progress f_equal.
now apply Nat2Pos.inj_add.
Qed.

Theorem inj_le : ∀ a b, (a <= b)%nat ↔ (Z.of_nat a ≤ Z.of_nat b)%Z.
Proof.
intros.
destruct a; [ now destruct b | ].
destruct b; [ easy | cbn ].
split; intros H. {
  apply Pos.compare_le_iff.
  now apply -> Pos.of_nat_inj_le.
} {
  apply Pos.compare_le_iff in H.
  now apply Pos.of_nat_inj_le.
}
Qed.

Theorem inj_lt : ∀ a b, (a < b)%nat ↔ (Z.of_nat a < Z.of_nat b)%Z.
Proof.
intros.
destruct a; [ now destruct b | ].
destruct b; [ easy | cbn ].
split; intros H. {
  apply Pos.compare_lt_iff.
  now apply -> Pos.of_nat_inj_lt.
} {
  apply Pos.compare_lt_iff in H.
  now apply Pos.of_nat_inj_lt.
}
Qed.

End Nat2Z.

Module Z2Nat.

Theorem id : ∀ a : Z, (0 ≤ a)%Z → Z.of_nat (Z.to_nat a) = a.
Proof.
intros * Hz.
destruct a as [| sa va]; [ easy | ].
destruct sa; [ clear Hz; cbn | easy ].
apply Z.of_nat_pos_to_nat.
Qed.

Theorem of_nat : ∀ a, Z.of_nat (Z.to_nat a) = Z.max 0 a.
Proof.
intros.
progress unfold Z.max.
destruct (Z.le_dec 0 a) as [Hza| Hza]; [ now apply Z2Nat.id | ].
apply Z.nle_gt in Hza.
destruct a as [| sa va]; [ easy | now destruct sa ].
Qed.

Theorem inj_add :
  ∀ a b,
  (0 ≤ a)%Z
  → (0 ≤ b)%Z
  → Z.to_nat (a + b) = (Z.to_nat a + Z.to_nat b)%nat.
Proof.
intros * Hza Hzb.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | ].
destruct sa; [ | easy ].
destruct sb; [ | easy ].
cbn - [ Z.to_nat ].
simpl.
apply Pos2Nat.inj_add.
Qed.

Theorem inj_mul :
  ∀ a b,
  (0 ≤ a)%Z
  → (0 ≤ b)%Z
  → Z.to_nat (a * b) = (Z.to_nat a * Z.to_nat b)%nat.
Proof.
intros * Hza Hzb.
destruct a as [| sa va]; [ easy | ].
destruct b as [| sb vb]; [ easy | ].
destruct sa; [ | easy ].
destruct sb; [ | easy ].
cbn - [ Z.to_nat ].
apply Pos2Nat.inj_mul.
Qed.

End Z2Nat.

Module Pos2Z.

Theorem inj_mul : ∀ a b, Z.of_pos (a * b) = (Z.of_pos a * Z.of_pos b)%Z.
Proof. easy. Qed.

End Pos2Z.

Module Z2Pos.

Theorem id: ∀ a, (1 ≤ a)%Z → Z.of_pos (Z.to_pos a) = a.
Proof.
intros * Ha.
destruct a as [| sa va]; [ easy | now destruct sa ].
Qed.

Theorem to_nat : ∀ a,
  (0 < a)%Z
  → Pos.to_nat (Z.to_pos a) = Z.to_nat a.
Proof.
intros a Ha.
destruct a as [| sa va]; [ easy | cbn ].
now destruct sa.
Qed.

End Z2Pos.

Definition Z_ring_theory : ring_theory 0%Z 1%Z Z.add Z.mul Z.sub Z.opp eq :=
  {| Radd_0_l := Z.add_0_l;
     Radd_comm := Z.add_comm;
     Radd_assoc := Z.add_assoc;
     Rmul_1_l := Z.mul_1_l;
     Rmul_comm := Z.mul_comm;
     Rmul_assoc := Z.mul_assoc;
     Rdistr_l := Z.mul_add_distr_r;
     Rsub_def x y := eq_sym (eq_refl _);
     Ropp_def := Z.add_opp_diag_r |}.

From Stdlib Require Import Ring.
Add Ring Z_ring : Z_ring_theory.
