(** * A ℤ arithmetics *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Psatz.
Require Import RingLike.Core RingLike.Misc.
Import ListDef.

Inductive Z :=
  | z_zero : Z
  | z_pos : nat → Z
  | z_neg : nat → Z.

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

Theorem if_eqb_bool_dec : ∀ A i j (a b : A),
  (if Bool.eqb i j then a else b) = (if Bool.bool_dec i j then a else b).
Proof. now intros; destruct i, j. Qed.

Theorem Nat_compare_add_cancel_l :
  ∀ a b c, (a + b ?= a + c)%nat = (b ?= c)%nat.
Proof.
intros.
revert a b.
induction c; intros; cbn. {
  rewrite Nat.add_0_r.
  destruct b. {
    apply Nat.compare_eq_iff.
    apply Nat.add_0_r.
  }
  apply Nat.compare_gt_iff.
  flia.
}
destruct b. {
  rewrite Nat.add_0_r; cbn.
  apply Nat.compare_lt_iff.
  flia.
}
cbn.
do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
apply IHc.
Qed.

Theorem Nat_compare_add_cancel_r :
  ∀ a b c, (a + c ?= b + c)%nat = (a ?= b)%nat.
Proof.
intros.
do 2 rewrite (Nat.add_comm _ c).
apply Nat_compare_add_cancel_l.
Qed.

Theorem Nat_compare_sub_cancel_l :
  ∀ a b c,
  (b <= a)%nat
  → (c <= a)%nat
  → (a - b ?= a - c)%nat = (c ?= b)%nat.
Proof.
intros * Hle1 Hle2.
revert a b Hle1 Hle2.
induction c; intros; cbn. {
  rewrite Nat.sub_0_r.
  destruct b. {
    apply Nat.compare_eq_iff.
    apply Nat.sub_0_r.
  }
  apply Nat.compare_lt_iff.
  flia Hle1.
}
destruct b. {
  apply Nat.compare_gt_iff.
  rewrite Nat.sub_0_r.
  flia Hle2.
}
destruct a; [ easy | cbn ].
apply Nat.succ_le_mono in Hle1, Hle2.
apply (IHc _ _ Hle1 Hle2).
Qed.

Theorem Nat_compare_sub_cancel_r :
  ∀ a b c,
  (c <= a)%nat
  → (c <= b)%nat
  → (a - c ?= b - c)%nat = (a ?= b)%nat.
Proof.
intros * Hle1 Hle2.
revert b c Hle1 Hle2.
induction a; intros; cbn. {
  apply Nat.le_0_r in Hle1; subst c.
  now rewrite Nat.sub_0_r.
}
destruct b. {
  now apply Nat.le_0_r in Hle2; subst c.
}
destruct c; [ easy | cbn ].
apply Nat.succ_le_mono in Hle1, Hle2.
apply (IHa _ _ Hle1 Hle2).
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

Theorem Nat_1_le_mul_add_1 : ∀ a b, (1 <= (a + 1) * (b + 1))%nat.
Proof. flia. Qed.

Theorem Nat_add_1_r_pos : ∀ a, (0 < a + 1)%nat.
Proof. flia. Qed.

Hint Resolve Nat_1_le_mul_add_1 : core.
Hint Resolve Nat_add_1_r_pos : core.

(* end misc theorems *)

Module Z.

Definition of_number (n : Number.int) : option Z :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos (Decimal.D0 Decimal.Nil) => Some z_zero
      | Decimal.Pos n => Some (z_pos (Nat.of_uint n - 1))
      | Decimal.Neg n => Some (z_neg (Nat.of_uint n - 1))
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (a : Z) : Number.int :=
  match a with
  | z_zero => Number.IntDecimal (Decimal.Pos (Nat.to_uint 0))
  | z_pos v => Number.IntDecimal (Decimal.Pos (Nat.to_uint (v + 1)))
  | z_neg v => Number.IntDecimal (Decimal.Neg (Nat.to_uint (v + 1)))
  end.

Number Notation Z of_number to_number : Z_scope.

Definition of_nat n :=
  match n with
  | 0 => z_zero
  | S n' => z_pos n'
  end.

Definition add a b :=
  match a with
  | z_zero => b
  | z_pos va =>
      match b with
      | z_zero => a
      | z_pos vb => z_pos (va + vb + 1)
      | z_neg vb =>
          match va ?= vb with
          | Eq => z_zero
          | Lt => z_neg (vb - va - 1)
          | Gt => z_pos (va - vb - 1)
          end
      end
  | z_neg va =>
      match b with
      | z_zero => a
      | z_pos vb =>
          match va ?= vb with
          | Eq => z_zero
          | Lt => z_pos (vb - va - 1)
          | Gt => z_neg (va - vb - 1)
          end
      | z_neg vb => z_neg (va + vb + 1)
      end
  end.

Definition mul a b :=
  match a with
  | z_zero => z_zero
  | z_pos va =>
      match b with
      | z_zero => z_zero
      | z_pos vb => z_pos ((va + 1) * (vb + 1) - 1)
      | z_neg vb => z_neg ((va + 1) * (vb + 1) - 1)
      end
  | z_neg va =>
      match b with
      | z_zero => z_zero
      | z_pos vb => z_neg ((va + 1) * (vb + 1) - 1)
      | z_neg vb => z_pos ((va + 1) * (vb + 1) - 1)
      end
  end.

Definition opp a :=
  match a with
  | z_zero => z_zero
  | z_pos v => z_neg v
  | z_neg v => z_pos v
  end.

Definition sub a b := Z.add a (Z.opp b).

Definition z_pos_div_eucl a b :=
  let a' := (a + 1)%nat in
  let b' := (b + 1)%nat in
  (Z.of_nat (a' / b'), Z.of_nat (a' mod b')).

Definition div_eucl (a b : Z) :=
  match a with
  | z_zero => (z_zero, z_zero)
  | z_pos a' =>
      match b with
      | z_zero => (z_zero, a)
      | z_pos b' => z_pos_div_eucl a' b'
      | z_neg b' =>
          let (q', r') := z_pos_div_eucl a' b' in
          match r' with
          | z_zero => (Z.opp q', z_zero)
          | _ => (Z.opp (Z.add q' (z_pos 0)), Z.add b r')
          end
      end
  | z_neg a' =>
      match b with
      | z_zero => (z_zero, a)
      | z_pos b' =>
          let (q', r') := z_pos_div_eucl a' b' in
          match r' with
          | z_zero => (Z.opp q', z_zero)
          | _ => (Z.opp (Z.add q' (z_pos 0)), Z.add b (Z.opp r'))
          end
      | z_neg b' =>
          let (q', r') := z_pos_div_eucl a' b' in
          (q', Z.opp r')
      end
  end.

Definition div a b := fst (div_eucl a b).

Theorem eq_dec : ∀ a b : Z, {a = b} + {a ≠ b}.
Proof.
intros.
destruct a as [| a | a]. {
  now destruct b; [ left | right | right ].
} {
  destruct b as [| b| b]; [ now right | | now right ].
  destruct (Nat.eq_dec a b) as [Hvab| Hvab]; [ now subst; left | right ].
  intros H; apply Hvab.
  now injection H.
} {
  destruct b as [| b| b]; [ now right | now right | ].
  destruct (Nat.eq_dec a b) as [Hvab| Hvab]; [ now subst; left | right ].
  intros H; apply Hvab.
  now injection H.
}
Qed.

Definition compare a b :=
  match a with
  | z_zero =>
      match b with
      | z_zero => Eq
      | z_pos _ => Lt
      | z_neg _ => Gt
      end
  | z_pos va =>
      match b with
      | z_pos vb => va ?= vb
      | _ => Gt
      end
  | z_neg va =>
      match b with
      | z_neg vb => vb ?= va
      | _ => Lt
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
  | z_pos va =>
      match b with
      | z_pos vb => va =? vb
      | _ => false
      end
  | z_neg va =>
      match b with
      | z_neg vb => va =? vb
      | _ => false
      end
  end.

Notation "a + b" := (Z.add a b) : Z_scope.
Notation "a - b" := (Z.sub a b) : Z_scope.
Notation "a * b" := (Z.mul a b) : Z_scope.
Notation "a / b" := (Z.div a b) : Z_scope.
Notation "- a" := (Z.opp a) : Z_scope.
Notation "a ≤ b" := (Z.le a b) : Z_scope.
Notation "a < b" := (Z.lt a b) : Z_scope.
Notation "a ?= b" := (Z.compare a b) : Z_scope.
Notation "a =? b" := (Z.eqb a b) : Z_scope.
Notation "a ≤? b" := (Z.leb a b) : Z_scope.
Notation "a ≤ b ≤ c" := (Z.le a b ∧ Z.le b c) : Z_scope.

Instance ring_like_op : ring_like_op Z :=
  {| rngl_zero := z_zero;
     rngl_add := Z.add;
     rngl_mul := Z.mul;
     rngl_opt_one := Some (z_pos 0);
     rngl_opt_opp_or_subt := Some (inl Z.opp);
     rngl_opt_inv_or_quot := Some (inr Z.div);
     rngl_opt_is_zero_divisor := None;
     rngl_opt_eq_dec := Some Z.eq_dec;
     rngl_opt_leb := Some Z.leb |}.

Theorem opp_involutive : ∀ a, (- - a)%Z = a.
Proof. now intros; destruct a. Qed.

Theorem add_comm : ∀ a b, (a + b)%Z = (b + a)%Z.
Proof.
intros.
progress unfold add.
destruct a as [| a| a]; [ now destruct b | | ]. {
  destruct b as [| b| b]; [ easy | now rewrite (Nat.add_comm a) | ].
  rewrite (Nat.compare_antisym a).
  now destruct (a ?= b).
} {
  destruct b as [| b | b]; [ easy | | now rewrite (Nat.add_comm a) ].
  rewrite (Nat.compare_antisym a).
  now destruct (a ?= b).
}
Qed.

Theorem add_0_l : ∀ a, (0 + a)%Z = a.
Proof. now intros; destruct a. Qed.

Theorem add_0_r : ∀ a, (a + 0)%Z = a.
Proof. now intros; destruct a. Qed.

(* old implementation of Z that I should remove one day, but
   for the current implementation to work, it supposes to remake
   all the proofs... *)
Inductive Z' :=
  | z_zero' : Z'
  | z_val' : bool → nat → Z'.

Definition add' a b :=
  match a with
  | z_zero' => b
  | z_val' sa va =>
      match b with
      | z_zero' => a
      | z_val' sb vb =>
          if Bool.eqb sa sb then z_val' sa (va + vb + 1)
          else
            match va ?= vb with
            | Eq => z_zero'
            | Lt => z_val' sb (vb - va - 1)
            | Gt => z_val' sa (va - vb - 1)
            end
      end
  end.

Definition mul' a b :=
  match a with
  | z_zero' => z_zero'
  | z_val' sa va =>
      match b with
      | z_zero' => z_zero'
      | z_val' sb vb => z_val' (Bool.eqb sa sb) ((va + 1) * (vb + 1) - 1)
      end
  end.

Definition compare' a b :=
  match a with
  | z_zero' =>
      match b with
      | z_zero' => Eq
      | z_val' sb _ => if sb then Lt else Gt
      end
  | z_val' sa va =>
      match b with
      | z_zero' => if sa then Gt else Lt
      | z_val' sb vb =>
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

Definition le' a b := compare' a b ≠ Gt.

Theorem add_comm' : ∀ a b : Z', Z.add' a b = Z.add' b a.
Proof.
intros.
progress unfold Z.add'.
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

Theorem add_0_l' : ∀ a : Z', Z.add' z_zero' a = a.
Proof. now intros; destruct a. Qed.

Theorem add_0_r' : ∀ a : Z', Z.add' a z_zero' = a.
Proof. now intros; destruct a. Qed.

Theorem add_add_swap' :
  ∀ a b c : Z', Z.add' (Z.add' a b) c = Z.add' (Z.add' a c) b.
Proof.
intros.
destruct a as [| sa va]; [ do 2 rewrite Z.add_0_l'; apply Z.add_comm' | ].
destruct b as [| sb vb]; [ now do 2 rewrite Z.add_0_r' | ].
destruct c as [| sc vc]; [ now do 2 rewrite Z.add_0_r' | ].
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

Definition z'_of_z (a : Z) : Z' :=
  match a with
  | z_zero => z_zero'
  | z_pos a => z_val' true a
  | z_neg a => z_val' false a
  end.

Definition z_of_z' (a : Z') : Z :=
  match a with
  | z_zero' => z_zero
  | z_val' true a => z_pos a
  | z_val' false a => z_neg a
  end.

Theorem z'_of_z_inj : ∀ a b, z'_of_z a = z'_of_z b ↔ a = b.
Proof.
intros.
split; intros H; [ | now subst ].
apply (f_equal z_of_z') in H.
now destruct a, b.
Qed.

Theorem z'_of_z_add : ∀ a b, z'_of_z (a + b) = Z.add' (z'_of_z a) (z'_of_z b).
Proof.
intros.
progress unfold add'.
destruct a as [| a| a], b as [| b| b]; try easy; cbn.
now destruct (a ?= b).
now destruct (a ?= b).
Qed.

Theorem z'_of_z_mul : ∀ a b, z'_of_z (a * b) = Z.mul' (z'_of_z a) (z'_of_z b).
Proof. now intros; destruct a, b. Qed.

Theorem z'_of_z_le : ∀ a b, Z.le' (z'_of_z a) (z'_of_z b) ↔ (a ≤ b)%Z.
Proof. now intros; destruct a, b. Qed.

Theorem add_add_swap : ∀ a b c, (a + b + c)%Z = (a + c + b)%Z.
Proof.
intros.
apply z'_of_z_inj; cbn.
do 4 rewrite z'_of_z_add.
apply add_add_swap'.
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
progress unfold mul.
destruct a as [| a| a]; [ now destruct b | | ]. {
  destruct b; [ easy | | ].
  f_equal; f_equal; apply Nat.mul_comm.
  f_equal; f_equal; apply Nat.mul_comm.
} {
  destruct b; [ easy | | ].
  f_equal; f_equal; apply Nat.mul_comm.
  f_equal; f_equal; apply Nat.mul_comm.
}
Qed.

Theorem mul_0_l : ∀ a, (0 * a)%Z = 0%Z.
Proof. easy. Qed.

Theorem mul_0_r : ∀ a, (a * 0)%Z = 0%Z.
Proof. now intros; rewrite mul_comm. Qed.

Theorem pos_pos_swap :
  ∀ a b c,
  ((a + 1) * (b + 1) - 1 + 1) * (c + 1) - 1 =
  ((a + 1) * (c + 1) - 1 + 1) * (b + 1) - 1.
Proof.
intros.
rewrite Nat.sub_add; [ | easy ].
rewrite Nat.sub_add; [ | easy ].
f_equal; apply Nat.mul_shuffle0.
Qed.

Theorem mul_mul_swap : ∀ a b c, (a * b * c)%Z = (a * c * b)%Z.
Proof.
intros.
destruct a as [| a| a]; [ easy | | ]. {
  destruct b as [| b| b]; [ now do 2 rewrite Z.mul_0_r | | ]. {
    destruct c as [| c| c]; [ now do 2 rewrite Z.mul_0_r | | ].
    cbn; f_equal; apply pos_pos_swap.
    cbn; f_equal; apply pos_pos_swap.
  } {
    destruct c as [| c| c]; [ now do 2 rewrite Z.mul_0_r | | ].
    cbn; f_equal; apply pos_pos_swap.
    cbn; f_equal; apply pos_pos_swap.
  }
} {
  destruct b as [| b| b]; [ now do 2 rewrite Z.mul_0_r | | ]. {
    destruct c as [| c| c]; [ now do 2 rewrite Z.mul_0_r | | ].
    cbn; f_equal; apply pos_pos_swap.
    cbn; f_equal; apply pos_pos_swap.
  } {
    destruct c as [| c| c]; [ now do 2 rewrite Z.mul_0_r | | ].
    cbn; f_equal; apply pos_pos_swap.
    cbn; f_equal; apply pos_pos_swap.
  }
}
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
intros; cbn.
destruct a as [| a| a]; [ easy | | ].
now rewrite Nat.add_0_r, Nat.add_sub.
now rewrite Nat.add_0_r, Nat.add_sub.
Qed.

Theorem mul_1_r : ∀ a, (a * 1)%Z = a.
Proof. intros; rewrite Z.mul_comm; apply Z.mul_1_l. Qed.

Theorem mul_add_distr_l' :
  ∀ a b c, Z.mul' a (Z.add' b c) = Z.add' (Z.mul' a b) (Z.mul' a c).
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

Theorem mul_add_distr_l : ∀ a b c, (a * (b + c))%Z = (a * b + a * c)%Z.
Proof.
intros.
apply z'_of_z_inj; cbn.
rewrite z'_of_z_mul.
do 2 rewrite z'_of_z_add.
do 2 rewrite z'_of_z_mul.
apply mul_add_distr_l'.
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
destruct a as [| a| a]; [ easy | | ]; cbn.
now rewrite Nat.compare_refl.
now rewrite Nat.compare_refl.
Qed.

Theorem mul_div : ∀ a b, b ≠ 0%Z → (a * b / b)%Z = a.
Proof.
intros * Hbz.
progress unfold mul.
progress unfold div.
destruct a as [| a| a]; [ easy | | ]. {
  destruct b as [| b| b]; [ easy | | ]; cbn. {
    rewrite Nat.sub_add; [ | easy ].
    do 2 rewrite Nat.add_1_r.
    now rewrite Nat.div_mul.
  } {
    rewrite Nat.sub_add; [ | easy ].
    do 2 rewrite Nat.add_1_r.
    now rewrite Nat.div_mul.
  }
} {
  destruct b as [| b| b]; [ easy | | ]; cbn. {
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.Div0.mod_mul; cbn.
    do 2 rewrite Nat.add_1_r.
    now rewrite Nat.div_mul.
  } {
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.Div0.mod_mul; cbn.
    do 2 rewrite Nat.add_1_r.
    now rewrite Nat.div_mul.
  }
}
Qed.

Theorem integral :
  ∀ a b : Z,
  (a * b)%Z = 0%Z
  → a = 0%Z ∨ b = 0%Z ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab; cbn.
destruct a as [| a| a]; [ now left | | ].
destruct b as [| b| b]; [ now right; left | easy | easy ].
destruct b as [| b| b]; [ now right; left | easy | easy ].
Qed.

Theorem compare_antisymm : ∀ a b, CompOpp (a ?= b)%Z = (b ?= a)%Z.
Proof.
intros.
destruct a as [| a| a]; [ now destruct b | | ].
destruct b as [| b| b]; [ easy | | easy ].
symmetry; apply Nat.compare_antisym.
destruct b as [| b| b]; [ easy | easy | ].
symmetry; apply Nat.compare_antisym.
Qed.

Theorem nle_gt : ∀ a b, ¬ (a ≤ b)%Z ↔ (b < a)%Z.
Proof.
intros.
progress unfold le.
progress unfold lt.
rewrite <- Z.compare_antisymm.
progress unfold CompOpp.
split; [ | now destruct (b ?= a)%Z ].
destruct (b ?= a)%Z; [ | easy | ].
now intros H; exfalso; apply H.
now intros H; exfalso; apply H.
Qed.

Theorem nlt_ge : ∀ a b, ¬ (a < b)%Z ↔ (b ≤ a)%Z.
Proof.
intros.
progress unfold le.
progress unfold lt.
rewrite <- Z.compare_antisymm.
progress unfold CompOpp.
split; [ | now destruct (b ?= a)%Z ].
now destruct (b ?= a)%Z.
Qed.

Theorem lt_le_incl : ∀ a b, (a < b)%Z → (a ≤ b)%Z.
Proof. intros * Hab; congruence. Qed.

Theorem lt_irrefl : ∀ a, ¬ (a < a)%Z.
Proof.
intros a Ha.
destruct a as [| a| a]; [ easy | | ]. {
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
destruct a as [| a| a]; [ now destruct b | | ]; cbn. {
  destruct b as [| b| b]; [ easy | | easy ].
  split; intros H.
  now apply Nat.compare_eq_iff in H; subst.
  now injection H; intros; apply Nat.compare_eq_iff.
} {
  destruct b as [| b| b]; [ easy | easy | ].
  split; intros H.
  now apply Nat.compare_eq_iff in H; subst.
  now injection H; intros; apply Nat.compare_eq_iff.
}
Qed.

Theorem compare_lt_iff : ∀ a b, (a ?= b)%Z = Lt ↔ (a < b)%Z.
Proof. now intros; destruct a, b. Qed.

Theorem compare_gt_iff : ∀ a b, (a ?= b)%Z = Gt ↔ (b < a)%Z.
Proof.
intros.
destruct a as [| a| a]; [ now destruct b | | ]. {
  destruct b as [| b| b]; [ easy | cbn | easy ].
  split; intros H. {
    apply Nat.compare_gt_iff in H.
    now apply Nat.compare_lt_iff.
  } {
    apply Nat.compare_lt_iff in H.
    now apply Nat.compare_gt_iff.
  }
} {
  destruct b as [| b| b]; [ easy | easy | cbn ].
  split; intros H. {
    apply Nat.compare_gt_iff in H.
    now apply Nat.compare_lt_iff.
  } {
    apply Nat.compare_lt_iff in H.
    now apply Nat.compare_gt_iff.
  }
}
Qed.

Theorem compare_le_iff : ∀ a b, (a ?= b)%Z ≠ Gt ↔ (a ≤ b)%Z.
Proof.
intros.
split; intros H. {
  apply Z.nlt_ge; intros H1; apply H.
  now apply Z.compare_gt_iff.
} {
  intros H1; apply Z.compare_gt_iff in H1.
  now apply Z.nlt_ge in H.
}
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
destruct a as [| a| a]; [ easy | | ]; cbn.
now rewrite Nat.compare_refl.
now rewrite Nat.compare_refl.
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

Theorem le_trans : ∀ a b c, (a ≤ b → b ≤ c → a ≤ c)%Z.
Proof.
intros * Hab Hbc.
progress unfold Z.le in Hab, Hbc |-*.
progress unfold Z.compare in Hab, Hbc |-*.
destruct a as [| a| a]. {
  now destruct b, c.
} {
  destruct b as [| b| b]; [ easy | | easy ].
  destruct c as [| c| c]; [ easy | | easy ].
  apply Nat.compare_le_iff in Hab, Hbc.
  apply Nat.compare_le_iff.
  now transitivity b.
} {
  destruct c as [| c| c]; [ easy | easy | ].
  destruct b as [| b| b]; [ easy | easy | ].
  apply Nat.compare_le_iff in Hab, Hbc.
  apply Nat.compare_le_iff.
  now transitivity b.
}
Qed.

Theorem le_add_l : ∀ a b, (0 ≤ a)%Z → (b ≤ a + b)%Z.
Proof.
intros * Hza.
progress unfold Z.le in Hza |-*.
progress unfold Z.compare in Hza |-*.
destruct a as [| a| a]; [ | | easy ]. {
  destruct b as [| b| b]; [ easy | | ]; cbn.
  now rewrite Nat.compare_refl.
  now rewrite Nat.compare_refl.
}
destruct b as [| b| b]; [ easy | | ]; cbn. {
  apply Nat.compare_le_iff.
  rewrite Nat.add_shuffle0.
  apply Nat.le_add_l.
} {
  destruct (a ?= b); [ easy | | easy ].
  apply Nat.compare_le_iff.
  rewrite <- Nat.sub_add_distr.
  apply Nat.le_sub_l.
}
Qed.

Theorem le_add_r : ∀ a b, (0 ≤ a)%Z → (b ≤ b + a)%Z.
Proof.
intros * Hza.
rewrite Z.add_comm.
now apply Z.le_add_l.
Qed.

Theorem lt_add_l : ∀ a b, (0 < a)%Z → (b < a + b)%Z.
Proof.
intros * Hza.
apply Z.lt_iff.
split; [ now apply Z.le_add_l, Z.lt_le_incl | ].
intros H; symmetry in H.
apply Z.add_move_r in H.
rewrite Z.sub_diag in H; subst a.
revert Hza; apply Z.lt_irrefl.
Qed.

Theorem lt_add_r : ∀ a b, (0 < a)%Z → (b < b + a)%Z.
Proof.
intros * Hza.
rewrite Z.add_comm.
now apply Z.lt_add_l.
Qed.

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
eapply Z.le_trans; [ apply IHi | ].
now apply Z.le_add_l.
Qed.

Theorem leb_refl : ∀ a, (a ≤? a)%Z = true.
Proof.
intros.
progress unfold Z.leb.
destruct a as [| a| a]; [ easy | | ]; cbn.
now rewrite Nat.compare_refl.
now rewrite Nat.compare_refl.
Qed.

Theorem add_le_mono_l' : ∀ a b c, Z.le' a b → Z.le' (Z.add' c a) (Z.add' c b).
Proof.
intros * Hab.
progress unfold Z.le' in Hab |-*.
progress unfold Z.compare' in Hab |-*.
destruct a as [| sa va]. {
  destruct b as [| sb vb]. {
    destruct c as [| sc vc]; [ easy | cbn ].
    now destruct sc; rewrite Nat.compare_refl.
  }
  destruct sb; [ | easy ].
  destruct c as [| sc vc]; [ easy | ].
  destruct sc; cbn. {
    apply Nat.compare_le_iff.
    rewrite <- Nat.add_assoc.
    apply Nat.le_add_r.
  }
  destruct (vc ?= vb); [ easy | easy | ].
  apply Nat.compare_le_iff.
  rewrite <- Nat.sub_add_distr.
  apply Nat.le_sub_l.
}
destruct b as [| sb vb]. {
  destruct sa; [ easy | ].
  destruct c as [| sc vc]; [ easy | cbn ].
  destruct sc; cbn. {
    destruct (vc ?= va); [ easy | easy | cbn ].
    apply Nat.compare_le_iff.
    rewrite <- Nat.sub_add_distr.
    apply Nat.le_sub_l.
  }
  apply Nat.compare_le_iff.
  rewrite <- Nat.add_assoc.
  apply Nat.le_add_r.
}
destruct c as [| sc vc]; [ easy | ].
destruct sa. {
  destruct sb; [ cbn | easy ].
  destruct sc; cbn. {
    apply Nat.compare_le_iff in Hab.
    apply Nat.compare_le_iff.
    now apply Nat.add_le_mono_r, Nat.add_le_mono_l.
  }
  remember (vc ?= va) as ca eqn:Hca.
  remember (vc ?= vb) as cb eqn:Hcb.
  symmetry in Hca, Hcb.
  destruct ca; cbn. {
    apply Nat.compare_eq_iff in Hca; subst vc.
    now destruct cb.
  } {
    destruct cb. {
      apply Nat.compare_eq_iff in Hcb; subst vc.
      apply Nat.compare_ngt_iff in Hab.
      now apply Nat.compare_lt_iff in Hca.
    } {
      apply Nat.compare_le_iff in Hab.
      apply Nat.compare_le_iff.
      now do 2 apply Nat.sub_le_mono_r.
    } {
      exfalso.
      apply Nat.compare_ngt_iff in Hab; apply Hab.
      apply Nat.compare_lt_iff in Hca.
      apply Nat.compare_gt_iff in Hcb.
      now apply (Nat.lt_trans _ vc).
    }
  } {
    destruct cb; [ easy | easy | cbn ].
    apply Nat.compare_le_iff in Hab.
    apply Nat.compare_le_iff.
    apply Nat.sub_le_mono_r.
    now apply Nat.sub_le_mono_l.
  }
}
destruct sb. {
  destruct sc; cbn. {
    destruct (vc ?= va); [ easy | easy | cbn ].
    apply Nat.compare_le_iff.
    rewrite <- Nat.sub_add_distr, <- Nat.add_assoc.
    apply (Nat.le_trans _ vc); [ apply Nat.le_sub_l | ].
    apply Nat.le_add_r.
  }
  destruct (vc ?= vb); [ easy | easy | cbn ].
  apply Nat.compare_le_iff.
  rewrite <- Nat.sub_add_distr, <- Nat.add_assoc.
  apply (Nat.le_trans _ vc); [ apply Nat.le_sub_l | ].
  apply Nat.le_add_r.
}
destruct sc; cbn. {
  remember (vc ?= va) as ca eqn:Hca.
  remember (vc ?= vb) as cb eqn:Hcb.
  symmetry in Hca, Hcb.
  destruct ca. {
    apply Nat.compare_eq_iff in Hca; subst vc.
    destruct cb; [ easy | | easy ].
    apply Nat.compare_ngt_iff in Hab.
    now apply Nat.compare_lt_iff in Hcb.
  } {
    destruct cb; [ easy | cbn | easy ].
    apply Nat.compare_le_iff in Hab.
    apply Nat.compare_le_iff.
    do 2 rewrite <- Nat.sub_add_distr.
    now apply Nat.sub_le_mono_r.
  } {
    destruct cb; [ exfalso | exfalso | ]. {
      now apply Nat.compare_eq_iff in Hcb; subst vc.
    } {
      apply Nat.compare_ngt_iff in Hab.
      apply Nat.compare_gt_iff in Hca.
      apply Nat.compare_lt_iff in Hcb.
      apply Hab.
      now apply (Nat.lt_trans _ vc).
    } {
      apply Nat.compare_le_iff in Hab.
      apply Nat.compare_le_iff.
      do 2 rewrite <- Nat.sub_add_distr.
      now apply Nat.sub_le_mono_l, Nat.add_le_mono_r.
    }
  }
}
apply Nat.compare_le_iff in Hab.
apply Nat.compare_le_iff.
now apply Nat.add_le_mono_r, Nat.add_le_mono_l.
Qed.

Theorem add_le_mono_l : ∀ a b c, (a ≤ b)%Z → (c + a ≤ c + b)%Z.
Proof.
intros * Hab.
apply z'_of_z_le.
do 2 rewrite z'_of_z_add.
apply add_le_mono_l'.
now apply z'_of_z_le.
Qed.

Theorem add_lt_mono_l : ∀ a b c, (a < b)%Z → (c + a < c + b)%Z.
Proof.
intros * Hab.
apply Z.lt_iff.
split; [ now apply Z.add_le_mono_l, Z.lt_le_incl | ].
intros H.
(* lemma *)
apply (f_equal (λ x, Z.sub x c)) in H.
do 2 rewrite (Z.add_comm c) in H.
do 2 rewrite Z.add_sub in H.
subst b.
revert Hab.
apply Z.lt_irrefl.
Qed.

Theorem mul_le_mono_nonneg_l :
  ∀ a b c, (0 ≤ a)%Z → (b ≤ c)%Z → (a * b ≤ a * c)%Z.
Proof.
intros * Hza Hbc.
progress unfold Z.le in Hza, Hbc |-*.
destruct a as [| a| a]; [ easy | clear Hza; cbn | easy ].
destruct b as [| b| b]; [ now destruct c | | ]. {
  destruct c as [| c| c]; [ easy | cbn | easy ].
  apply Nat.compare_le_iff in Hbc.
  rewrite Nat_compare_sub_add_r; [ | easy ].
  rewrite Nat.sub_add; [ | easy ].
  rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
  apply Nat.compare_le_iff.
  now apply Nat.add_le_mono_r.
} {
  destruct c as [| c| c]; [ easy | easy | cbn ].
  apply Nat.compare_le_iff in Hbc.
  rewrite Nat_compare_sub_add_r; [ | easy ].
  rewrite Nat.sub_add; [ | easy ].
  rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
  apply Nat.compare_le_iff.
  now apply Nat.add_le_mono_r.
}
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
progress unfold Z.le in Hza, Hbc |-*.
destruct a as [| a| a]; [ easy | easy | clear Hza; cbn ].
destruct b as [| b| b]; [ now destruct c | | ]. {
  destruct c as [| c| c]; [ easy | cbn | easy ].
  apply Nat.compare_le_iff in Hbc.
  rewrite Nat_compare_sub_add_r; [ | easy ].
  rewrite Nat.sub_add; [ | easy ].
  rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
  apply Nat.compare_le_iff.
  now apply Nat.add_le_mono_r.
} {
  destruct c as [| c| c]; [ easy | easy | cbn ].
  apply Nat.compare_le_iff in Hbc.
  rewrite Nat_compare_sub_add_r; [ | easy ].
  rewrite Nat.sub_add; [ | easy ].
  rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
  apply Nat.compare_le_iff.
  now apply Nat.add_le_mono_r.
}
Qed.

Theorem add_le_compat : ∀ a b c d, (a ≤ b)%Z → (c ≤ d)%Z → (a + c ≤ b + d)%Z.
Proof.
intros * Hab Hcd.
apply (Z.le_trans _ (a + d)); [ apply Z.add_le_mono_l, Hcd | ].
do 2 rewrite (Z.add_comm _ d).
now apply Z.add_le_mono_l.
Qed.

Theorem mul_opp_l : ∀ a b, (- a * b)%Z = (- (a * b))%Z.
Proof. now intros; destruct a, b. Qed.

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
apply (Z.le_trans _ (a * d)). {
  now apply Z.mul_le_mono_nonneg_l.
}
do 2 rewrite (Z.mul_comm _ d).
apply Z.mul_le_mono_nonneg_l; [ | easy ].
now apply (Z.le_trans _ b).
Qed.

Theorem mul_le_compat_nonpos :
  ∀ a b c d : Z, (c ≤ a ≤ 0)%Z → (d ≤ b ≤ 0)%Z → (a * b ≤ c * d)%Z.
Proof.
intros * Hca Hdb.
apply (Z.le_trans _ (a * d)). {
  now apply Z.mul_le_mono_nonpos_l.
}
do 2 rewrite (Z.mul_comm _ d).
apply Z.mul_le_mono_nonpos_l; [ | easy ].
now apply (Z.le_trans _ b).
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
destruct a as [| a| a]; [ easy | | ].
now rewrite Nat.compare_refl in H1.
now rewrite Nat.compare_refl in H1.
Qed.

Instance ring_like_ord : ring_like_ord Z :=
  {| rngl_ord_le_dec := (λ a b, Bool.bool_dec (a ≤? b)%Z true);
     rngl_ord_le_refl := Z.leb_refl;
     rngl_ord_le_antisymm := Z.leb_antisymm;
     rngl_ord_le_trans := Z.leb_trans;
     rngl_ord_add_le_compat := Z.add_leb_compat;
     rngl_ord_mul_le_compat_nonneg := Z.mul_leb_compat_nonneg;
     rngl_ord_mul_le_compat_nonpos := Z.mul_leb_compat_nonpos;
     rngl_ord_not_le := Z.not_leb |}.

(* borrowed from RingLike.Z_algebra *)
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
apply Nat.add_1_r.
Qed.

Theorem nat_archimedean : ∀ a b, (0 < a → ∃ n, b < n * a)%nat.
Proof.
intros * Ha.
exists (S b); simpl.
induction b; [ now rewrite Nat.add_0_r | ].
simpl; rewrite <- Nat.add_1_l.
now apply Nat.add_le_lt_mono.
Qed.

Theorem archimedean : ∀ a b, (0 < a → ∃ n, b < Z.of_nat n * a)%Z.
Proof.
intros * Ha.
destruct a as [| a| a]; [ easy | clear Ha | easy ].
progress unfold Z.lt; cbn.
destruct b as [| b| b]; [ now exists 1; rewrite Z.mul_1_l | | ]. {
  specialize (nat_archimedean (a + 1) (b + 1)) as (m, Hm); [ easy | ].
  exists m.
  destruct m; [ easy | cbn ].
  apply Nat.compare_lt_iff.
  apply Nat.lt_add_lt_sub_r.
  now rewrite (Nat.add_1_r m).
} {
  specialize (nat_archimedean (a + 1) (b + 1)) as (m, Hm); [ easy | ].
  now exists m; destruct m.
}
Qed.

Theorem archimedean_b :
(*
  ∀ a b, (0 < a)%L → ∃ n : nat, (rngl_mul_nat a n ≤? b)%Z = false.
*)
  ∀ a b, (a ≤? 0)%Z = false → ∃ n : nat, (rngl_mul_nat a n ≤? b)%Z = false.
Proof.
intros * Haz.
assert (Ha : (0 < a)%Z). {
  apply Bool.not_true_iff_false in Haz.
  apply Z.not_leb in Haz.
  destruct Haz as (Haz, Hza).
  apply Z.leb_le in Hza.
  destruct a as [| a| a]; [ easy | | ]; now apply Z.lt_iff.
}
apply (Z.archimedean a b) in Ha.
destruct Ha as (n, Ha).
rewrite <- rngl_mul_nat_Z in Ha.
exists n.
progress unfold Z.lt in Ha.
progress unfold Z.compare in Ha.
destruct b as [| b| b]; [ now destruct (rngl_mul_nat a n) | | ]. {
  destruct (rngl_mul_nat a n) as [| c| c]; [ easy | | easy ].
  rewrite Nat.compare_antisym in Ha.
  progress unfold CompOpp in Ha.
  progress unfold Z.leb; cbn.
  now destruct (c ?= b).
} {
  destruct (rngl_mul_nat a n) as [| c| c]; [ easy | easy | ].
  rewrite Nat.compare_antisym in Ha.
  progress unfold CompOpp in Ha.
  progress unfold Z.leb; cbn.
  now destruct (b ?= c).
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

Theorem opp_add_distr : ∀ a b, (- (a + b))%Z = (- a - b)%Z.
Proof.
intros.
specialize (rngl_opp_add_distr eq_refl a b) as H1.
now rewrite rngl_opp_sub_swap in H1.
Qed.

Theorem eqb_refl : ∀ a, (a =? a)%Z = true.
Proof.
intros.
destruct a as [| a| a]; [ easy | | ]; apply Nat.eqb_refl.
Qed.

Theorem eqb_eq : ∀ a b, (a =? b)%Z = true ↔ a = b.
Proof.
intros.
split; intros Hab; [ | subst b; apply eqb_refl ].
destruct a as [| a| a]; [ now destruct b | | ]. {
  destruct b as [| b| b]; [ easy | | easy ].
  now apply Nat.eqb_eq in Hab; subst.
} {
  destruct b as [| b| b]; [ easy | easy | ].
  now apply Nat.eqb_eq in Hab; subst.
}
Qed.

Theorem mul_le_mono_pos_l :
  ∀ a b c, (0 < a)%Z → (b ≤ c)%Z ↔ (a * b ≤ a * c)%Z.
Proof.
intros * Hza.
destruct a as [| a| a]; [ now apply lt_irrefl in Hza | cbn | cbn ]. {
  destruct b as [| b| b]; [ now destruct c | | ]. {
    destruct c as [| c| c]; [ easy | | easy ].
    progress unfold Z.le; cbn.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
    now rewrite Nat_compare_add_cancel_r.
  } {
    destruct c as [| c| c]; [ easy | easy | ].
    progress unfold Z.le; cbn.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
    now rewrite Nat_compare_add_cancel_r.
  }
} {
  destruct b as [| b| b]; [ now destruct c | | ]. {
    destruct c as [| c| c]; [ easy | | easy ].
    progress unfold Z.le; cbn.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
    now rewrite Nat_compare_add_cancel_r.
  } {
    destruct c as [| c| c]; [ easy | easy | ].
    progress unfold Z.le; cbn.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
    now rewrite Nat_compare_add_cancel_r.
  }
}
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
destruct a as [| a| a]; [ now apply lt_irrefl in Hza | cbn | cbn ]. {
  destruct b as [| b| b]; [ now destruct c | | ]. {
    destruct c as [| c| c]; [ easy | | easy ].
    progress unfold Z.lt; cbn.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
    now rewrite Nat_compare_add_cancel_r.
  } {
    destruct c as [| c| c]; [ easy | easy | ].
    progress unfold Z.lt; cbn.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
    now rewrite Nat_compare_add_cancel_r.
  }
} {
  destruct b as [| b| b]; [ now destruct c | | ]. {
    destruct c as [| c| c]; [ easy | | easy ].
    progress unfold Z.lt; cbn.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
    now rewrite Nat_compare_add_cancel_r.
  } {
    destruct c as [| c| c]; [ easy | easy | ].
    progress unfold Z.lt; cbn.
    rewrite Nat_compare_sub_cancel_r; [ | easy | easy ].
    rewrite Nat_compare_mul_cancel_l; [ | now rewrite Nat.add_1_r ].
    now rewrite Nat_compare_add_cancel_r.
  }
}
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
progress unfold Z.le.
destruct a as [| a| a]; [ easy | | ]; cbn.
now apply Nat.compare_le_iff.
now apply Nat.compare_le_iff.
Qed.

Theorem mul_nonneg_nonneg : ∀ a b, (0 ≤ a → 0 ≤ b → 0 ≤ a * b)%Z.
Proof.
intros * Hz1 Hz2.
destruct a as [| a| a]; [ apply Z.le_refl | | easy ].
destruct b as [| b| b]; [ apply Z.le_refl | | easy ].
easy.
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

Module Nat2Z.

Open Scope Z_scope.

Theorem is_nonneg : ∀ a, (0 ≤ Z.of_nat a)%Z.
Proof. now intros; destruct a. Qed.

Theorem eq_0 : ∀ a, Z.of_nat a = 0%Z → a = 0%nat.
Proof. now intros; destruct a. Qed.

Theorem inj_succ : ∀ a, Z.of_nat (S a) = Z.of_nat a + 1.
Proof.
intros.
destruct a; [ easy | cbn ].
now rewrite Nat.add_0_r, Nat.add_comm.
Qed.

Theorem inj_mul : ∀ a b, Z.of_nat (a * b) = Z.of_nat a * Z.of_nat b.
Proof.
intros.
progress unfold Z.mul.
progress unfold Z.of_nat.
destruct a; [ easy | ].
rewrite Nat.mul_comm.
destruct b; [ easy | cbn ].
f_equal; flia.
Qed.

Theorem inj_lt : ∀ a b, (a < b)%nat ↔ (Z.of_nat a < Z.of_nat b)%Z.
Proof.
intros.
destruct a; [ now destruct b | ].
destruct b; [ easy | cbn ].
progress unfold Z.lt; cbn.
split; intros H. {
  apply Nat.compare_lt_iff.
  now apply Nat.succ_lt_mono in H.
} {
  apply Nat.compare_lt_iff in H.
  now apply -> Nat.succ_lt_mono.
}
Qed.

End Nat2Z.

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
