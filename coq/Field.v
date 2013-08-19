(* $Id: Field.v,v 1.17 2013-08-19 13:53:43 deraugla Exp $ *)

Require Import Utf8.
Require Import Setoid.

Set Implicit Arguments.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    mul : α → α → α;
    fld_eq : α → α → Prop;
    fld_eq_refl : ∀ a, fld_eq a a;
    fld_eq_sym : ∀ a b, fld_eq a b → fld_eq b a;
    fld_eq_trans : ∀ a b c, fld_eq a b → fld_eq b c → fld_eq a c;
    fld_add_comm : ∀ a b, fld_eq (add a b) (add b a);
    fld_add_assoc : ∀ a b c, fld_eq (add (add a b) c) (add a (add b c));
    fld_add_neutral : ∀ a, fld_eq (add zero a) a;
    fld_add_compat : ∀ a b c d, fld_eq a b → fld_eq c d
      → fld_eq (add a c) (add b d);
    fld_mul_neutral : ∀ a, fld_eq (mul one a) a;
    fld_mul_compat : ∀ a b c d, fld_eq a b → fld_eq c d
      → fld_eq (mul a c) (mul b d) }.

Add Parametric Relation α (fld : field α) : α (fld_eq fld)
 reflexivity proved by (fld_eq_refl fld)
 symmetry proved by (fld_eq_sym fld)
 transitivity proved by (fld_eq_trans fld)
 as fld_eq_rel.

Add Parametric Morphism α (fld : field α) : (add fld) with 
signature fld_eq fld ==> fld_eq fld ==> fld_eq fld
  as fld_add_morph.
Proof.
intros a b Hab c d Hcd.
apply fld_add_compat; assumption.
Qed.

Add Parametric Morphism α (fld : field α) : (mul fld) with 
signature fld_eq fld ==> fld_eq fld ==> fld_eq fld
  as fld_mul_morph.
Proof.
intros a b Hab c d Hcd.
apply fld_mul_compat; assumption.
Qed.
