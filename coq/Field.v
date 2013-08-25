(* $Id: Field.v,v 1.21 2013-08-25 10:24:30 deraugla Exp $ *)

Require Import Utf8.
Require Import Setoid.

Set Implicit Arguments.

Record field α :=
  { zero : α;
    one : α;
    add : α → α → α;
    mul : α → α → α;
    neg : α → α;
    fld_eq : α → α → Prop;
    fld_eq_refl : ∀ a, fld_eq a a;
    fld_eq_sym : ∀ a b, fld_eq a b → fld_eq b a;
    fld_eq_trans : ∀ a b c, fld_eq a b → fld_eq b c → fld_eq a c;
    fld_add_comm : ∀ a b, fld_eq (add a b) (add b a);
    fld_add_assoc : ∀ a b c, fld_eq (add (add a b) c) (add a (add b c));
    fld_add_ident : ∀ a, fld_eq (add zero a) a;
    fld_add_neg : ∀ a, fld_eq (add a (neg a)) zero;
    fld_add_subst_l : ∀ a b c, fld_eq a b → fld_eq (add a c) (add b c);
    fld_mul_comm : ∀ a b, fld_eq (mul a b) (mul b a);
    fld_mul_ident : ∀ a, fld_eq (mul one a) a;
    fld_mul_subst_l : ∀ a b c, fld_eq a b → fld_eq (mul a c) (mul b c) }.

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
rewrite fld_add_subst_l; [ idtac | eassumption ].
rewrite fld_add_comm; symmetry.
rewrite fld_add_comm; symmetry.
rewrite fld_add_subst_l; [ reflexivity | eassumption ].
Qed.

Add Parametric Morphism α (fld : field α) : (mul fld) with 
signature fld_eq fld ==> fld_eq fld ==> fld_eq fld
  as fld_mul_morph.
Proof.
intros a b Hab c d Hcd.
rewrite fld_mul_subst_l; [ idtac | eassumption ].
rewrite fld_mul_comm; symmetry.
rewrite fld_mul_comm; symmetry.
rewrite fld_mul_subst_l; [ reflexivity | eassumption ].
Qed.
