(* AlgCloCharPol.v *)

Require Import Utf8.

Require Import Misc.
Require Import Field.
Require Import Fpolynomial.
Require Import CharactPolyn.

Set Implicit Arguments.

Fixpoint degree_plus_1_of_list α (is_zero : α → bool) (l : list α) :=
  match l with
  | [] => O
  | [x … l₁] =>
      match degree_plus_1_of_list is_zero l₁ with
      | O => if is_zero x then O else 1%nat
      | S n => S (S n)
      end
  end.

Definition degree α is_zero (pol : polynomial α) :=
  pred (degree_plus_1_of_list is_zero (al pol)).

Definition apply_polynomial α (f : field α) :=
  apply_poly (fld_zero f) (fld_add f) (fld_mul f).

Fixpoint list_mod_div_mono A zero (add : A → A → A) mul (c : A) al :=
  match al with
  | [] => []
  | [a₁ … al₁] =>
      [apply_poly zero add mul (POL al)%pol c …
       list_mod_div_mono zero add mul c al₁]
  end.

Definition poly_div_mod_mono A zero (add : A → A → A) mul pol c :=
  match list_mod_div_mono zero add mul c (al pol) with
  | [] => (POL []%pol, zero)
  | [m … ml] => (POL ml%pol, m)
  end.

(* test
Require Import QArith.
Definition test cl c := poly_div_mod_mono 0 Qplus Qmult (POL cl)%pol c.
Eval vm_compute in test [Qnat 2; -Qnat 3; 1 … []] (Qnat 4).
Eval vm_compute in test [-Qnat 5; -Qnat 13; Qnat 0; Qnat 4 … []] (- 1 # 2).
*)

Record algeb_closed_field α :=
  { ac_field : field α;
    ac_root : polynomial α → (α * nat);
    ac_is_zero : α → bool;
    ac_prop : ∀ pol, degree ac_is_zero pol ≥ 1
      → (apply_polynomial ac_field pol (fst (ac_root pol)) .= ac_field
         .0 ac_field)%K }.

Fixpoint poly_power α (f : field α) pol n :=
  match n with
  | O => .1 f%pol
  | S m => (pol .* f poly_power f pol m)%pol
  end.

Notation "a .^ f b" := (poly_power f a b) : poly_scope.
Notation "a ./ f b" := (poly_div f a b) : poly_scope.

Fixpoint multiplicity_and_quotient pol ns c d :=
  match d with
  | O => (

Definition Ψ α (f : field α) pol ns c₁ r :=
  (Φq f pol ns ./ f POL [(.- f c₁)%K; .1 f … []] .^ f r)%pol.

Section theorems.

Variable α : Type.
Variable f : field α.

(* [Walker, p. 100] « If c₁ ≠ 0 is an r-fold root, r ≥ 1, of Φ(z^q) = 0,
   we have:
      Φ(z^q) = (z - c₁)^r Ψ(z), [...] » *)
Theorem phi_zq_eq_z_sub_c₁_psy : ∀ pol ns c₁ r,
  (Φq f pol ns .= f
   POL [(.- f c₁)%K; .1 f … []] .^ f r .* f Ψ f pol ns c₁ r)%pol.
Proof.
bbb.

End theorems.
