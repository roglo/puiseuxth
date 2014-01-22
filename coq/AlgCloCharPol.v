(* AlgCloCharPol.v *)

Require Import Utf8.
Require Import NPeano.

Require Import Misc.
Require Import Field.
Require Import Newton.
Require Import Fpolynomial.
Require Import Puiseux_base.
Require Import CharactPolyn.

Set Implicit Arguments.

(* euclidean division of a polynomial by (x - c) *)

Fixpoint list_mod_div_mono A zero (add : A → A → A) mul (c : A) al :=
  match al with
  | [] => []
  | [a₁ … al₁] =>
      [apply_poly zero add mul (POL al)%pol c …
       list_mod_div_mono zero add mul c al₁]
  end.

Definition poly_div_mono A zero (add : A → A → A) mul pol c :=
  match list_mod_div_mono zero add mul c (al pol) with
  | [] => POL []%pol
  | [m … ml] => POL ml%pol
  end.

Definition poly_mod_mono A zero (add : A → A → A) mul pol c :=
  match list_mod_div_mono zero add mul c (al pol) with
  | [] => zero
  | [m … ml] => m
  end.

(* test
Require Import QArith.
Definition Ztest_div cl c := poly_div_mono Z0 Z.add Z.mul (POL cl)%pol c.
Definition Ztest_mod cl c := poly_mod_mono Z0 Z.add Z.mul (POL cl)%pol c.
Definition Qtest_div cl c := poly_div_mono 0 Qplus Qmult (POL cl)%pol c.
Definition Qtest_mod cl c := poly_mod_mono 0 Qplus Qmult (POL cl)%pol c.
Eval vm_compute in Ztest_div [2; -3; 1 … []]%Z 4.
Eval vm_compute in Ztest_mod [2; -3; 1 … []]%Z 4.
Eval vm_compute in Qtest_div [-Qnat 5; -Qnat 13; Qnat 0; Qnat 4 … []] (- 1 # 2).
Eval vm_compute in Qtest_mod [-Qnat 5; -Qnat 13; Qnat 0; Qnat 4 … []] (- 1 # 2).
*)

(* trying to compute i-th derivative divided by factorial i *)

Fixpoint comb n k :=
  match n with
  | O => O
  | 1 => 1
  | S n₁ =>
      match n - k with
      | O => 1
      | _ =>
          match k with
          | O => 1
          | S k₁ => comb n₁ k₁ + comb n₁ k
          end
      end
  end.

Fixpoint glop A (mul : nat → A → A) al i j :=
  match al with
  | [] => []
  | [a₁ … al₁] => [mul (comb i j) a₁ … glop mul al₁ i (S j)]
  end.

Definition ith_der_on_fact_i A (mul : nat → A → A) pol i :=
  glop mul (List.skipn i (al pol)) i i.

(* *)

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

Record algeb_closed_field α :=
  { ac_field : field α;
    ac_is_zero : α → bool;
    ac_root : polynomial α → α;
    ac_prop : ∀ pol, degree ac_is_zero pol ≥ 1
      → (apply_polynomial ac_field pol (ac_root pol) .= ac_field
         .0 ac_field)%K }.

Fixpoint poly_power α (f : field α) pol n :=
  match n with
  | O => .1 f%pol
  | S m => (pol .* f poly_power f pol m)%pol
  end.

Notation "a .^ f b" := (poly_power f a b) : poly_scope.

(*
Definition Ψ α (f : field α) pol ns c₁ r :=
  (Φq f pol ns ./ f POL [(.- f c₁)%K; .1 f … []] .^ f r)%pol.
*)

Fixpoint list_multiplicity α (acf : algeb_closed_field α) c₁ al d :=
  let f := ac_field acf in
  match d with
  | O => O
  | S d₁ =>
      match list_mod_div_mono (.0 f)%K (fld_add f) (fld_mul f) c₁ al with
      | [] => O
      | [m … ml] =>
          if ac_is_zero acf m then S (list_multiplicity acf c₁ ml d₁)
          else O
      end
  end.

Definition multiplicity α (acf : algeb_closed_field α) c₁ pol :=
  list_multiplicity acf c₁ (al pol) (List.length (al pol)).

Fixpoint quotient_phi_x_sub_c_pow_r α (f : field α) pol c₁ r :=
  match r with
  | O => pol
  | S r₁ =>
      quotient_phi_x_sub_c_pow_r f
        (poly_div_mono (.0 f)%K (fld_add f) (fld_mul f) pol c₁) c₁ r₁
  end.

Section theorems.

Variable α : Type.
Variable acf : algeb_closed_field α.
Let f := ac_field acf.

(* [Walker, p. 100] « If c₁ ≠ 0 is an r-fold root, r ≥ 1, of Φ(z^q) = 0,
   we have:
      Φ(z^q) = (z - c₁)^r Ψ(z), [...] » *)
Theorem phi_zq_eq_z_sub_c₁_psy : ∀ pol ns c₁ r Ψ,
  ns ∈ newton_segments f pol
  → c₁ = ac_root acf (Φq f pol ns)
    → r = multiplicity acf c₁ (Φq f pol ns)
      → Ψ = quotient_phi_x_sub_c_pow_r f (Φq f pol ns) c₁ r
        → (Φq f pol ns .= f POL [(.- f c₁)%K; .1 f%K … []] .^ f r .* f Ψ)%pol.
Proof.
intros pol ns c₁ r Ψ Hns Hc₁ Hr HΨ.
destruct r.
 simpl.
bbb.

intros pol ns c₁ r Ψ Hns Hc₁ Hr HΨ.
subst r Ψ; simpl.
unfold multiplicity; simpl.
rewrite Nat.sub_diag; simpl.
bbb.

End theorems.
