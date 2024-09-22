(* coqc version 8.20.0 compiled with OCaml 4.13.1
   coqtop version 8.20.0
   Expected coqc runtime on this file: 0.352 sec *)

Require Coq.QArith.QArith.

Set Implicit Arguments.

Class ring α := { rng_zero : α; }.

Class field α (rng_ring : ring α) := { fld_inv : α -> α }.

Import Coq.QArith.QArith.

Inductive lap_eq {α} {r : ring α} : list α -> list α -> Prop :=
  | lap_eq_cons : forall x₁ x₂ l₁ l₂, lap_eq (x₁ :: l₁) (x₂ :: l₂).

Theorem lap_eq_refl {α} {r : ring α} : reflexive _ lap_eq.
Admitted.

Theorem lap_eq_sym {α} {r : ring α} : symmetric _ lap_eq.
Admitted.

Theorem lap_eq_trans {α} {r : ring α} : transitive _ lap_eq.
Admitted.

Add Parametric Relation α (r : ring α) : (list α) lap_eq
 reflexivity proved by lap_eq_refl
 symmetry proved by lap_eq_sym
 transitivity proved by lap_eq_trans
 as lap_eq_rel.

Theorem lap_eq_0 : forall (α : Type) (r : ring α), lap_eq (cons rng_zero nil) nil.
Admitted.

Definition series_0 {α} {r : ring α} : nat -> α := fun i => rng_zero.

Record puiseux_series α := mkps { ps_terms : nat -> α }.

Definition ps_zero {α} {r : ring α} := {| ps_terms := series_0 |}.
Definition ps_ring α (R : ring α) (K : field R) : ring (puiseux_series α) := {| rng_zero := ps_zero; |}.

Canonical Structure ps_ring.

Theorem glop :
  forall (α : Type) (R : ring α) (K : field R),
  @lap_eq (puiseux_series α) (@ps_ring α R K)
     (@cons (puiseux_series α) (@ps_zero α R) (@nil (puiseux_series α)))
     nil.
Proof.
intros.
Check 1%nat.
rewrite lap_eq_0.
Check 1%nat.
