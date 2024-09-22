(* coqc version 8.20.0 compiled with OCaml 4.13.1
   coqtop version 8.20.0
   Expected coqc runtime on this file: 0.352 sec *)

Require Import Coq.Unicode.Utf8.
Require Import Coq.QArith.QArith.

Set Implicit Arguments.

Class ring α :=
  { rng_zero : α;
    rng_eq : α → α → Prop }.

Delimit Scope field_scope with K.
Notation "0" := rng_zero : field_scope.

Class field α (rng_ring : ring α) := { fld_inv : α → α }.

Notation "[ ]" := nil.
Notation "[ x ]" := (cons x nil).

Inductive lap_eq {α} {r : ring α} : list α → list α → Prop :=
  | lap_eq_cons : ∀ x₁ x₂ l₁ l₂, lap_eq (x₁ :: l₁) (x₂ :: l₂).

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

Theorem lap_eq_0 : ∀ (α : Type) (r : ring α), lap_eq [0%K] [ ].
Admitted.

Record power_series α := series { terms : nat → α }.

Definition series_0 {α} {r : ring α} := {| terms i := 0%K |}.

Record puiseux_series α := mkps { ps_terms : power_series α }.

Definition ps_zero {α} {r : ring α} := {| ps_terms := series_0 |}.

Inductive eq_ps {α} {r : ring α} {K : field r} :
  puiseux_series α → puiseux_series α → Prop :=
  | eq_ps_base : ∀ ps₁ ps₂, eq_ps ps₁ ps₂.

Notation "a = b" := (eq_ps a b) : ps_scope.
Notation "0" := ps_zero : ps_scope.

Definition ps_ring α (R : ring α) (K : field R) : ring (puiseux_series α) :=
  {| rng_zero := ps_zero;
     rng_eq := eq_ps |}.

Canonical Structure ps_ring.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Theorem glop :
  @lap_eq (puiseux_series α) (@ps_ring α R K)
     (@cons (puiseux_series α) (@ps_zero α R) (@nil (puiseux_series α)))
     [].
Proof.
intros.
Check 1%nat.
rewrite lap_eq_0.
Check 1%nat.
...
