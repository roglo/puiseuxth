(* coqc version 8.20.0 compiled with OCaml 4.13.1
   coqtop version 8.20.0
   Expected coqc runtime on this file: 0.352 sec *)

Require Coq.QArith.QArith.
Require Coq.Unicode.Utf8.

Import Coq.Unicode.Utf8.

Set Implicit Arguments.

Class ring α :=
  { rng_zero : α;
    rng_one : α;
    rng_add : α → α → α;
    rng_mul : α → α → α;
    rng_eq : α → α → Prop }.

Delimit Scope field_scope with K.
Notation "a = b" := (rng_eq a b) : field_scope.
Notation "a + b" := (rng_add a b) : field_scope.
Notation "a * b" := (rng_mul a b) : field_scope.
Notation "0" := rng_zero : field_scope.
Notation "1" := rng_one : field_scope.

Class field α (rng_ring : ring α) := { fld_inv : α → α }.

Import Coq.QArith.QArith.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Definition Qnat i := Z.of_nat i # 1.

Fixpoint summation_aux α (r : ring α) b len g :=
  match len with
  | O => 0%K
  | S len₁ => (g b + summation_aux r (S b) len₁ g)%K
  end.

Definition summation α {R : ring α} b e g := summation_aux R b (S e - b) g.

Notation "'Σ' ( i = b , e ) , g" := (summation b e (λ i, (g)))
  (at level 0, i at level 0, b at level 60, e at level 60, g at level 40).

Inductive lap_eq {α} {r : ring α} : list α → list α → Prop :=
  | lap_eq_nil : lap_eq [] []
  | lap_eq_cons : ∀ x₁ x₂ l₁ l₂,
      (x₁ = x₂)%K
      → lap_eq l₁ l₂
        → lap_eq [x₁ … l₁] [x₂ … l₂].

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

Definition lap_mul {α} {R : ring α} (la lb : list α) : list α := [].

Global Instance lap_mul_morph α (R : ring α) :
  Proper (lap_eq ==> lap_eq ==> lap_eq) (@lap_mul _ R).
Admitted.

Section lap.

Variable α : Type.
Variable r : ring α.

Theorem lap_eq_0 : lap_eq [0%K] [].
Admitted.

End lap.

Inductive Nbar : Set :=
  | fin : ∀ x : nat, Nbar
  | inf : Nbar.

Notation "∞" := inf.

Record power_series α := series { terms : nat → α }.

Notation "s .[ i ]" := (@terms _ s i) (at level 1).

Definition series_0 {α} {r : ring α} :=
  {| terms i := 0%K |}.
Delimit Scope series_scope with ser.
Notation "0" := series_0 : series_scope.

Inductive eq_series {α} {r : ring α} :
    power_series α → power_series α → Prop :=
  eq_series_base : ∀ s₁ s₂,
    (∀ i, (s₁.[i] = s₂.[i])%K)
    → eq_series s₁ s₂.

Definition series_add {α} {r : ring α} s₁ s₂ :=
  {| terms i := (s₁.[i] + s₂.[i])%K |}.

Definition series_opp {α} {r : ring α} s :=
  {| terms i := (- s.[i])%K |}.
Notation "- a" := (series_opp a) : series_scope.

Definition convol_mul {α} {r : ring α} a b k :=
  Σ (i = 0, k), (a.[i] * b.[k-i])%K.

Definition series_mul {α} {r : ring α} a b :=
  {| terms k := convol_mul a b k |}.

Record puiseux_series α := mkps
  { ps_terms : power_series α;
    ps_ordnum : Z;
    ps_polydo : positive }.
Delimit Scope ps_scope with ps.

Definition series_stretch α {R : ring α} k s :=
  {| terms i :=
       if zerop (i mod Pos.to_nat k) then s .[i / Pos.to_nat k]
       else rng_zero |}.

Definition series_shift α {R : ring α} n s :=
  {| terms i := if lt_dec i n then rng_zero else s .[i - n] |}.

Definition series_left_shift α n (s : power_series α) :=
  {| terms i := s.[n + i] |}.

Definition ps_zero {α} {r : ring α} :=
  {| ps_terms := 0%ser; ps_ordnum := 0; ps_polydo := 1 |}.

Inductive eq_ps {α} {r : ring α} {K : field r} :
  puiseux_series α → puiseux_series α → Prop :=
  | eq_ps_base : ∀ ps₁ ps₂, eq_ps ps₁ ps₂.

Definition ps_monom {α} {r : ring α} (c : α) pow :=
  {| ps_terms := {| terms i := if zerop i then c else 0%K |};
     ps_ordnum := Qnum pow;
     ps_polydo := Qden pow |}.

Definition ps_one {α} {r : ring α} := ps_monom rng_one 0.
Notation "a = b" := (eq_ps a b) : ps_scope.
Notation "0" := ps_zero : ps_scope.

Section other_theorems.

Variable α : Type.

Definition cm (ps₁ ps₂ : puiseux_series α) :=
  (ps_polydo ps₁ * ps_polydo ps₂)%positive.
Definition cm_factor α (ps₁ ps₂ : puiseux_series α) :=
  ps_polydo ps₂.

End other_theorems.

Definition adjust_series α {R : ring α} n k s :=
  series_shift n (series_stretch k s).

Definition ps_terms_add α {R : ring α} (ps₁ ps₂ : puiseux_series α) :=
  let k₁ := cm_factor ps₁ ps₂ in
  let k₂ := cm_factor ps₂ ps₁ in
  let v₁ := (ps_ordnum ps₁ * Zpos k₁)%Z in
  let v₂ := (ps_ordnum ps₂ * Zpos k₂)%Z in
  let n₁ := Z.to_nat (v₁ - Z.min v₁ v₂) in
  let n₂ := Z.to_nat (v₂ - Z.min v₂ v₁) in
  let s₁ := adjust_series n₁ k₁ (ps_terms ps₁) in
  let s₂ := adjust_series n₂ k₂ (ps_terms ps₂) in
  series_add s₁ s₂.

Definition ps_ordnum_add α (ps₁ ps₂ : puiseux_series α) :=
  let k₁ := cm_factor ps₁ ps₂ in
  let k₂ := cm_factor ps₂ ps₁ in
  let v₁ := (ps_ordnum ps₁ * Zpos k₁)%Z in
  let v₂ := (ps_ordnum ps₂ * Zpos k₂)%Z in
  Z.min v₁ v₂.

Definition ps_add {α} {r : ring α} (ps₁ ps₂ : puiseux_series α) :=
  {| ps_terms := ps_terms_add ps₁ ps₂;
     ps_ordnum := ps_ordnum_add ps₁ ps₂;
     ps_polydo := cm ps₁ ps₂ |}.

Notation "a + b" := (ps_add a b) : ps_scope.

Definition ps_mul {α} {r : ring α} ps₁ ps₂ :=
  {| ps_terms :=
       series_mul
         (series_stretch (cm_factor ps₁ ps₂) (ps_terms ps₁))
         (series_stretch (cm_factor ps₂ ps₁) (ps_terms ps₂));
     ps_ordnum :=
       (ps_ordnum ps₁ * Zpos (ps_polydo ps₂) +
        ps_ordnum ps₂ * Zpos (ps_polydo ps₁))%Z;
     ps_polydo :=
       cm ps₁ ps₂ |}.

Definition ps_ring α (R : ring α) (K : field R) : ring (puiseux_series α).
exact ({| rng_zero := ps_zero;
     rng_one := ps_one;
     rng_add := ps_add;
     rng_mul := ps_mul;
     rng_eq := eq_ps |}).
Defined.

Canonical Structure ps_ring.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Theorem glop :
  ∀ a,
@lap_eq (puiseux_series α) (@ps_ring α R K)
    (@lap_mul (puiseux_series α) (@ps_ring α R K)
       (@lap_mul (puiseux_series α) (@ps_ring α R K)
          (@cons (puiseux_series α) (@ps_zero α R) (@nil (puiseux_series α)))
          (@cons (puiseux_series α) (@ps_monom α R (@rng_one α R) a) (@nil (puiseux_series α))))
       []
     )
     [].
Proof.
intros.
Check 1%nat.
rewrite lap_eq_0.
Check 1%nat.
...
