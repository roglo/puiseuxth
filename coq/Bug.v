(* coqc version 8.20.0 compiled with OCaml 4.13.1
   coqtop version 8.20.0
   Expected coqc runtime on this file: 0.352 sec *)

Require Coq.QArith.QArith.
Require Coq.Unicode.Utf8.

Import Coq.Unicode.Utf8.

Set Implicit Arguments.
(*
Reserved Notation "a ∘ b" (left associativity, at level 32).
*)

Class ring α :=
  { rng_zero : α;
    rng_one : α;
    rng_add : α → α → α;
    rng_mul : α → α → α;
    rng_opp : α → α;
    rng_eq : α → α → Prop;
    rng_eq_refl : ∀ a, rng_eq a a;
    rng_eq_sym : ∀ a b, rng_eq a b → rng_eq b a;
    rng_eq_trans : ∀ a b c, rng_eq a b → rng_eq b c → rng_eq a c;
    rng_add_comm : ∀ a b, rng_eq (rng_add a b) (rng_add b a);
    rng_add_assoc : ∀ a b c,
      rng_eq (rng_add a (rng_add b c)) (rng_add (rng_add a b) c);
    rng_add_0_l : ∀ a, rng_eq (rng_add rng_zero a) a;
    rng_add_opp_l : ∀ a, rng_eq (rng_add (rng_opp a) a) rng_zero;
    rng_add_compat_l : ∀ a b c,
      rng_eq a b → rng_eq (rng_add c a) (rng_add c b);
    rng_mul_comm : ∀ a b, rng_eq (rng_mul a b) (rng_mul b a);
    rng_mul_assoc : ∀ a b c,
      rng_eq (rng_mul a (rng_mul b c)) (rng_mul (rng_mul a b) c);
    rng_mul_1_l : ∀ a, rng_eq (rng_mul rng_one a) a;
    rng_mul_compat_l : ∀ a b c,
      rng_eq a b → rng_eq (rng_mul c a) (rng_mul c b);
    rng_mul_add_distr_l : ∀ a b c,
      rng_eq (rng_mul a (rng_add b c))
        (rng_add (rng_mul a b) (rng_mul a c)) }.
Delimit Scope field_scope with K.
Notation "a = b" := (rng_eq a b) : field_scope.
Notation "a + b" := (rng_add a b) : field_scope.
Notation "a * b" := (rng_mul a b) : field_scope.
Notation "- a" := (rng_opp a) : field_scope.
Notation "0" := rng_zero : field_scope.
Notation "1" := rng_one : field_scope.

(*
Add Parametric Relation α (K : ring α) : α rng_eq
 reflexivity proved by rng_eq_refl
 symmetry proved by rng_eq_sym
 transitivity proved by rng_eq_trans
 as eq_rel.
*)

Class field α (rng_ring : ring α) :=
  { fld_inv : α → α;
    fld_mul_inv_l : ∀ a,
      not (rng_eq a rng_zero)
      → rng_eq (rng_mul (fld_inv a) a) rng_one;
    fld_zerop : ∀ a, { rng_eq a rng_zero } + { not (rng_eq a rng_zero) } }.
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
        → lap_eq [x₁ … l₁] [x₂ … l₂]
  | lap_eq_cons_nil : ∀ x l,
      (x = 0)%K
      → lap_eq l []
        → lap_eq [x … l] []
  | lap_eq_nil_cons : ∀ x l,
      (x = 0)%K
      → lap_eq [] l
        → lap_eq [] [x … l].

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

(*
Fixpoint lap_add {α} {r : ring α} al₁ al₂ :=
  match al₁ with
  | [] => al₂
  | [a₁ … bl₁] =>
      match al₂ with
      | [] => al₁
      | [a₂ … bl₂] => [(a₁ + a₂)%K … lap_add bl₁ bl₂]
      end
  end.
*)

Fixpoint lap_convol_mul α (r : ring α) al₁ al₂ i len :=
  match len with
  | O => []
  | S len₁ =>
      [Σ (j = 0, i), (List.nth j al₁ 0 * List.nth (i - j) al₂ 0)%K …
       lap_convol_mul r al₁ al₂ (S i) len₁]
  end.

Definition lap_mul {α} {R : ring α} la lb :=
  lap_convol_mul R la lb 0 (pred (length la + length lb)).

Fixpoint lap_power {α} {r : ring α} la n :=
  match n with
  | O => [1%K]
  | S m => lap_mul la (lap_power la m)
  end.

(*
Definition lap_compose {α} {r : ring α} la lb :=
  List.fold_right (λ c accu, lap_add (lap_mul accu lb) [c]) [] la.

Definition lap_compose2 {α} {r : ring α} la lb :=
  List.fold_right
    (λ i accu,
     lap_add accu (lap_mul [List.nth i la 0] (lap_power lb i)))%K
    [] (List.seq 0 (length la)).
Delimit Scope lap_scope with lap.
Notation "a * b" := (lap_mul a b) : lap_scope.
*)

Global Instance lap_mul_morph α (R : ring α) :
  Proper (lap_eq ==> lap_eq ==> lap_eq) (@lap_mul _ R).
Admitted.

(*
Theorem lap_add_compat : ∀ α (r : ring α) a b c d,
  lap_eq a c
  → lap_eq b d
    → lap_eq (lap_add a b) (lap_add c d).
Admitted.

Theorem lap_mul_compat : ∀ α (r : ring α) a b c d,
  lap_eq a c
  → lap_eq b d
    → lap_eq (lap_mul a b) (lap_mul c d).
Admitted.
*)

Section lap.

Variable α : Type.
Variable r : ring α.

(*
Theorem lap_mul_assoc : ∀ la lb lc,
  lap_eq (lap_mul la (lap_mul lb lc))
    (lap_mul (lap_mul la lb) lc).
Admitted.

Theorem lap_mul_1_r : ∀ la, lap_eq (lap_mul la [1%K]) la.
Admitted.

Theorem lap_power_mul : ∀ la lb n,
  lap_eq
    (lap_power (lap_mul la lb) n)
    (lap_mul (lap_power la n) (lap_power lb n)).
Admitted.
*)

Theorem lap_eq_0 : lap_eq [0%K] [].
Admitted.

End lap.

(*
Record polynomial α := mkpol { al : list α }.
Delimit Scope poly_scope with pol.
Notation "'POL' l" := {| al := l |} (at level 1) : poly_scope.

Definition eq_poly {α} {r : ring α} x y := lap_eq (al x) (al y).

Notation "a = b" := (eq_poly a b) : poly_scope.

Theorem eq_poly_refl α (r : ring α) : reflexive _ eq_poly.
Admitted.

Theorem eq_poly_sym α (r : ring α) : symmetric _ eq_poly.
Admitted.

Theorem eq_poly_trans α (r : ring α) : transitive _ eq_poly.
Admitted.

Add Parametric Relation α (r : ring α) : (polynomial α) eq_poly
 reflexivity proved by (eq_poly_refl r)
 symmetry proved by (eq_poly_sym (r := r))
 transitivity proved by (eq_poly_trans (r := r))
 as eq_poly_rel.

Definition poly_mul {α} {r : ring α} pol₁ pol₂ :=
  {| al := lap_mul (al pol₁) (al pol₂) |}.

Definition poly_power {α} {r : ring α} pol n :=
  (POL (lap_power (al pol) n))%pol.

Definition poly_compose {α} {r : ring α} a b :=
  POL (lap_compose (al a) (al b))%pol.

Definition poly_compose2 {α} {r : ring α} a b :=
  POL (lap_compose2 (al a) (al b))%pol.
Notation "a * b" := (poly_mul a b) : poly_scope.
Notation "a ∘ b" := (poly_compose a b) : poly_scope.

Global Instance poly_mul_morph α (r : ring α) :
  Proper (eq_poly ==> eq_poly ==> eq_poly) poly_mul.
Admitted.

Section poly.

Variable α : Type.
Variable r : ring α.

Theorem poly_mul_compat : ∀ a b c d,
  (a = c)%pol
  → (b = d)%pol
    → (a * b = c * d)%pol.
Admitted.

End poly.
*)

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
Definition series_order {α} {R : ring α} {K : field R} :
    power_series α → nat → Nbar.
Admitted.
Definition greatest_series_x_power : ∀ α (R : ring α) (K : field R),
    power_series α → nat → nat.
Admitted.

Definition series_stretch α {R : ring α} k s :=
  {| terms i :=
       if zerop (i mod Pos.to_nat k) then s .[i / Pos.to_nat k]
       else rng_zero |}.

Definition series_shift α {R : ring α} n s :=
  {| terms i := if lt_dec i n then rng_zero else s .[i - n] |}.

Definition series_shrink α k (s : power_series α) :=
  {| terms i := s.[i * Pos.to_nat k] |}.

Definition series_left_shift α n (s : power_series α) :=
  {| terms i := s.[n + i] |}.

Definition normalise_series α n k (s : power_series α) :=
  series_shrink k (series_left_shift n s).

Definition gcd_ps α n k (ps : puiseux_series α) :=
  Z.gcd (Z.gcd (ps_ordnum ps + Z.of_nat n) (Zpos (ps_polydo ps))) (Z.of_nat k).

Definition ps_zero {α} {r : ring α} :=
  {| ps_terms := 0%ser; ps_ordnum := 0; ps_polydo := 1 |}.

Definition normalise_ps α {R : ring α} {K : field R} ps :=
  match series_order (ps_terms ps) 0 with
  | fin n =>
      let k := greatest_series_x_power K (ps_terms ps) n in
      let g := gcd_ps n k ps in
      {| ps_terms := normalise_series n (Z.to_pos g) (ps_terms ps);
         ps_ordnum := (ps_ordnum ps + Z.of_nat n) / g;
         ps_polydo := Z.to_pos (Zpos (ps_polydo ps) / g) |}
  | ∞ =>
      ps_zero
  end.

Inductive eq_ps_strong {α} {r : ring α} :
  puiseux_series α → puiseux_series α → Prop :=
  | eq_strong_base : ∀ ps₁ ps₂,
      ps_ordnum ps₁ = ps_ordnum ps₂
      → ps_polydo ps₁ = ps_polydo ps₂
        → eq_series (ps_terms ps₁) (ps_terms ps₂)
          → eq_ps_strong ps₁ ps₂.

Inductive eq_ps {α} {r : ring α} {K : field r} :
  puiseux_series α → puiseux_series α → Prop :=
  | eq_ps_base : ∀ ps₁ ps₂,
      eq_ps_strong (normalise_ps ps₁) (normalise_ps ps₂)
      → eq_ps ps₁ ps₂.

Definition ps_monom {α} {r : ring α} (c : α) pow :=
  {| ps_terms := {| terms i := if zerop i then c else 0%K |};
     ps_ordnum := Qnum pow;
     ps_polydo := Qden pow |}.

Definition ps_one {α} {r : ring α} := ps_monom rng_one 0.
Notation "a = b" := (eq_ps a b) : ps_scope.
Notation "0" := ps_zero : ps_scope.
Notation "1" := ps_one : ps_scope.

Section eq_ps_equiv_rel.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Theorem eq_ps_refl : reflexive _ eq_ps.
Admitted.

Theorem eq_ps_sym : symmetric _ eq_ps.
Admitted.

Theorem eq_ps_trans : transitive _ eq_ps.
Admitted.

End eq_ps_equiv_rel.

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

Definition ps_opp {α} {r : ring α} ps :=
  {| ps_terms := (- ps_terms ps)%ser;
     ps_ordnum := ps_ordnum ps;
     ps_polydo := ps_polydo ps |}.

Notation "- a" := (ps_opp a) : ps_scope.

Section theorems_add.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Theorem ps_add_comm : ∀ ps₁ ps₂, (ps₁ + ps₂ = ps₂ + ps₁)%ps.
Admitted.

Theorem ps_add_assoc : ∀ ps₁ ps₂ ps₃,
  (ps₁ + (ps₂ + ps₃) = (ps₁ + ps₂) + ps₃)%ps.
Admitted.

Theorem ps_add_0_l : ∀ ps, (0 + ps = ps)%ps.
Admitted.

Theorem ps_add_opp_l : ∀ ps, (- ps + ps = 0)%ps.
Admitted.

End theorems_add.

Section theorem_add_compat.

Variable α : Type.
Variable r : ring α.
Variable K : field r.

Theorem ps_add_compat_l : ∀ ps₁ ps₂ ps₃,
  (ps₁ = ps₂)%ps
  → (ps₃ + ps₁ = ps₃ + ps₂)%ps.
Admitted.

End theorem_add_compat.

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

Notation "a * b" := (ps_mul a b) : ps_scope.

Section theorems_for_mul.

Variable α : Type.
Variable r : ring α.
Variable K : field r.

Theorem ps_mul_comm : ∀ ps₁ ps₂, (ps₁ * ps₂ = ps₂ * ps₁)%ps.
Admitted.

Theorem ps_mul_1_l : ∀ ps, (1 * ps = ps)%ps.
Admitted.

(*
Theorem ps_mul_1_r : ∀ ps, (ps * 1 = ps)%ps.
Admitted.
*)

Theorem ps_mul_assoc : ∀ ps₁ ps₂ ps₃,
  (ps₁ * (ps₂ * ps₃) = (ps₁ * ps₂) * ps₃)%ps.
Admitted.

Theorem ps_mul_compat_l : ∀ ps₁ ps₂ ps₃,
  (ps₁ = ps₂)%ps
  → (ps₃ * ps₁ = ps₃ * ps₂)%ps.
Admitted.

End theorems_for_mul.

Section other_theorems.

Variable α : Type.
Variable r : ring α.
Variable K : field r.

Theorem ps_mul_add_distr_l : ∀ ps₁ ps₂ ps₃,
  (ps₁ * (ps₂ + ps₃) = ps₁ * ps₂ + ps₁ * ps₃)%ps.
Admitted.

End other_theorems.

Definition ps_ring α (R : ring α) (K : field R) : ring (puiseux_series α).
exact ({| rng_zero := ps_zero;
     rng_one := ps_one;
     rng_add := ps_add;
     rng_mul := ps_mul;
     rng_opp := ps_opp;
     rng_eq := eq_ps;
     rng_eq_refl := eq_ps_refl K;
     rng_eq_sym := eq_ps_sym (K := K);
     rng_eq_trans := eq_ps_trans (K := K);
     rng_add_comm := ps_add_comm K;
     rng_add_assoc := ps_add_assoc K;
     rng_add_0_l := ps_add_0_l K;
     rng_add_opp_l := ps_add_opp_l K;
     rng_add_compat_l := @ps_add_compat_l α R K;
     rng_mul_comm := ps_mul_comm K;
     rng_mul_assoc := ps_mul_assoc K;
     rng_mul_1_l := ps_mul_1_l K;
     rng_mul_compat_l := @ps_mul_compat_l α R K;
     rng_mul_add_distr_l := ps_mul_add_distr_l K |}).
Defined.

Canonical Structure ps_ring.

(*
Definition ps_lap_nth α {R : ring α} h la := (List.nth h la 0)%ps.
Definition ps_poly_nth α {R : ring α} h f := (ps_lap_nth h (al f)).

Definition ps_pol_eq α {R : ring α} {K : field R} a b :=
  @eq_poly (puiseux_series α) (ps_ring K) a b.

Definition ps_pol_mul α {R : ring α} {K : field R} a b :=
  @poly_mul (puiseux_series α) (ps_ring K) a b.

Definition ps_pol_pow α {R : ring α} {K : field R} a n :=
  @poly_power (puiseux_series α) (ps_ring K) a n.

Definition ps_pol_comp α {R : ring α} {K : field R} a b :=
  @poly_compose (puiseux_series α) (ps_ring K) a b.

Definition ps_pol α a := @mkpol (puiseux_series α) a.
Delimit Scope ps_pol_scope with pspol.
Notation "a = b" := (ps_pol_eq a b) : ps_pol_scope.
Notation "a * b" := (ps_pol_mul a b) : ps_pol_scope.
Notation "a ^ b" := (ps_pol_pow a b) : ps_pol_scope.
Notation "a ∘ b" := (ps_pol_comp a b) : ps_pol_scope.
Notation "'POL' l" := (ps_pol l) (at level 1) : ps_pol_scope.
Definition ps_field α {R : ring α} {K : field R} : field (ps_ring K).
Admitted.

Theorem poly_compose_compose2 : ∀ α (r : ring α) P Q,
  (P ∘ Q = poly_compose2 P Q)%pol.
Admitted.

Definition next_lap α {R : ring α} {K : field R} f β₁ γ₁ (c₁ : α) :=
  let _ := ps_ring K in
  ([ps_monom 1%K (- β₁)] *
   lap_compose f [ps_monom c₁ γ₁; ps_monom 1%K γ₁ … []])%lap.

Definition next_pol α {R : ring α} {K : field R} f β₁ γ₁ c₁ :=
  (POL (next_lap (al f) β₁ γ₁ c₁))%pol.

Definition lap_summation α {R : ring α} {K : field R} (li : list nat) g :=
  List.fold_right (λ i accu, lap_add accu (g i)) [] li.

Definition poly_summation α {R : ring α} {K : field R} (li : list nat) g :=
  (POL (lap_summation li (λ i, al (g i))))%pol.

Definition ps_pol_summ α {R : ring α} {K : field R} ln f :=
  @poly_summation (puiseux_series α) (ps_ring K) ln f.

Global Instance ps_monom_qeq_morph α (r : ring α) (K : field r) :
  Proper (rng_eq ==> Qeq ==> eq_ps) ps_monom.
Admitted.

Theorem list_fold_right_compat : ∀ α β equal g h (a₀ : α) (l : list β),
  (∀ x y z, equal x y → equal (g z x) (h z y))
  → equal a₀ a₀
    → equal (List.fold_right g a₀ l) (List.fold_right h a₀ l).
Admitted.
*)

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Theorem glop :
  ∀ γ₁,
@lap_eq (puiseux_series α) (@ps_ring α R K)
    (@lap_mul (puiseux_series α) (@ps_ring α R K)
       (@lap_mul (puiseux_series α) (@ps_ring α R K)
          (@cons (puiseux_series α) (@ps_zero α R) (@nil (puiseux_series α)))
          (@cons (puiseux_series α) (@ps_monom α R (@rng_one α R) γ₁) (@nil (puiseux_series α))))
       (@lap_power (puiseux_series α) (@ps_ring α R K)
          (@cons (puiseux_series α) (@ps_monom α R (@rng_one α R) γ₁) (@nil (puiseux_series α))) 0))
    (@cons (puiseux_series α)
       (@ps_mul α R (@ps_zero α R) (@ps_monom α R (@rng_one α R) (Qmult (Qnat (S 0)) γ₁)))
       (@nil (puiseux_series α))).
Proof.
intros.
Check 1%nat.
Check lap_eq_0.
rewrite lap_eq_0.
Check 1%nat.
...

Theorem f₁_eq_x_min_β₁_comp : ∀ f β₁ γ₁ c₁,
  (next_pol f β₁ γ₁ c₁ =
   POL [ps_monom 1%K (- β₁)] *
   f ∘ (POL [ps_monom 1%K γ₁] * POL [ps_monom c₁ 0; 1%ps … []]))%pspol.
Admitted.

Theorem f₁_eq_x_min_β₁_summation : ∀ f β₁ γ₁ (c₁ : α),
  (next_pol f β₁ γ₁ c₁ =
   POL [ps_monom 1%K (- β₁)] *
   ps_pol_summ ps_field (List.seq 0 (length (al f)))
     (λ h,
      let āh := ps_poly_nth h f in
      POL [(āh * ps_monom 1%K (Qnat h * γ₁))%ps] *
      POL [ps_monom c₁ 0; 1%ps … []] ^ h))%pspol.
Proof.
intros f β₁ γ₁ c.
rewrite f₁_eq_x_min_β₁_comp.
progress unfold ps_pol_comp.
rewrite poly_compose_compose2.
apply poly_mul_compat; [ reflexivity | idtac ].
progress unfold poly_compose2; simpl.
progress unfold lap_compose2, poly_summation; simpl.
progress unfold eq_poly; simpl.
apply list_fold_right_compat; [ idtac | reflexivity ].
intros la lb i Heq.
apply lap_add_compat; [ assumption | idtac ].
progress unfold ps_poly_nth, ps_lap_nth.
rewrite lap_power_mul.
rewrite lap_mul_assoc.
apply lap_mul_compat; [ idtac | reflexivity ].
clear la lb Heq.
remember (al f) as la; clear f Heqla.
revert la.
induction i; intros; simpl.
 rewrite lap_mul_1_r.
 constructor; [ idtac | reflexivity ].
 progress unfold Qnat; simpl.
 rewrite <- ps_mul_1_r in |- * at 1.
 apply ps_mul_compat_l.
 rewrite Qmult_0_l; reflexivity.

 destruct la as [| a]; simpl.
  rewrite lap_mul_assoc; simpl.

...
  Check 1%nat.
  rewrite lap_eq_0.
  Check 1%nat.
