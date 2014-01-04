(* Fsummation.v *)

Require Import Utf8.

Require Import Field.

Set Implicit Arguments.

Fixpoint summation_aux α (f : field α) b len g :=
  match len with
  | O => .0 f%F
  | S len₁ => (g b .+ f summation_aux f (S b) len₁ g)%F
  end.

Definition summation α (f : field α) b e g := summation_aux f b (S e - b) g.

Notation "'Σ' f ( i = b , e ) '_' g" := (summation f b e (λ i, (g)%F))
  (at level 0, f at level 0, i at level 0, b at level 60, e at level 60,
   g at level 40).
