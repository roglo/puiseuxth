(* Polynomial.v *)

Require Import Utf8.
Require Import QArith.

Set Implicit Arguments.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Record polynomial α := mkpol { al : list α }.

(* addition *)

Fixpoint pol_add_loop α (add_coeff : α → α → α) al₁ al₂ :=
  match al₁ with
  | [] => al₂
  | [a₁ … bl₁] =>
      match al₂ with
      | [] => al₁
      | [a₂ … bl₂] => [add_coeff a₁ a₂ … pol_add_loop add_coeff bl₁ bl₂]
      end
  end.

Definition pol_add α (add_coeff : α → α → α) pol₁ pol₂ :=
  {| al := pol_add_loop add_coeff (al pol₁) (al pol₂) |}.

(* multiplication *)

Fixpoint summation_gen_aux α zero_c (add_c : α → α → _) b len g :=
  match len with
  | O => zero_c
  | S len₁ => add_c (g b) (summation_gen_aux zero_c add_c (S b) len₁ g)
  end.

Definition summation_gen α zero_c (add_c : α → α → _) b e g :=
  summation_gen_aux zero_c add_c b (S e - b) g.

Fixpoint pol_convol_mul α zero_c add_c (mul_c : α → α → _) al₁ al₂ i len :=
  match len with
  | O => []
  | S len₁ =>
      [summation_gen zero_c add_c O i
         (λ j, mul_c (List.nth j al₁ zero_c) (List.nth (i - j) al₂ zero_c)) …
       pol_convol_mul zero_c add_c mul_c al₁ al₂ (S i) len₁]
  end.

Definition pol_mul α (zero_c : α) add_c mul_c pol₁ pol₂ :=
  {| al :=
       pol_convol_mul zero_c add_c mul_c (al pol₁) (al pol₂) O
         (max (List.length (al pol₁)) (List.length (al pol₂))) |}.

(* Horner's algorithm *)
Definition apply_poly α β γ
    (zero_c : α) (add_v_c : α → β → α) (mul_v_x : α → γ → α)
    (pol : polynomial β) (x : γ) :=
  List.fold_right (λ c accu, add_v_c (mul_v_x accu x) c) zero_c (al pol).
