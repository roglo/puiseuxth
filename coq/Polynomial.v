(* Polynomial.v *)

Require Import Utf8.
Require Import QArith.

Set Implicit Arguments.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Record polynomial α := mkpol { bl : list α }.

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
  {| bl := pol_add_loop add_coeff (bl pol₁) (bl pol₂) |}.

(* multiplication *)

Fixpoint sigma_aux α zero_v (add_v : α → α → _) b len g :=
  match len with
  | O => zero_v
  | S len₁ => add_v (g b) (sigma_aux zero_v add_v (S b) len₁ g)
  end.

Definition sigma α zero_v (add_v : α → α → _) b e g :=
  sigma_aux zero_v add_v b (S e - b) g.

Fixpoint pol_convol_mul α zero_v add_v (mul_v : α → α → _) al₁ al₂ i len :=
  match len with
  | O => []
  | S len₁ =>
      [sigma zero_v add_v O i
         (λ j, mul_v (List.nth j al₁ zero_v) (List.nth (i - j) al₂ zero_v)) …
       pol_convol_mul zero_v add_v mul_v al₁ al₂ (S i) len₁]
  end.

Definition pol_mul α (zero_v : α) add_v mul_v pol₁ pol₂ :=
  {| bl :=
       pol_convol_mul zero_v add_v mul_v (bl pol₁) (bl pol₂) O
         (max (List.length (bl pol₁)) (List.length (bl pol₂))) |}.

(* Horner's algorithm *)
Definition apply_poly α β γ
    (zero_plus_v : β → α) (add_v_coeff : α → β → α) (mul_v_x : α → γ → α)
    (pol : polynomial β) (x : γ) :=
  List.fold_right (λ c accu, add_v_coeff (mul_v_x accu x) c)
    (zero_plus_v (bl pol)) (bl pol).
