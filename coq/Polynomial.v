(* $Id: Polynomial.v,v 1.3 2013-07-08 21:12:35 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Set Implicit Arguments.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Record polynomial α := mkpol { al : list α; an : α }.

Fixpoint pol_add_loop α (add_coeff : α → α → α) an₁ an₂ al₁ al₂ :=
  match al₁ with
  | [] =>
      match al₂ with
      | [] => {| al := []; an := add_coeff an₁ an₂ |}
      | [a₂ … bl₂] => {| al := [add_coeff an₁ a₂ … bl₂]; an := an₂ |}
      end
  | [a₁ … bl₁] =>
      match al₂ with
      | [] => {| al := [add_coeff a₁ an₂ … bl₁]; an := an₁ |}
      | [a₂ … bl₂] =>
          let r := pol_add_loop add_coeff an₁ an₂ bl₁ bl₂ in
          {| al := [add_coeff a₁ a₂ … al r]; an := an r |}
      end
  end.

Definition pol_add α (add_coeff : α → α → α) pol₁ pol₂ :=
  pol_add_loop add_coeff (an pol₁) (an pol₂) (al pol₁) (al pol₂).

Fixpoint insert_pol_term α (add_coeff : α → α → α) c₁ p₁ ml :=
  match ml with
  | [] => [(c₁, p₁)]
  | [(c₂, p₂) … ml₂] =>
      match nat_compare p₁ p₂ with
      | Eq => [(add_coeff c₁ c₂, p₂) … ml₂]
      | Lt => [(c₁, p₁) … ml]
      | Gt => [(c₂, p₂) … insert_pol_term add_coeff c₁ p₁ ml₂]
      end
  end.

Fixpoint combine_pol α add_coeff (mul_coeff : α → α → α) c₁ pow₁ pow₂ ml
    cn cl :=
  let p := (pow₁ + pow₂)%nat in
  match cl with
  | [] =>
      let c := mul_coeff c₁ cn in
      insert_pol_term add_coeff c p ml
  | [c₂ … cl₂] =>
      let c := mul_coeff c₁ c₂ in
      let ml := insert_pol_term add_coeff c p ml in
      combine_pol add_coeff mul_coeff c₁ pow₁ (S pow₂) ml cn cl₂
  end.

Fixpoint mul_loop α (add_coeff : α → α → α) mul_coeff ml pow₁ cn₂ cl₂
    cn₁ cl₁ :=
  match cl₁ with
  | [] => combine_pol add_coeff mul_coeff cn₁ pow₁ 0 ml cn₂ cl₂
  | [c … cl] =>
      let ml := combine_pol add_coeff mul_coeff c pow₁ 0 ml cn₂ cl₂ in
      mul_loop add_coeff mul_coeff ml (S pow₁) cn₂ cl₂ cn₁ cl
  end.

Fixpoint make_pol α (zero_coeff : α) pow ml n :=
  match n with
  | O => ([], zero_coeff)
  | S n₁ =>
      match ml with
      | [] => ([], zero_coeff)
      | [(c, p)] =>
          if eq_nat_dec p pow then ([], c)
          else
            let (cl, cn) := make_pol zero_coeff (S pow) [(c, p)] n₁ in
            ([zero_coeff … cl], cn)
      | [(c, p) … ml₁] =>
          if eq_nat_dec p pow then
            let (cl, cn) := make_pol zero_coeff (S pow) ml₁ n₁ in
            ([c … cl], cn)
          else
            let (cl, cn) := make_pol zero_coeff (S pow) ml n₁ in
            ([zero_coeff … cl], cn)
      end
  end.

Definition pol_mul α (zero_coeff : α) add_coeff mul_coeff pol₁ pol₂ :=
  let ml :=
    mul_loop add_coeff mul_coeff [] 0 (an pol₂) (al pol₂) (an pol₁) (al pol₁)
  in
  let (cl, cn) := make_pol zero_coeff 0 ml (List.length ml) in
  {| al := cl; an := cn |}.

(* Horner's algorithm *)
Definition apply_poly α β γ
    (zero_plus_v : β → α) (add_v_coeff : α → β → α) (mul_v_x : α → γ → α)
    (pol : polynomial β) (x : γ) :=
  List.fold_right (λ c accu, add_v_coeff (mul_v_x accu x) c)
    (zero_plus_v (an pol)) (al pol).
