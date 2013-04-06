(* $Id: poly.mli,v 1.18 2013-04-06 11:07:28 deraugla Exp $ *)

type monomial α = { coeff : α; power : int };
type old_polynomial α = { monoms : list (monomial α) };

type polynomial α = { al : list α };
value p_of_op : α → old_polynomial α → polynomial α;
value op_of_p : (α → bool) → polynomial α → old_polynomial α;

value pol_add :
  (α → α → α) → (α → bool)
  → old_polynomial α → old_polynomial α → old_polynomial α;
(** [pol_add add_coeff is_null_coeff p₁ p₂] *)

value pol_mul :
  (α → α → α) → (α → α → α) → (α → bool)
  → old_polynomial α → old_polynomial α → old_polynomial α;
(** [pol_mul add_coeff mul_coeff is_null_coeff p₁ p₂] *)

value apply_poly :
   α → (β → bool) → (α → β → α) → (α → γ → α) → polynomial β → γ
   → α;
(** [apply_poly zero_v is_zero_v add_v_coeff mul_v_x pol x] *)
