(* $Id: poly.mli,v 1.23 2013-04-06 20:44:21 deraugla Exp $ *)

type polynomial α = { al : list α };

value pol_add :
  α → (α → α → α) → (α → bool)
  → polynomial α → polynomial α → polynomial α;
(** [pol_add zero_coeff add_coeff is_zero_coeff p₁ p₂] *)

value pol_mul :
  α → (α → α → α) → (α → α → α) → (α → bool)
  → polynomial α → polynomial α → polynomial α;
(** [pol_mul zero_coeff add_coeff mul_coeff is_zero_coeff p₁ p₂] *)

value apply_poly : α → (α → β → α) → (α → γ → α) → polynomial β → γ → α;
(** [apply_poly zero_v add_v_coeff mul_v_x pol x] *)

(**)

type monomial α = { coeff : α; power : int };
type old_polynomial α = { monoms : list (monomial α) };
value p_of_op : α → old_polynomial α → polynomial α;
