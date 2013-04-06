(* $Id: poly.mli,v 1.27 2013-04-06 22:51:30 deraugla Exp $ *)

type polynomial α = { al : list α };

value pol_add :
  (α → α → α) → polynomial α → polynomial α → polynomial α;
(** [pol_add add_coeff p₁ p₂] *)

value pol_mul :
  α → (α → α → α) → (α → α → α) → (α → bool)
  → polynomial α → polynomial α → polynomial α;
(** [pol_mul zero_coeff add_coeff mul_coeff is_zero_coeff p₁ p₂] *)

value apply_poly : α → (α → β → α) → (α → γ → α) → polynomial β → γ → α;
(** [apply_poly zero_v add_v_coeff mul_v_x pol x] *)

(**)

type old_monomial α = { old_coeff : α; old_power : int };
value p_of_op : α → list (old_monomial α) → polynomial α;
