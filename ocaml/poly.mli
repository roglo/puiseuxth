(* $Id: poly.mli,v 1.44 2013-06-26 20:09:14 deraugla Exp $ *)

type polynomial α = { al : list α; an : α };
value mkpol : list α → α → polynomial α;
value al : polynomial α → list α;
value an : polynomial α → α;

value pol_add : (α → α → α) → polynomial α → polynomial α → polynomial α;
(** [pol_add add_coeff p₁ p₂] *)

value pol_mul :
  α → (α → α → α) → (α → α → α) → polynomial α → polynomial α → polynomial α;
(** [pol_mul zero_coeff add_coeff mul_coeff p₁ p₂] *)

value apply_poly : (β → α) → (α → β → α) → (α → γ → α) → polynomial β → γ → α;
(** [apply_poly zero_plus_v add_v_coeff mul_v_x pol x] *)
