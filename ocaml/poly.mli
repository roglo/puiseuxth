(* $Id: poly.mli,v 1.16 2013-04-06 10:42:36 deraugla Exp $ *)

type monomial α = { coeff : α; power : int };
type polynomial α = { monoms : list (monomial α) };

type new_polynomial α = { al : list α };
value np_of_p : α → polynomial α → new_polynomial α;
value p_of_np : (α → bool) → new_polynomial α → polynomial α;

value pol_add :
  (α → α → α) → (α → bool)
  → polynomial α → polynomial α → polynomial α;
(** [pol_add add_coeff is_null_coeff p₁ p₂] *)

value pol_mul :
  (α → α → α) → (α → α → α) → (α → bool)
  → polynomial α → polynomial α → polynomial α;
(** [pol_mul add_coeff mul_coeff is_null_coeff p₁ p₂] *)

value apply_poly :
   α → (α → β → α) → (α → γ → α) → polynomial β → γ → α;
(** [apply_poly zero_v add_v_coeff mul_v_x pol x] *)
