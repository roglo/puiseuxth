(* $Id: poly.mli,v 1.14 2013-04-06 09:07:58 deraugla Exp $ *)

type monomial α = { coeff : α; power : int };
type polynomial α = { monoms : list (monomial α) };

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
