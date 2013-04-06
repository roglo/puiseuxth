(* $Id: poly.mli,v 1.12 2013-04-06 08:37:30 deraugla Exp $ *)

type monomial α = { coeff : α; power : int };
type polynomial α = { monoms : list (monomial α) };

type monomial₂ α = { coeff₂ : α; power₂ : Pnums.Q.t };
type puiseux_series α = { monoms₂ : list (monomial₂ α) };

value pol_add :
  (α → α → α) → (α → bool)
  → polynomial α → polynomial α → polynomial α;
(** [pol_add add_coeff is_null_coeff p₁ p₂] *)

value pol_mul :
  (α → α → α) → (α → α → α) → (α → bool)
  → polynomial α → polynomial α → polynomial α;
(** [pol_mul add_coeff mul_coeff is_null_coeff p₁ p₂] *)

value pol_add₂ :
  (α → α → α) → (α → bool) → (Pnums.Q.t → Pnums.Q.t → int)
  → puiseux_series α → puiseux_series α → puiseux_series α;
(** [pol_add₂ add_coeff is_null_coeff cmp_power p₁ p₂] *)

value pol_mul₂ :
  (α → α → α) → (α → α → α) → (α → bool)
  → (Pnums.Q.t → Pnums.Q.t → Pnums.Q.t) → (Pnums.Q.t → Pnums.Q.t → int)
    → puiseux_series α → puiseux_series α → puiseux_series α;
(** [pol_mul₂ add_coeff mul_coeff is_null_coeff add_power cmp_power p₁ p₂] *)

value apply_poly :
   α → (α → β → α) → (α → γ → α) → polynomial β → γ → α;
(** [apply_poly zero_v add_v_coeff mul_v_x pol x] *)
