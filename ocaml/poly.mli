(* $Id: poly.mli,v 1.9 2013-04-03 21:46:12 deraugla Exp $ *)

type monomial α β = { coeff : α; power : β };
type polynomial α β = { monoms : list (monomial α β) };

value pol_add :
  (α → α → α) → (α → bool) → (β → β → int)
  → polynomial α β → polynomial α β → polynomial α β;
(** [pol_add add_coeff is_null_coeff cmp_power p₁ p₂] *)

value pol_mul :
  (α → α → α) → (α → α → α) → (α → bool) → (β → β → β) → (β → β → int)
  → polynomial α β → polynomial α β → polynomial α β;
(** [pol_mul add_coeff mul_coeff is_null_coeff add_power cmp_power p₁ p₂] *)

value apply_poly :
  α → (α → β → α) → (α → γ → α) → polynomial β int → γ → α;
(** [apply_poly zero_v add_v_coeff mul_v_x pol x] *)

value apply_poly₂ :
  polynomial α int
  → (polynomial α int → α → polynomial α int)
    → (polynomial α int → polynomial α int → polynomial α int)
      → polynomial α int
        → polynomial α int
          → polynomial α int;
(** [apply_poly₂ zero_pol add_pol_coeff mul_pol_pol pol₁ pol₂] *)
