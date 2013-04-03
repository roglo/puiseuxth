(* $Id: poly.mli,v 1.1 2013-04-03 09:17:31 deraugla Exp $ *)

type monomial α β = { coeff : α; power : β };
type polynomial α β = { monoms : list (monomial α β) };

value pol_add :
  (α → α → α) → (α → bool) → (β → β → int) → polynomial α β → polynomial α β →
    polynomial α β;
(** [pol_add add_coeff is_null_coeff cmp_power] *)

value pol_mul :
  (α → α → α) → (α → α → α) → (α → bool) → (β → β → β) → (β → β → int) →
    polynomial α β → polynomial α β → polynomial α β;
(** [pol_mul add_coeff mul_coeff is_null_coeff add_power cmp_power] *)
