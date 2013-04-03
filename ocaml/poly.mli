(* $Id: poly.mli,v 1.2 2013-04-03 09:30:47 deraugla Exp $ *)

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

value horner : α → (α → α → α) → (α → α → α) → α → polynomial α int → α;
(** horner zero_coeff add_coeff mul_coeff x pol *)
