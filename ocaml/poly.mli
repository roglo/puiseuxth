(* $Id: poly.mli,v 1.34 2013-05-23 14:19:51 deraugla Exp $ *)

type polynomial α = { al : list α; an : α };
value mkpol : unit → list α → α → polynomial α;
value al : polynomial α → list α;
value an : polynomial α → α;

value pol_add :
  unit → (α → α → α) → polynomial α → polynomial α → polynomial α;
(** [pol_add () add_coeff p₁ p₂] *)

(* *)

type old_poly α = { ml : list α };

value pol_mul :
  α → (α → α → α) → (α → α → α) → (α → bool)
  → old_poly α → old_poly α → old_poly α;
(** [pol_mul zero_coeff add_coeff mul_coeff is_zero_coeff p₁ p₂] *)

value apply_poly : α → (α → β → α) → (α → γ → α) → polynomial β → γ → α;
(** [apply_poly zero_v add_v_coeff mul_v_x pol x] *)

open Field;

value p2op : field α _ → polynomial α → old_poly α;
value op2p : field α _ → old_poly α → polynomial α;
