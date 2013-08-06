(* $Id: puiseux_series.mli,v 1.48 2013-08-06 20:08:34 deraugla Exp $ *)

open Pnums;
open Field;
open Series;

type puiseux_coseries α =
  { co_terms : coseries α;
    co_valuation : Q.t }
;
value co_terms : puiseux_coseries α → coseries α;
value co_valuation : puiseux_coseries α → Q.t;

value ps_add :
  field α (ext α β) → puiseux_coseries α → puiseux_coseries α → puiseux_coseries α;
(** [ps_add fld p₁ p₂] *)

value ps_mul :
  field α (ext α β) → puiseux_coseries α → puiseux_coseries α → puiseux_coseries α;
(** [ps_mul fld p₁ p₂] *)

value series_head : (α → bool) → int → series α → option (int * α);

value valuation : field α β → puiseux_coseries α → option Q.t;
value valuation_coeff : field α β → puiseux_coseries α → α;

(* *)

type term α β = { coeff : α; power : β };
value coeff : term α β → α;
value power : term α β → β;

value term_series_to_coeff_series :
  α → I.t → coseries (term α Q.t) → coseries α;
(** [term_series_to_coeff_series zero comden s *)

value coseries_head :
  field α _ → (α → bool) → int → coseries α → option (int * α);
