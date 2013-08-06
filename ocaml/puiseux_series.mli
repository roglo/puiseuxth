(* $Id: puiseux_series.mli,v 1.47 2013-08-06 19:27:56 deraugla Exp $ *)

open Pnums;
open Field;
open Series;

type puiseux_series α =
  { ps_terms : coseries α;
    ps_valuation : Q.t }
;
value ps_terms : puiseux_series α → coseries α;
value ps_valuation : puiseux_series α → Q.t;

value ps_add :
  field α (ext α β) → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_add fld p₁ p₂] *)

value ps_mul :
  field α (ext α β) → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_mul fld p₁ p₂] *)

value series_head : (α → bool) → int → series α → option (int * α);

value valuation : field α β → puiseux_series α → option Q.t;
value valuation_coeff : field α β → puiseux_series α → α;

(* *)

type term α β = { coeff : α; power : β };
value coeff : term α β → α;
value power : term α β → β;

value term_series_to_coeff_series :
  α → I.t → coseries (term α Q.t) → coseries α;
(** [term_series_to_coeff_series zero comden s *)

value coseries_head :
  field α _ → (α → bool) → int → coseries α → option (int * α);
