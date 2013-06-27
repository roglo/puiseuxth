(* $Id: puiseux_series.mli,v 1.35 2013-06-27 18:58:11 deraugla Exp $ *)

open Pnums;
open Field;
open Series;

type puiseux_series α =
  { ms_terms : series α;
    ms_valnum : I.t;
    ms_comden : I.t }
;
value ms_terms : puiseux_series α → series α;
value ms_valnum : puiseux_series α → I.t;
value ms_comden : puiseux_series α → I.t;

value ps_add :
  field α (ext α β) → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_add fld p₁ p₂] *)

value ps_mul :
  field α (ext α β) → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_mul fld p₁ p₂] *)

value series_head : (α → bool) → series α → series α;

value valuation : field α β → puiseux_series α → option Q.t;
value valuation_coeff : field α β → puiseux_series α → α;
