(* $Id: puiseux_series.mli,v 1.31 2013-06-26 16:21:54 deraugla Exp $ *)

open Pnums;
open Field;
open Series;

type puiseux_series α =
  { ms_terms : series α;
    ms_valnum : option I.t;
    ms_comden : I.t }
;
value ms_terms : puiseux_series α → series α;
value ms_valnum : puiseux_series α → option I.t;
value ms_comden : puiseux_series α → I.t;

type term α = { coeff : α; power : Q.t };
value coeff : term α → α;
value power : term α → Q.t;

type old_puiseux_series α =
  { ps_terms : series (term α);
    ps_comden : I.t }
;
value ps_terms : old_puiseux_series α → series (term α);
value ps_comden : old_puiseux_series α → I.t;

value ps_add :
  field α (ext α β) → old_puiseux_series α → old_puiseux_series α → old_puiseux_series α;
(** [ps_add fld p₁ p₂] *)

value ps_mul :
  field α (ext α β) → old_puiseux_series α → old_puiseux_series α → old_puiseux_series α;
(** [ps_mul fld p₁ p₂] *)

value series_head : (α → bool) → series (term α) → series (term α);

value valuation : field α β → old_puiseux_series α → option Q.t;
value valuation_coeff : field α β → old_puiseux_series α → α;

(* *)

(* old version to be converted little by little: *)
type old_ps α = { old_ps_mon : list (term α) };

value ps2ops : old_puiseux_series α → old_ps α;
value ops2ps : old_ps α → old_puiseux_series α;
