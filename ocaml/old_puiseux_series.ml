(* $Id: old_puiseux_series.ml,v 1.12 2013-08-06 20:08:34 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Field;
open Pnums;
open Puiseux_series;
open Series;

Record old_puiseux_series α :=
  { ops_terms : coseries (term α Q);
    ops_comden : positive }.

value rec old_series_head is_zero s =
  match s with
  | Term m t →
      if is_zero m.coeff then old_series_head is_zero (Lazy.force t) else s
  | End →
      End
  end;

Definition old_valuation α fld (ps : old_puiseux_series α) :=
  match old_series_head (is_zero fld) (ops_terms ps) with
  | Term mx _ => Some (power mx)
  | End => None
  end.

(* old_puiseux_series ↔ puiseux_series *)

CoFixpoint term_of_ms α v (s : coseries α) :=
  match s with
  | Term c ns =>
      Term {| coeff := c; power := Qred v |}
        (term_of_ms (Qmake (Z.succ (Qnum v)) (Qden v)) ns)
  | End =>
      End _
  end.

Definition ops_terms_of_ms α (ms : puiseux_coseries α) : coseries (term α Q) :=
  term_of_ms (co_valuation ms) (co_terms ms).

Definition ops_of_ms α (ms : puiseux_coseries α) :=
  {| ops_terms := ops_terms_of_ms ms;
     ops_comden := Qden (co_valuation ms) |}.

Definition ps_terms_of_ps α zero is_zero (ps : old_puiseux_series α) :=
  term_series_to_coeff_series zero (ops_comden ps)
    (old_series_head is_zero (ops_terms ps)).

Definition ms_of_ps α fld (ps : old_puiseux_series α) :=
  {| co_terms :=
       ps_terms_of_ps (zero fld) (is_zero fld) ps;
     co_valuation :=
       match old_valuation fld ps with
       | Some v =>
           Qmake (Qnum (Qred (Qmult v (inject_Z (Zpos (ops_comden ps))))))
             (ops_comden ps)
       | None => Q.zero
       end |}.
