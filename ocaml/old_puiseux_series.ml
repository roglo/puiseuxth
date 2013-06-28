(* $Id: old_puiseux_series.ml,v 1.4 2013-06-28 09:01:21 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Field;
open Pnums;
open Puiseux_series;
open Series;

Record term α := { coeff : α; power : Q }.

Record old_puiseux_series α :=
  { ops_terms : series (term α);
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

CoFixpoint term_of_ms α cd p (s : series α) :=
  match s with
  | Term c ns =>
      Term {| coeff := c; power := Qred (Qmake p cd) |}
        (term_of_ms cd (Z.succ p) ns)
  | End =>
      End _
  end.

Definition ops_terms_of_ms α (ms : puiseux_series α) : series (term α) :=
  term_of_ms (ps_comden ms) (ps_valnum ms) (ps_terms ms).

Definition ops_of_ms α (ms : puiseux_series α) :=
  {| ops_terms := ops_terms_of_ms ms;
     ops_comden := ps_comden ms |}.

CoFixpoint complete α (zero : α) cd p s :=
  match s with
  | Term t ns =>
      let p₁ := Qplus p (Qmake I.one cd) in
      if Qlt_le_dec p₁ (power t) then
        Term {| coeff := zero; power := p₁ |} (complete zero cd p₁ s)
      else
        Term t ns
  | End =>
      End _
  end.

CoFixpoint old_ps_to_ps zero cd s :=
  match s with
  | Term t ns =>
      Term (coeff t) (old_ps_to_ps zero cd (complete zero cd (power t) ns))
  | End =>
      End _
  end.

Definition ps_terms_of_ps α zero is_zero (ps : old_puiseux_series α) :=
  old_ps_to_ps zero (ops_comden ps) (old_series_head is_zero (ops_terms ps)).

Definition ms_of_ps α fld (ps : old_puiseux_series α) :=
  {| ps_terms :=
       ps_terms_of_ps (zero fld) (is_zero fld) ps;
     ps_valnum :=
       match old_valuation fld ps with
       | Some v => Qnum (Qred (Qmult v (inject_Z (Zpos (ops_comden ps)))))
       | None => I.zero
       end;
     ps_comden :=
       ops_comden ps |}.
