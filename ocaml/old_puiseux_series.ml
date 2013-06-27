(* $Id: old_puiseux_series.ml,v 1.1 2013-06-27 09:29:00 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Field;
open Pnums;
open Puiseux_series;
open Series;

Record term α := { coeff : α; power : Q }.

Record old_puiseux_series α :=
  { ps_terms : series (term α);
    ps_comden : positive }.

value rec old_series_head is_zero s =
  match s with
  | Term m t →
      if is_zero m.coeff then old_series_head is_zero (Lazy.force t) else s
  | End →
      End
  end;

Definition old_valuation α fld (ps : old_puiseux_series α) :=
  match old_series_head (is_zero fld) (ps_terms ps) with
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

Definition ps_terms_of_ms α (ms : puiseux_series α) : series (term α) :=
  match ms_valnum ms with
  | Some v => term_of_ms (ms_comden ms) v (ms_terms ms)
  | None => End _
  end.

Definition ps_of_ms α (ms : puiseux_series α) :=
  {| ps_terms := ps_terms_of_ms ms;
     ps_comden := ms_comden ms |}.

CoFixpoint complete α (zero : α) (ps : old_puiseux_series α) p s :=
  match s with
  | Term t ns =>
      let p₁ := Qplus p (Qmake I.one (ps_comden ps)) in
      if Qlt_le_dec p₁ (power t) then
        Term {| coeff := zero; power := p₁ |} (complete zero ps p₁ s)
      else
        Term t ns
  | End =>
      End _
  end.

Definition ms_terms_of_ps α zero is_zero (ps : old_puiseux_series α) :=
  let cofix loop s :=
    match s with
    | Term t ns => Term (coeff t) (loop (complete zero ps (power t) ns))
    | End => End _
    end
  in
  loop (old_series_head is_zero (ps_terms ps)).

Definition ms_of_ps α fld (ps : old_puiseux_series α) :=
  {| ms_terms :=
       ms_terms_of_ps (zero fld) (is_zero fld) ps;
     ms_valnum :=
       match old_valuation fld ps with
       | Some v =>
           Some (Qnum (Qred (Qmult v (inject_Z (Zpos (ps_comden ps))))))
       | None =>
           None
       end;
     ms_comden :=
       ps_comden ps |}.
