(* $Id: puiseux_series.ml,v 1.219 2013-08-08 01:50:55 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Printf;

open Coq;
open Field;
open Pnums;
open Series;

Record puiseux_series α :=
  { ps_terms : series α;
    ps_valuation : Q }.

value rec series_head is_zero n s =
  match series_nth n s with
  | Some c → if is_zero c then series_head is_zero (n + 1) s else Some (n, c)
  | None → None
  end
;

Definition valuation fld (ps : puiseux_series α) :=
  match series_head (fld_eq fld (zero fld)) 0 (ps_terms ps) with
  | Some (n, c) =>
      Some
        (Qmake
           (Z.add (Qnum (ps_valuation ps)) (Z.of_nat n))
           (Qden (ps_valuation ps)))
  | None =>
      None
  end.

Definition valuation_coeff fld (ps : puiseux_series α) :=
  match series_head (fld_eq fld (zero fld)) 0 (ps_terms ps) with
  | Some (_, c) => c
  | None => zero fld
  end.

Definition stretch_series fld k s :=
  {| terms i :=
       if zerop (i mod k) then terms s (i / k) else zero fld;
     stop :=
       match stop s with
       | Some st => Some (st * k)%nat
       | None => None
       end |}.

Definition adjust fld k ps :=
  let l := (I.mul k (Qden (ps_valuation ps)))%positive in
  {| ps_terms := stretch_series fld (Pos.to_nat k) (ps_terms ps);
     ps_valuation := Qmake (I.mul (Qnum (ps_valuation ps)) (Zpos k)) l |}.

Definition series_pad_left fld n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n)%nat;
     stop :=
       match stop s with
       | Some st => Some (st + n)%nat
       | None => None
       end |}.

Definition lcm_div α (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (Qden (ps_valuation ps₁)) (Qden (ps_valuation ps₂)) in
  Pos.of_nat (Nat.div (Pos.to_nat l) (Pos.to_nat (Qden (ps_valuation ps₁)))).

Definition valnum_diff_0 fld ps₁ ps₂ :=
  {| ps_terms := series_add fld (ps_terms ps₁) (ps_terms ps₂);
     ps_valuation := ps_valuation ps₁ |}.

Definition valnum_diff_pos fld n ps₁ ps₂ :=
  {| ps_terms :=
       series_add fld (ps_terms ps₁)
         (series_pad_left fld (Pos.to_nat n) (ps_terms ps₂));
     ps_valuation := ps_valuation ps₁ |}.

Definition valnum_diff_neg fld n ps₁ ps₂ :=
  {| ps_terms :=
       series_add fld (series_pad_left fld (Pos.to_nat n) (ps_terms ps₁))
         (ps_terms ps₂);
     ps_valuation := ps_valuation ps₂ |}.

Definition valnum_diff fld ms₁ ms₂ d :=
  match d with
  | Z0 => valnum_diff_0 fld ms₁ ms₂
  | Zpos n => valnum_diff_pos fld n ms₁ ms₂
  | Zneg n => valnum_diff_neg fld n ms₁ ms₂
  end.

Definition ps_add fld (ps₁ ps₂ : puiseux_series α) :=
  let ms₁ := adjust fld (lcm_div ps₁ ps₂) ps₁ in
  let ms₂ := adjust fld (lcm_div ps₂ ps₁) ps₂ in
  valnum_diff fld ms₁ ms₂
    (Z.sub (Qnum (ps_valuation ms₂)) (Qnum (ps_valuation ms₁))).

(* *)

Record puiseux_coseries α :=
  { co_terms : coseries α;
    co_valuation : Q }.

value coseries_head fld is_zero n cs =
  series_head is_zero n (series_of_coseries fld cs)
;

Definition puiseux_series_of_puiseux_coseries fld cs :=
  {| ps_terms := series_of_coseries fld (co_terms cs);
     ps_valuation := co_valuation cs |}.

Definition puiseux_coseries_of_puiseux_series cs :=
  {| co_terms := coseries_of_series (ps_terms cs);
     co_valuation := ps_valuation cs |}.

Definition valuation fld (ps : puiseux_coseries α) :=
  valuation fld (puiseux_series_of_puiseux_coseries fld ps).

Definition valuation_coeff α fld (ps : puiseux_coseries α) :=
  valuation_coeff fld (puiseux_series_of_puiseux_coseries fld ps).

value norm fld f x y = fld.ext.normalise (f x y);

CoFixpoint normal_terms α fld n cd₁ (s : coseries α) :=
  match s with
  | Term c ss =>
      match n with
      | O => Term c (normal_terms fld cd₁ cd₁ ss)
      | S n₁ => Term (zero fld) (normal_terms fld n₁ cd₁ s)
      end
  | End => End _
  end.

Definition normal α (fld : field α) l cd ms :=
  {| co_terms :=
       normal_terms fld 0 (cd - 1) (co_terms ms);
     co_valuation :=
       Qmake (Z.mul (Qnum (co_valuation ms)) (Z.of_nat cd)) l |}.

(* ps_add *)

Definition ps_add α fld (ps₁ ps₂ : puiseux_coseries α) :=
  puiseux_coseries_of_puiseux_series
    (ps_add fld (puiseux_series_of_puiseux_coseries fld ps₁)
       (puiseux_series_of_puiseux_coseries fld ps₂)).

(* ps_mul *)

Fixpoint sum_mul_coeff α (fld : field α) i ni₁ s₁ s₂ :=
  match ni₁ with
  | O => None
  | S ni =>
      match sum_mul_coeff fld (S i) ni s₁ s₂ with
      | Some c =>
          match coseries_nth i s₁ with
          | Some c₁ =>
              match coseries_nth ni s₂ with
              | Some c₂ => Some (norm fld (add fld) (mul fld c₁ c₂) c)
              | None => Some c
              end
          | None => Some c
          end
      | None =>
          match coseries_nth i s₁ with
          | Some c₁ =>
              match coseries_nth ni s₂ with
              | Some c₂ => Some (mul fld c₁ c₂)
              | None => None
              end
          | None => None
          end
      end
  end.

Definition series_mul_term α fld (s₁ s₂ : coseries α) :=
  let cofix mul_loop n₁ :=
    match sum_mul_coeff fld 0 n₁ s₁ s₂ with
    | Some c => Term c (mul_loop (S n₁))
    | None => End _
    end
  in
  mul_loop 1%nat.

Definition ps_mul α fld (ps₁ ps₂ : puiseux_coseries α) :=
  let l := Plcm (Qden (co_valuation ps₁)) (Qden (co_valuation ps₂)) in
  let ms₁ :=
    normal fld l (I.to_int (I.div l (Qden (co_valuation ps₁)))) ps₁
  in
  let ms₂ :=
    normal fld l (I.to_int (I.div l (Qden (co_valuation ps₂)))) ps₂
  in
  {| co_terms :=
       series_mul_term fld (co_terms ms₁) (co_terms ms₂);
     co_valuation :=
       Qmake (Z.add (Qnum (co_valuation ms₁)) (Qnum (co_valuation ms₂))) l |}.

(* *)

Record term α β := { coeff : α; power : β }.

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

CoFixpoint term_series_to_coeff_series α zero cd s : coseries α :=
  match s with
  | Term t ns =>
      Term (coeff t)
        (term_series_to_coeff_series zero cd
           (complete zero cd (power t) ns))
  | End =>
      End _
  end.
