(* $Id: puiseux_series.ml,v 1.201 2013-08-06 08:36:17 deraugla Exp $ *)

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

Definition valuation α fld (ps : puiseux_series α) :=
  match series_head (is_zero fld) 0 (ps_terms ps) with
  | Some (n, c) =>
      Some
        (Qmake (Z.add (Qnum (ps_valuation ps)) (Z.of_nat n))
           (Qden (ps_valuation ps)))
  | None =>
      None
  end.

Definition valuation_coeff α fld (ps : puiseux_series α) :=
  match series_head (is_zero fld) 0 (ps_terms ps) with
  | Some (_, c) => c
  | None => zero fld
  end.

value norm fld f x y = fld.ext.normalise (f x y);

Definition stretch_series fld k s :=
  {| terms i :=
       if zerop (i mod k) then terms s (i / k) else zero fld;
     stop :=
       match stop s with
       | Some st => Some (st * k)%nat
       | None => None
       end |}.

Definition normalise fld k ps :=
  let l := (I.mul k (Qden (ps_valuation ps)))%positive in
  {| ps_terms := stretch_series fld (Pos.to_nat k) (ps_terms ps);
     ps_valuation := Qmake (I.mul (Qnum (ps_valuation ps)) (Zpos k)) l |}.

(* ps_add *)

Definition series_pad_left fld n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n)%nat;
     stop :=
       match stop s with
       | Some st => Some (st - n)%nat
       | None => None
       end |}.

Definition lcm_div α (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (Qden (ps_valuation ps₁)) (Qden (ps_valuation ps₂)) in
  Pos.of_nat (div (Pos.to_nat l) (Pos.to_nat (Qden (ps_valuation ps₁)))).

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
  let ms₁ := normalise fld (lcm_div ps₁ ps₂) ps₁ in
  let ms₂ := normalise fld (lcm_div ps₂ ps₁) ps₂ in
  valnum_diff fld ms₁ ms₂
    (Z.sub (Qnum (ps_valuation ms₂)) (Qnum (ps_valuation ms₁))).

(* ps_mul *)

Fixpoint sum_mul_coeff α (fld : field α) i ni₁ s₁ s₂ :=
  match ni₁ with
  | O => None
  | S ni =>
      match sum_mul_coeff fld (S i) ni s₁ s₂ with
      | Some c =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (norm fld (add fld) (mul fld c₁ c₂) c)
              | None => Some c
              end
          | None => Some c
          end
      | None =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (mul fld c₁ c₂)
              | None => None
              end
          | None => None
          end
      end
  end.

Definition ps_mul_term fld (s₁ s₂ : series α) :=
  {| terms i :=
       match sum_mul_coeff fld 0 (S i) s₁ s₂ with
       | Some c => c
       | None => zero fld
       end;
     stop :=
       match stop s₁ with
       | Some st₁ =>
           match stop s₂ with
           | Some st₂ => Some (max st₁ st₂)
           | None => None
           end
       | None => None
       end |}.

Definition ps_mul fld (ps₁ ps₂ : puiseux_series α) :=
  let ms₁ := normalise fld (lcm_div ps₁ ps₂) ps₁ in
  let ms₂ := normalise fld (lcm_div ps₂ ps₁) ps₂ in
  let l := Plcm (Qden (ps_valuation ps₁)) (Qden (ps_valuation ps₂)) in
  {| ps_terms := ps_mul_term fld (ps_terms ms₁) (ps_terms ms₂);
     ps_valuation :=
       Qmake (I.add (Qnum (ps_valuation ms₁)) (Qnum (ps_valuation ms₂))) l |}.

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

CoFixpoint term_series_to_coeff_series α zero cd s : series α :=
  match s with
  | Term t ns =>
      Term (coeff t)
        (term_series_to_coeff_series zero cd
           (complete zero cd (power t) ns))
  | End =>
      End _
  end.
