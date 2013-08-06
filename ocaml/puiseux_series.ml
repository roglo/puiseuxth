(* $Id: puiseux_series.ml,v 1.208 2013-08-06 19:27:56 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Printf;

open Coq;
open Field;
open Pnums;
open Series;

Record puiseux_series α :=
  { ps_terms : coseries α;
    ps_valuation : Q }.

value rec series_head is_zero n s =
  match series_nth n s with
  | Some c → if is_zero c then series_head is_zero (n + 1) s else Some (n, c)
  | None → None
  end
;

value coseries_head fld is_zero n cs =
  series_head is_zero n (series_of_coseries fld cs)
;

Definition valuation α fld (ps : puiseux_series α) :=
  match coseries_head fld (is_zero fld) 0 (ps_terms ps) with
  | Some (n, c) =>
      Some
        (Qmake (Z.add (Qnum (ps_valuation ps)) (Z.of_nat n))
           (Qden (ps_valuation ps)))
  | None =>
      None
  end.

Definition valuation_coeff α fld (ps : puiseux_series α) :=
  match coseries_head fld (is_zero fld) 0 (ps_terms ps) with
  | Some (_, c) => c
  | None => zero fld
  end.

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
  {| ps_terms :=
       normal_terms fld 0 (cd - 1) (ps_terms ms);
     ps_valuation :=
       Qmake (Z.mul (Qnum (ps_valuation ms)) (Z.of_nat cd)) l |}.

(* ps_add *)

CoFixpoint series_add α (fld : field α) s₁ s₂ :=
  match s₁ with
  | Term c₁ ss₁ =>
      match s₂ with
      | Term c₂ ss₂ => Term (add fld c₁ c₂) (series_add fld ss₁ ss₂)
      | End => s₁
      end
  | End => s₂
  end.

Fixpoint series_pad_left α (fld : field α) n s :=
  match n with
  | O => s
  | S n₁ => Term (zero fld) (series_pad_left fld n₁ s)
  end.

Definition ps_add α fld (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (Qden (ps_valuation ps₁)) (Qden (ps_valuation ps₂)) in
  let ms₁ :=
    normal fld l (I.to_int (I.div l (Qden (ps_valuation ps₁)))) ps₁
  in
  let ms₂ :=
    normal fld l (I.to_int (I.div l (Qden (ps_valuation ps₂)))) ps₂
  in
  let v₁ := Qnum (ps_valuation ms₁) in
  let v₂ := Qnum (ps_valuation ms₂) in
  match Z.sub v₂ v₁ with
  | Z0 =>
      {| ps_terms := series_add fld (ps_terms ms₁) (ps_terms ms₂);
         ps_valuation := Qmake v₁ l |}
  | Zpos n =>
      {| ps_terms :=
           series_add fld (ps_terms ms₁)
             (series_pad_left fld (Pos.to_nat n) (ps_terms ms₂));
         ps_valuation := Qmake v₁ l |}
  | Zneg n =>
      {| ps_terms :=
           series_add fld (series_pad_left fld (Pos.to_nat n) (ps_terms ms₁))
             (ps_terms ms₂);
         ps_valuation := Qmake v₂ l |}
  end.

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

Definition ps_mul α fld (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (Qden (ps_valuation ps₁)) (Qden (ps_valuation ps₂)) in
  let ms₁ :=
    normal fld l (I.to_int (I.div l (Qden (ps_valuation ps₁)))) ps₁
  in
  let ms₂ :=
    normal fld l (I.to_int (I.div l (Qden (ps_valuation ps₂)))) ps₂
  in
  {| ps_terms :=
       series_mul_term fld (ps_terms ms₁) (ps_terms ms₂);
     ps_valuation :=
       Qmake (Z.add (Qnum (ps_valuation ms₁)) (Qnum (ps_valuation ms₂))) l |}.

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
