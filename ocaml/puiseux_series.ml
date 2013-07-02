(* $Id: puiseux_series.ml,v 1.193 2013-07-02 01:45:40 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Printf;

open Coq;
open Field;
open Pnums;
open Series;

Record puiseux_series α :=
  { ps_terms : series α;
    ps_valnum : Z;
    ps_comden : positive }.

value rec series_head is_zero n s =
  match s with
  | Term c t →
      if is_zero c then series_head is_zero (n + 1) (Lazy.force t)
      else Some (n, c)
  | End →
      None
  end;

Definition valuation α fld (ps : puiseux_series α) :=
  match series_head (is_zero fld) 0 (ps_terms ps) with
  | Some (n, c) =>
      Some (Qmake (Z.add (ps_valnum ps) (Z.of_nat n)) (ps_comden ps))
  | None =>
      None
  end.

Definition valuation_coeff α fld (ps : puiseux_series α) :=
  match series_head (is_zero fld) 0 (ps_terms ps) with
  | Some (_, c) => c
  | None => zero fld
  end.

value norm fld f x y = fld.ext.normalise (f x y);

CoFixpoint normal_terms α fld n cd₁ (s : series α) :=
  match s with
  | Term c ss =>
      match n with
      | O => Term c (normal_terms fld cd₁ cd₁ ss)
      | S n₁ => Term (zero fld) (normal_terms fld n₁ cd₁ s)
      end
  | End => End _
  end.

Definition normal α (fld : field α _) l cd ms :=
  {| ps_terms := normal_terms fld 0 (cd - 1) (ps_terms ms);
     ps_valnum := Z.mul (ps_valnum ms) (Z.of_nat cd);
     ps_comden := l |}.

(* ps_add *)

CoFixpoint series_add α (fld : field α _) s₁ s₂ :=
  match s₁ with
  | Term c₁ ss₁ =>
      match s₂ with
      | Term c₂ ss₂ => Term (add fld c₁ c₂) (series_add fld ss₁ ss₂)
      | End => s₁
      end
  | End => s₂
  end.

Fixpoint series_pad_left α (fld : field α _) n s :=
  match n with
  | O => s
  | S n₁ => Term (zero fld) (series_pad_left fld n₁ s)
  end.

Definition ps_add α fld (ms₁ ms₂ : puiseux_series α) :=
  let l := Plcm (ps_comden ms₁) (ps_comden ms₂) in
  let ms₁ := normal fld l (I.to_int (I.div l (ps_comden ms₁))) ms₁ in
  let ms₂ := normal fld l (I.to_int (I.div l (ps_comden ms₂))) ms₂ in
  let v₁ := ps_valnum ms₁ in
  let v₂ := ps_valnum ms₂ in
  if Z_lt_le_dec v₁ v₂ then
    {| ps_terms :=
         series_add fld
           (ps_terms ms₁)
           (series_pad_left fld (Z.to_nat (Z.sub v₂ v₁)) (ps_terms ms₂));
       ps_valnum := v₁;
       ps_comden := l |}
  else
    {| ps_terms :=
         series_add fld
           (series_pad_left fld (Z.to_nat (Z.sub v₁ v₂)) (ps_terms ms₁))
           (ps_terms ms₂);
       ps_valnum := v₂;
       ps_comden := l |}.

(* ps_mul *)

Fixpoint sum_mul_coeff α (fld : field α _) i ni₁ s₁ s₂ :=
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

Definition ps_mul_term α fld (s₁ s₂ : series α) :=
  let cofix mul_loop n₁ :=
    match sum_mul_coeff fld 0 n₁ s₁ s₂ with
    | Some c => Term c (mul_loop (S n₁))
    | None => End _
    end
  in
  mul_loop 1%nat.

Definition ps_mul α fld (ms₁ ms₂ : puiseux_series α) :=
  let l := Plcm (ps_comden ms₁) (ps_comden ms₂) in
  let ms₁ := normal fld l (I.to_int (I.div l (ps_comden ms₁))) ms₁ in
  let ms₂ := normal fld l (I.to_int (I.div l (ps_comden ms₂))) ms₂ in
  {| ps_terms := ps_mul_term fld (ps_terms ms₁) (ps_terms ms₂);
     ps_valnum := Z.add (ps_valnum ms₁) (ps_valnum ms₂);
     ps_comden := l |}.

(* *)

Record term α := { coeff : α; power : Q }.

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
