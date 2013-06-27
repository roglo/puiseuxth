(* $Id: puiseux_series.ml,v 1.178 2013-06-27 09:06:28 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Printf;

open Coq;
open Field;
open Pnums;
open Series;

Record term α := { coeff : α; power : Q }.

Record old_puiseux_series α :=
  { ps_terms : series (term α);
    ps_comden : positive }.

Record puiseux_series α :=
  { ms_terms : series α;
    ms_valnum : option Z;
    ms_comden : positive }.

value rec series_head_loop is_zero n s =
  match s with
  | Term m t →
      if is_zero m then series_head_loop is_zero (n + 1) (Lazy.force t)
      else (s, n)
  | End →
      (End, n)
  end;

value series_head is_zero s = fst (series_head_loop is_zero 0 s);

Definition valuation α fld ps :=
  match ms_valnum ps with
  | Some v =>
      let (t, n) := series_head_loop (is_zero fld) 0 (ms_terms ps) in
      match t with
      | Term _ _ => Some (Qred (Qmake (I.addi v n) (ms_comden ps)))
      | End => None
      end
  | None => None
  end.

Definition valuation_coeff α fld ps :=
  match series_head (is_zero fld) (ms_terms ps) with
  | Term c _ => c
  | End => zero fld
  end.

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

Definition old_valuation_coeff α fld (ps : old_puiseux_series α) :=
  match old_series_head (is_zero fld) (ps_terms ps) with
  | Term mx _ => coeff mx
  | End => zero fld
  end.

value norm fld f x y = fld.ext.normalise (f x y);

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
  {| ms_terms := normal_terms fld 0 (cd - 1) (ms_terms ms);
     ms_valnum :=
       match ms_valnum ms with
       | Some v => Some (Z.mul v (Z.of_nat cd))
       | None => None
       end;
     ms_comden := l |}.

(* ps_add *)

CoFixpoint ms_add_end α (fld : field α _) s₁ s₂ :=
  match s₁ with
  | Term c₁ ss₁ =>
      match s₂ with
      | Term c₂ ss₂ => Term (add fld c₁ c₂) (ms_add_end fld ss₁ ss₂)
      | End => s₁
      end
  | End => s₂
  end.

Fixpoint ms_add_terms α fld n (s₁ s₂ : series α) :=
  match n with
  | O => ms_add_end fld s₁ s₂
  | S n₁ =>
      match s₁ with
      | Term c₁ s => Term c₁ (ms_add_terms fld n₁ s s₂)
      | End => Term (zero fld) (ms_add_terms fld n₁ s₁ s₂)
      end
  end.

Definition ps_add α fld (ms₁ ms₂ : puiseux_series α) :=
  let l := Plcm (ms_comden ms₁) (ms_comden ms₂) in
  let ms₁ := normal fld l (I.to_int (I.div l (ms_comden ms₁))) ms₁ in
  let ms₂ := normal fld l (I.to_int (I.div l (ms_comden ms₂))) ms₂ in
  match ms_valnum ms₁ with
  | Some v₁ =>
      match ms_valnum ms₂ with
      | Some v₂ =>
          {| ms_terms :=
               if Z_lt_le_dec v₁ v₂ then
                 ms_add_terms fld (Z.to_nat (Z.sub v₂ v₁)) (ms_terms ms₁)
                   (ms_terms ms₂)
               else
                 ms_add_terms fld (Z.to_nat (Z.sub v₁ v₂)) (ms_terms ms₂)
                   (ms_terms ms₁);
             ms_valnum := Some (Z.min v₁ v₂);
             ms_comden := l |}
      | None => ms₁
      end
  | None => ms₂
  end.

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

Definition ms_mul_term α fld (s₁ s₂ : series α) :=
  let cofix mul_loop n₁ :=
    match sum_mul_coeff fld 0 n₁ s₁ s₂ with
    | Some c => Term c (mul_loop (S n₁))
    | None => End _
    end
  in
  mul_loop 1%nat.

Definition ps_mul α fld (ms₁ ms₂ : puiseux_series α) :=
  let l := Plcm (ms_comden ms₁) (ms_comden ms₂) in
  let ms₁ := normal fld l (I.to_int (I.div l (ms_comden ms₁))) ms₁ in
  let ms₂ := normal fld l (I.to_int (I.div l (ms_comden ms₂))) ms₂ in
  {| ms_terms :=
       ms_mul_term fld (ms_terms ms₁) (ms_terms ms₂);
     ms_valnum :=
       match ms_valnum ms₁ with
       | Some v₁ =>
           match ms_valnum ms₂ with
           | Some v₂ => Some (Z.add v₁ v₂)
           | None => None
           end
       | None => None
       end;
     ms_comden :=
       l |}.
