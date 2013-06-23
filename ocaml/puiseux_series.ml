(* $Id: puiseux_series.ml,v 1.153 2013-06-23 17:34:52 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Printf;

open Coq;
open Field;
open Pnums;
open Series;

Record term α := { coeff : α; power : Q };
Record puiseux_series α :=
  { ps_terms : series (term α);
    ps_comden : I.t };

value mult = I.mul;

value rec series_head is_zero s =
  match s with
  | Term m t →
      if is_zero m.coeff then series_head is_zero (Lazy.force t) else s
  | End →
      End
  end;

Definition valuation α fld (ps : puiseux_series α) :=
  match series_head (is_zero fld) (ps_terms ps) with
  | Term mx _ => Some (power mx)
  | End => None
  end.

Definition valuation_coeff α fld (ps : puiseux_series α) :=
  match series_head (is_zero fld) (ps_terms ps) with
  | Term mx _ => coeff mx
  | End => zero fld
  end.

CoFixpoint ps_add_loop α (add_coeff : α → α → α) ms₁ ms₂ :=
  match ms₁ with
  | Term c₁ s₁ =>
      match ms₂ with
      | Term c₂ s₂ =>
          match Qcompare (power c₁) (power c₂) with
          | Eq =>
              let c := add_coeff (coeff c₁) (coeff c₂) in
              let m := {| coeff := c; power := power c₁ |} in
              Term m (ps_add_loop add_coeff s₁ s₂)
          | Lt =>
              Term c₁ (ps_add_loop add_coeff s₁ ms₂)
          | Gt =>
              Term c₂ (ps_add_loop add_coeff ms₁ s₂)
          end
      | End => ms₁
      end
  | End => ms₂
  end.

Definition ps_add α (add_coeff : α → α → α) (ps₁ : puiseux_series α)
    (ps₂ : puiseux_series α) :=
  {| ps_terms := ps_add_loop add_coeff (ps_terms ps₁) (ps_terms ps₂);
     ps_comden := Plcm (ps_comden ps₁) (ps_comden ps₂) |}.

(* ps_mul *)

Record fifo_elem α :=
  { fe_t₁ : term α; fe_t₂ : term α;
    fe_s₁ : series (term α); fe_s₂ : series (term α) }.

Fixpoint add_coeff_list α (add_coeff : α → α → α) (mul_coeff : α → α → α)
    c₁ fel₁ :=
  match fel₁ with
  | [] =>
      c₁
  | [fe … fel] =>
      let c := mul_coeff (coeff (fe_t₁ fe)) (coeff (fe_t₂ fe)) in
      add_coeff c₁ (add_coeff_list add_coeff mul_coeff c fel)
  end.

Fixpoint insert_elem α (fe : fifo_elem α) fel :=
  match fel with
  | [] => [fe]
  | [fe₁ … fel₁] =>
      match Qcompare (power (fe_t₁ fe)) (power (fe_t₁ fe₁)) with
      | Eq =>
          match Qcompare (power (fe_t₂ fe)) (power (fe_t₂ fe₁)) with
          | Eq => fel
          | Lt => [fe … fel]
          | Gt => [fe₁ … insert_elem fe fel₁]
          end
      | Lt => [fe … fel]
      | Gt => [fe₁ … insert_elem fe fel₁]
      end
  end.

Fixpoint insert_sum α sum (fe : fifo_elem α) sl :=
  match sl with
  | [] => [(sum, [fe])]
  | [(sum₁, fel₁) … l] =>
      match Qcompare sum sum₁ with
      | Eq => [(sum₁, insert_elem fe fel₁) … l]
      | Lt => [(sum, [fe]) … sl]
      | Gt => [(sum₁, fel₁) … insert_sum sum fe l]
      end
  end.

Definition add_below α (mul_coeff : α → α → α) sl fel :=
  List.fold_left
    (λ sl₁ fe,
       match (fe_s₁ fe : series (term α)) with
       | Term t₁ s₁ =>
            insert_sum (Qplus (power t₁) (power (fe_t₂ fe)))
              {| fe_t₁ := t₁; fe_t₂ := fe_t₂ fe;
                 fe_s₁ := s₁; fe_s₂ := fe_s₂ fe |}
              sl₁
       | End => sl₁
       end)
    sl fel.

Definition add_right α (mul_coeff : α → α → α) sl fel :=
  List.fold_left
    (λ sl₂ fe,
       match (fe_s₂ fe : series (term α)) with
       | Term t₂ s₂ =>
            insert_sum (Qplus (power (fe_t₁ fe)) (power t₂))
              {| fe_t₁ := fe_t₁ fe; fe_t₂ := t₂;
                 fe_s₁ := fe_s₁ fe; fe_s₂ := s₂ |}
              sl₂
       | End => sl₂
       end)
    sl fel.

CoFixpoint ps_mul_loop α add_coeff mul_coeff sum_fifo :
    series (term α) :=
  match sum_fifo with
  | [] => End _
  | [(sum, []) … sl] => End _
  | [(sum, [fe₁ … fel₁]) … sl] =>
      let m :=
        let c₁ := mul_coeff (coeff (fe_t₁ fe₁)) (coeff (fe_t₂ fe₁)) in
        let c := add_coeff_list add_coeff mul_coeff c₁ fel₁ in
        {| coeff := c; power := Q.norm sum |}
      in
      let sl₁ := add_below mul_coeff sl [fe₁ … fel₁] in
      let sl₂ := add_right mul_coeff sl₁ [fe₁ … fel₁] in
      Term m (ps_mul_loop add_coeff mul_coeff sl₂)
  end.

Definition ps_mul_term α add_coeff (mul_coeff : α → α → α) s₁ s₂ :=
  match s₁ with
  | Term t₁ ns₁ =>
      match s₂ with
      | Term t₂ ns₂ =>
          let fe :=
            {| fe_t₁ := t₁; fe_t₂ := t₂; fe_s₁ := ns₁; fe_s₂ := ns₂ |}
          in
          ps_mul_loop add_coeff mul_coeff
            [(Qplus (power t₁) (power t₂), [fe])]
      | End => End _
      end
  | End => End _
  end.

(* other version *)

Fixpoint sum_mul_coeff α add_coeff (mul_coeff : α → α → α) i ni₁ s₁ s₂ :=
  match ni₁ with
  | O => None
  | S ni =>
      match sum_mul_coeff add_coeff mul_coeff (S i) ni s₁ s₂ with
      | Some c =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (add_coeff (mul_coeff c₁ c₂) c)
              | None => Some (add_coeff c₁ c)
              end
          | None =>
              match series_nth ni s₂ with
              | Some c₂ => Some (add_coeff c₂ c)
              | None => Some c
              end
          end
      | None =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (mul_coeff c₁ c₂)
              | None => Some c₁
              end
          | None =>
              match series_nth ni s₂ with
              | Some c₂ => Some c₂
              | None => None
              end
          end
      end
  end.

Definition ms_mul_term α add_coeff mul_coeff (s₁ s₂ : series α) :=
  let cofix mul_loop n₁ :=
    match sum_mul_coeff add_coeff mul_coeff 0 n₁ s₁ s₂ with
    | Some c => Term c (mul_loop (S n₁))
    | None => End _
    end
  in
  mul_loop 1%nat.

Record math_puiseux_series α :=
  { ms_terms : series α;
    ms_valnum : option Z;
    ms_comden : positive }.

Definition ms_mul α add_coeff mul_coeff (ms₁ ms₂ : math_puiseux_series α) :=
  {| ms_terms :=
       ms_mul_term add_coeff mul_coeff (ms_terms ms₁) (ms_terms ms₂);
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
       Pos.mul (ms_comden ms₁) (ms_comden ms₂) |}.

CoFixpoint term_of_ms α cd p (s : series α) :=
  match s with
  | Term c ns =>
      Term {| coeff := c; power := Qmake p cd |} (term_of_ms cd (Z.succ p) ns)
  | End =>
      End _
  end.

Definition ps_terms_of_ms α (ms : math_puiseux_series α) : series (term α) :=
  match ms_valnum ms with
  | Some v => term_of_ms (ms_comden ms) v (ms_terms ms)
  | None => End _
  end.

CoFixpoint complete α (zero : α) (ps : puiseux_series α) p s :=
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

Definition ms_terms_of_ps α zero is_zero (ps : puiseux_series α) :=
  let cofix loop s :=
    match s with
    | Term t ns => Term (coeff t) (loop (complete zero ps (power t) ns))
    | End => End _
    end
  in
  loop (series_head is_zero (ps_terms ps)).

Definition ps_of_ms α (ms : math_puiseux_series α) :=
  {| ps_terms := ps_terms_of_ms ms;
     ps_comden := ms_comden ms |}.

Definition ms_of_ps α fld (ps : puiseux_series α) :=
  {| ms_terms :=
       ms_terms_of_ps (zero fld) (is_zero fld) ps;
     ms_valnum :=
       match valuation fld ps with
       | Some v =>
(*
let _ := printf "  val %s comden %s\n%!" (Q.to_string v) (I.ts (ps_comden ps)) in
*)
           Some (Qnum (Qred (Qmult v (inject_Z (Zpos (ps_comden ps))))))
       | None =>
           None
       end;
     ms_comden :=
       ps_comden ps |}.

value trace_ps zero is_zero ps =
  loop (ps_terms ps) where rec loop s =
    match s with
    | Term t s₁ → do {
        printf "Term {c=%s;p=%s} %!" (C.to_string False (Obj.magic t.coeff))
          (Q.to_string t.power);
        loop (Lazy.force s₁)
      }
    | End → printf "End\n%!"
    end
;

(**)
Definition ps_mul α fld (ps₁ ps₂ : puiseux_series α) :=
  ps_of_ms (ms_mul (add fld) (mul fld) (ms_of_ps fld ps₁) (ms_of_ps fld ps₂)).

(* *)

Definition ps_mul α zero is_zero add_coeff mul_coeff
    (ps₁ ps₂ : puiseux_series α) :=
(*
let _ := printf "changing:\n  %!" in
let _ := trace_ps zero is_zero ps₁ in
  let ps₁ := ps_of_ms (ms_of_ps zero is_zero ps₁) in
let _ := printf "  %!" in
let _ := trace_ps zero is_zero ps₁ in
  let ps₂ := ps_of_ms (ms_of_ps zero is_zero ps₂) in
*)
  {| ps_terms :=
       ps_mul_term add_coeff mul_coeff (ps_terms ps₁) (ps_terms ps₂);
     ps_comden :=
       I.mul (ps_comden ps₁) (ps_comden ps₂) |}.
(**)

(**)

type old_ps α = { old_ps_mon : list (term α) };

value ops2ps ops =
  let terms =
    loop ops.old_ps_mon where rec loop =
      fun
      [ [] → End
      | [m₁ … ml₁] → Term m₁ (loop ml₁) ]
  in
  let comden =
    loop ops.old_ps_mon where rec loop =
      fun
      [ [] → I.one
      | [m₁ … ml₁] → I.lcm (Q.rden (power m₁)) (loop ml₁) ]
  in
  {ps_terms = terms; ps_comden = comden}
;

value ps2ops ps =
  let rec loop lim ms =
    if lim = 0 then []
    else
      match ms with
      | Term m₁ ms₁ → [m₁ … loop (lim - 1) (Lazy.force ms₁)]
      | End → []
      end
  in
  {old_ps_mon = loop (-1) ps.ps_terms}
;
