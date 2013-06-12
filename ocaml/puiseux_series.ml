(* $Id: puiseux_series.ml,v 1.129 2013-06-12 09:11:22 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Printf;
open Pnums;

type series α = [ Term of α and Lazy.t (series α) | End ];

Record term α := { coeff : α; power : Q };
Record puiseux_series α :=
  { ps_terms : series (term α);
    ps_comden : I.t };

type comparison = [ Eq | Lt | Gt ];

value mult = I.mul;
value qcompare q₁ q₂ =
  let c = Q.compare q₁ q₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
;
value bnat_compare i₁ i₂ =
  let c = I.compare i₁ i₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
;

CoFixpoint ps_add_loop (add_coeff : α → α → α) ms₁ ms₂ :=
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
  end;

Definition ps_add (add_coeff : α → α → α) (ps₁ : puiseux_series α)
    (ps₂ : puiseux_series α) :=
  {| ps_terms := ps_add_loop add_coeff (ps_terms ps₁) (ps_terms ps₂);
     ps_comden := I.lcm (ps_comden ps₁) (ps_comden ps₂) |};

Definition series_hd (s : series α) :=
  match s with
  | Term a _ => Some a
  | End => None
  end;

Definition series_tl (s : series α) : option (series α) :=
  match s with
  | Term _ t => Some t
  | End => None
  end;

Fixpoint series_nth_tl (n : nat) (s : series α) : option (series α) :=
  match n with
  | O => Some s
  | S m =>
      match series_tl s with
      | None => None
      | Some t => series_nth_tl m t
      end
  end;

Definition series_nth (n : nat) (s : series α) : option α :=
  match series_nth_tl n s with
  | None => None
  | Some t => series_hd t
  end;

CoFixpoint series_map (f : α → β) s :=
  match s with
  | Term a t => Term (f a) (series_map f t)
  | End => End _
  end;

(* ps_mul *)

Record fifo_elem α :=
  { fe_c : α; fe_t₁ : term α; fe_t₂ : term α;
    fe_ns₁ : series (term α); fe_ns₂ : series (term α) };

value qnat n = Q.of_i n;

Definition sum_int_powers comden (m₁ m₂ : term α) :=
  let q := Qred (Qmult (Qplus (power m₁) (power m₂)) (Qnat comden)) in
  Qnum q;

Fixpoint add_coeff_list α (add_coeff : α → α → α) c₁ fel₁ :=
  match fel₁ with
  | [] => c₁
  | [fe :: fel] => add_coeff c₁ (add_coeff_list add_coeff (fe_c fe) fel)
  end;

Fixpoint insert_ij (fe : fifo_elem α) fel :=
  match fel with
  | [] => [fe]
  | [fe₁ :: fel₁] =>
      match Qcompare (power (fe_t₁ fe)) (power (fe_t₁ fe₁)) with
      | Eq =>
          match Qcompare (power (fe_t₂ fe)) (power (fe_t₂ fe₁)) with
          | Eq => fel
          | Lt => [fe :: fel]
          | Gt => [fe₁ :: insert_ij fe fel₁]
          end
      | Lt => [fe :: fel]
      | Gt => [fe₁ :: insert_ij fe fel₁]
      end
  end;

Fixpoint insert_sum sum (fe : fifo_elem α) sl :=
  match sl with
  | [] => [(sum, [fe])]
  | [(sum₁, fel₁) :: l] =>
      match bnat_compare sum sum₁ with
      | Eq => [(sum₁, insert_ij fe fel₁) :: l]
      | Lt => [(sum, [fe]) :: sl]
      | Gt => [(sum₁, fel₁) :: insert_sum sum fe l]
      end
  end;

Definition insert_term mul_coeff comden s₁ s₂ sl :=
  match (s₁, s₂) with
  | (Term m₁ ns₁, Term m₂ ns₂) =>
      let ns₁ := Lazy.force ns₁ in
      let ns₂ := Lazy.force ns₂ in
      let c := mul_coeff (coeff m₁) (coeff m₂) in
      insert_sum (sum_int_powers comden m₁ m₂)
        {| fe_c := c; fe_t₁ := m₁; fe_t₂ := m₂;
           fe_ns₁ := ns₁; fe_ns₂ := ns₂ |}
        sl
  | _ => sl
  end;

Definition add_below α (mul_coeff : α → α → α) comden sl fel :=
  List.fold_left
    (λ sl₁ fe,
       insert_term mul_coeff comden (fe_ns₁ fe) (Term (fe_t₂ fe) (fe_ns₂ fe))
         sl₁)
    sl fel;

Definition add_right α (mul_coeff : α → α → α) comden sl fel :=
  List.fold_left
    (λ sl₂ fe,
       insert_term mul_coeff comden (Term (fe_t₁ fe) (fe_ns₁ fe))
         (fe_ns₂ fe) sl₂)
    sl fel;

CoFixpoint series_mul α add_coeff mul_coeff comden sum_fifo :
    series (term α) :=
  match sum_fifo with
  | [] => End _
  | [(sum, []) :: sl] => End _
  | [(sum, [fe₁ :: fel₁]) :: sl] =>
      let m :=
        let c := add_coeff_list add_coeff (fe_c fe₁) fel₁ in
        {| coeff := c; power := Qred (Q.make sum comden) |}
      in
      let sl₁ := add_below mul_coeff comden sl [fe₁ :: fel₁] in
      let sl₂ := add_right mul_coeff comden sl₁ [fe₁ :: fel₁] in
      Term m (series_mul add_coeff mul_coeff comden sl₂)
  end;

Definition ps_mul_term α add_coeff (mul_coeff : α → α → α) s₁ s₂ cd₁ cd₂ :=
  let comden := I.lcm cd₁ cd₂ in
  match s₁ with
  | Term m₁ ns₁ =>
      match s₂ with
      | Term m₂ ns₂ =>
          let c := mul_coeff (coeff m₁) (coeff m₂) in
          let fe :=
            {| fe_c := c; fe_t₁ := m₁; fe_t₂ := m₂;
               fe_ns₁ := ns₁; fe_ns₂ := ns₂ |}
          in
          series_mul add_coeff mul_coeff comden
            [(sum_int_powers comden m₁ m₂, [fe])]
      | End => End _
      end
  | End => End _
  end;

Definition ps_mul α add_coeff mul_coeff (ps₁ ps₂ : puiseux_series α) :=
  {| ps_terms :=
       ps_mul_term add_coeff mul_coeff (ps_terms ps₁) (ps_terms ps₂)
         (ps_comden ps₁) (ps_comden ps₂);
     ps_comden := mult (ps_comden ps₁) (ps_comden ps₂) |};

(**)

type old_ps α = { old_ps_mon : list (term α) };

value ops2ps ops =
  let terms =
    loop ops.old_ps_mon where rec loop =
      fun
      [ [] → End
      | [m₁ :: ml₁] → Term m₁ (loop ml₁) ]
  in
  let comden =
    loop ops.old_ps_mon where rec loop =
      fun
      [ [] → I.one
      | [m₁ :: ml₁] → I.lcm (Q.rden (power m₁)) (loop ml₁) ]
  in
  {ps_terms = terms; ps_comden = comden}
;

value ps2ops ps =
  let rec loop ms =
    match ms with
    | Term m₁ ms₁ → [m₁ :: loop (Lazy.force ms₁)]
    | End → []
    end
  in
  {old_ps_mon = loop ps.ps_terms}
;
