(* $Id: puiseux_series.ml,v 1.90 2013-05-29 17:25:23 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Printf;
open Pnums;

type series α = [ Term of α and Lazy.t (series α) | End ];

Record ps_monomial α := { coeff : α; power : Q };
Record puiseux_series α :=
  { ps_terms : series (ps_monomial α);
    ps_comden : I.t };
Record old_ps α := { old_ps_mon : list (ps_monomial α) };

type comparison = [ Eq | Lt | Gt ];

value qcompare q₁ q₂ =
  let c = Q.compare q₁ q₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
;

value icompare i₁ i₂ =
  let c = I.compare i₁ i₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
;

value qof2nat = Q.make;

value merge_pow add_coeff is_null_coeff =
  loop [] where rec loop rev_list =
    fun
    [ [m₁ :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [m₂ :: rev_list₂] →
              if Q.compare m₁.power m₂.power = 0 then
                let c = add_coeff m₁.coeff m₂.coeff in
                if is_null_coeff c then rev_list₂
                else [{coeff = c; power = m₁.power} :: rev_list₂]
              else
                [m₁ :: rev_list]
          | [] →
              [m₁] ]
        in
        loop rev_list₁ ml₁
    | [] →
        List.rev rev_list ]
;

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

Definition ps_add (add_coeff : α → α → α) (ps₁ : old_ps α) (ps₂ : old_ps α) :=
  let ps₁ := ops2ps ps₁ in
  let ps₂ := ops2ps ps₂ in
  let cofix loop₁ ms₁ ms₂ :=
    match Lazy.force ms₁ with
    | Term c₁ s₁ =>
        let cofix loop₂ ms₂ :=
          match Lazy.force ms₂ with
          | Term c₂ s₂ =>
              match Qcompare (power c₁) (power c₂) with
              | Eq =>
                  let c := add_coeff (coeff c₁) (coeff c₂) in
                  let m := {| coeff := c; power := power c₁ |} in
                  Term m (loop₁ s₁ s₂)
              | Lt =>
                  Term c₁ (loop₁ s₁ ms₂)
              | Gt =>
                  Term c₂ (loop₂ s₂)
              end
          | End => Lazy.force ms₁
          end
        in
        loop₂ ms₂
    | End => Lazy.force ms₂
    end
  in
  {| ps_terms := loop₁ (lazy (ps_terms ps₁)) (lazy (ps_terms ps₂));
     ps_comden := I.lcm (ps_comden ps₁) (ps_comden ps₂) |};

(*
value old_ps_mul add_coeff mul_coeff is_null_coeff ps₁ ps₂ =
  let ml =
    List.fold_left
      (fun a m₁ →
         List.fold_left
           (fun a m₂ →
              let c = mul_coeff m₁.coeff m₂.coeff in
              let p = Q.norm (Q.add m₁.power m₂.power) in
              [{coeff = c; power = p} :: a])
           a ps₂.old_ps_mon)
      [] ps₁.old_ps_mon
  in
  let ml = List.sort (fun m₁ m₂ → Q.compare m₁.power m₂.power) ml in
  {old_ps_mon = merge_pow add_coeff is_null_coeff ml}
;
value ps_mul add_coeff mul_coeff is_null_coeff ops₁ ops₂ =
  old_ps_mul add_coeff mul_coeff is_null_coeff ops₁ ops₂
;
*)

Definition ser_hd (s : series α) :=
  match s with
  | Term a _ => Some a
  | End => None
  end;

Definition ser_tl (s : series α) : option (series α) :=
  match s with
  | Term _ t => Some (Lazy.force t)
  | End => None
  end;

Fixpoint ser_nth_tl (n : nat) (s : series α) : option (series α) :=
  match n with
  | O => Some s
  | S m =>
      match ser_tl s with
      | None => None
      | Some t => ser_nth_tl m t
      end
  end;

Definition ser_nth (n : nat) (s : series α) : option α :=
  match ser_nth_tl n s with
  | None => None
  | Some t => ser_hd t
  end;

(* ps_mul *)

Record fifo_elem α :=
  { fe_i : nat;
    fe_j : nat;
    fe_c : α;
    fe_p : Q;
    fe_s₁ : series (ps_monomial α);
    fe_s₂ : series (ps_monomial α) };

value rec insert_ij fe fel =
  match fel with
  | [] → [fe]
  | [fe₁ :: fel₁] →
      if fe_i fe < fe_i fe₁ then [fe :: fel]
      else if fe_i fe > fe_i fe₁ then [fe₁ :: insert_ij fe fel₁]
      else if fe_j fe < fe_j fe₁ then [fe :: fel]
      else if fe_j fe > fe_j fe₁ then [fe₁ :: insert_ij fe fel₁]
      else fel
  end
;

value rec insert_sum sum fe sl =
  match sl with
  | [] → [(sum, [fe])]
  | [(sum₁, fel₁) :: l] →
      match icompare sum sum₁ with
      | Eq → [(sum₁, insert_ij fe fel₁) :: l]
      | Lt → [(sum, [fe]) :: sl]
      | Gt → [(sum₁, fel₁) :: insert_sum sum fe l]
      end
  end
;        

value sum_int_powers comden m₁ m₂ =
  let p₁c = Qnum (Q.norm (Q.muli (power m₁) comden)) in
  let p₂c = Qnum (Q.norm (Q.muli (power m₂) comden)) in
  I.add p₁c p₂c
;

value insert_point mul_coeff comden i j s₁ s₂ sl =
  match (s₁, s₂) with
  | (Term m₁ _, Term m₂ _) →
      let c = mul_coeff (coeff m₁) (coeff m₂) in
      let p = Q.norm (Qplus (power m₁) (power m₂)) in
      insert_sum (sum_int_powers comden m₁ m₂)
        {fe_i = i; fe_j = j; fe_c = c; fe_p = p; fe_s₁ = s₁; fe_s₂ = s₂} sl
  | _ → sl
  end
;

value add_coeff_list add_coeff fe₁ fel₁ =
  loop (fe_c fe₁) fel₁ where rec loop c₁ fel₁ =
    match fel₁ with
    | [] → c₁
    | [fe :: fel] → add_coeff c₁ (loop (fe_c fe) fel)
    end
;

value ps_mul add_coeff mul_coeff ps₁ ps₂ =
  let s₁ = ps_terms ps₁ in
  let s₂ = ps_terms ps₂ in
  let comden = I.mul (ps_comden ps₁) (ps_comden ps₂) in
  let t =
    let rec series_mul sum_fifo =
      match sum_fifo with
      | [] → End
      | [(sum, []) :: sl] → End
      | [(sum, [fe₁ :: fel₁]) :: sl] →
          let m =
            let c = add_coeff_list add_coeff fe₁ fel₁ in
            {coeff = c; power = fe_p fe₁}
          in
          let sl =
            List.fold_left
              (fun sl fe →
                 match fe_s₁ fe with
                 | Term _ ls₁ →
                     insert_point mul_coeff comden (S (fe_i fe)) (fe_j fe)
                       (Lazy.force ls₁) (fe_s₂ fe) sl
                 | End → sl
                 end)
              sl [fe₁ :: fel₁]
          in
          let sl =
            List.fold_left
              (fun sl fe →
                 match fe_s₂ fe with
                 | Term _ ls₂ →
                     insert_point mul_coeff comden (fe_i fe) (S (fe_j fe))
                       (fe_s₁ fe) (Lazy.force ls₂) sl
                 | End → sl
                 end)
              sl [fe₁ :: fel₁]
          in
          Term m (series_mul sl)
      end
    in
    match s₁ with
    | Term m₁ _ →
        match s₂ with
        | Term m₂ _ →
            let c = mul_coeff (coeff m₁) (coeff m₂) in
            let p = Q.norm (Qplus (power m₁) (power m₂)) in
            let fe =
              {fe_i = 0; fe_j = 0; fe_c = c; fe_p = p; fe_s₁ = s₁; fe_s₂ = s₂}
            in
            series_mul [(sum_int_powers comden m₁ m₂, [fe])]
        | End → End
        end
    | End → End
    end
  in
  {ps_terms = t; ps_comden = comden}
;

value ps_mul add_coeff mul_coeff is_null_coeff ops₁ ops₂ =
  ps2ops (ps_mul add_coeff mul_coeff (ops2ps ops₁) (ops2ps ops₂))
;
