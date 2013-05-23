(* $Id: puiseux_series.ml,v 1.26 2013-05-23 23:51:40 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Pnums;

type series α = [ Term of α and Lazy.t (series α) | End ];

Record ps_monomial α := { coeff : α; power : Q };
Record puiseux_series α := { ps_monoms : series (ps_monomial α) };
Record old_ps α := { old_ps_mon : list (ps_monomial α) };

type comparison = [ Eq | Lt | Gt ];

value qcompare q₁ q₂ =
  let c = Q.compare q₁ q₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
;

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
  let rec loop =
    fun
    [ [] → End
    | [m₁ :: ml₁] → Term m₁ (loop ml₁) ]
  in
  {ps_monoms = loop ops.old_ps_mon}
;

value ps2ops ps =
  let rec loop ms =
    match ms with
    | Term m₁ ms₁ → [m₁ :: loop (Lazy.force ms₁)]
    | End → []
    end
  in
  {old_ps_mon = loop ps.ps_monoms}
;

Definition ps_add (add_coeff : α → α → α) (is_null_coeff : α → bool)
     (ps₁ : old_ps α) (ps₂ : old_ps α) :=
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
  {| ps_monoms := loop₁ (lazy (ps_monoms ps₁)) (lazy (ps_monoms ps₂)) |};

Definition ser_hd α (s : series α) :=
  match s with
  | Term a _ => Some a
  | End => None
  end;

Definition ser_tl α (s : series α) : option (series α) :=
  match s with
  | Term _ t => Some (Lazy.force t)
  | End => None
  end;

Fixpoint ser_nth_tl α (n : nat) (s : series α) : option (series α) :=
  match n with
  | O => Some s
  | S m =>
      match ser_tl α s with
      | None => None
      | Some t => ser_nth_tl α m t
      end
  end;

Definition ser_nth α (n : nat) (s : series α) : option α :=
  match ser_nth_tl α n s with
  | None => None
  | Some t => ser_hd α t
  end;

(*
value ps_mul add_coeff mul_coeff is_null_coeff ps₁ ps₂ =
  let ml =
    match (ps₁.old_ps_mon, ps₂.old_ps_mon) with
    | ([], _) → []
    | (_, []) → []
    | ([m₁ :: ml₁], [m₂ :: ml₂]) →
        let c = mul_coeff (coeff m₁) (coeff m₂) in
        let p = Q.norm (Q.add m₁.power m₂.power) in
        let m = {coeff = c; power = p} in
        let rest = ml₁ in
        [m :: rest]
    end
  in
  {old_ps_mon = ml}
;
*)

value ps_mul add_coeff mul_coeff is_null_coeff ps₁ ps₂ =
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
