(* $Id: puiseux_series.ml,v 1.22 2013-05-23 13:23:35 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Pnums;

type series α = [ Cons of α and Lazy.t (series α) | End ];

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
    | [m₁ :: ml₁] → Cons m₁ (loop ml₁) ]
  in
  {ps_monoms = loop ops.old_ps_mon}
;

value ps2ops ps =
  let rec loop ms =
    match ms with
    | Cons m₁ ms₁ → [m₁ :: loop (Lazy.force ms₁)]
    | End → []
    end
  in
  {old_ps_mon = loop ps.ps_monoms}
;

Definition ps_add α (add_coeff : α → α → α) (is_null_coeff : α → bool)
     (ps₁ : old_ps α) (ps₂ : old_ps α) :=
  let ps₁ := ops2ps ps₁ in
  let ps₂ := ops2ps ps₂ in
  let cofix loop₁ ms₁ ms₂ :=
    match Lazy.force ms₁ with
    | Cons c₁ s₁ =>
        let cofix loop₂ ms₂ :=
          match Lazy.force ms₂ with
          | Cons c₂ s₂ =>
              match Qcompare (power c₁) (power c₂) with
              | Eq =>
                  let c := add_coeff (coeff c₁) (coeff c₂) in
                  let m := {| coeff := c; power := power c₁ |} in
                  Cons m (loop₁ s₁ s₂)
              | Lt =>
                  Cons c₁ (loop₁ s₁ ms₂)
              | Gt =>
                  Cons c₂ (loop₂ s₂)
              end
          | End => Lazy.force ms₁
          end
        in
        loop₂ ms₂
    | End => Lazy.force ms₂
    end
  in
  {| ps_monoms := loop₁ (lazy (ps_monoms ps₁)) (lazy (ps_monoms ps₂)) |};

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
