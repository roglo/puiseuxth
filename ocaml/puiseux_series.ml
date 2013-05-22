(* $Id: puiseux_series.ml,v 1.7 2013-05-22 15:34:55 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Pnums;

Record ps_monomial α := { coeff : α; power : Q };
Record puiseux_series α := { ps_monoms : list (ps_monomial α) };

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

Definition ps_add add_coeff is_null_coeff ps₁ ps₂ :=
  let fix loop ml₁ ml₂ :=
    match (ml₁, ml₂) with
    | ([], ml₂) => ml₂
    | (ml₁, []) => ml₁
    | ([m₁ :: ml₁], [m₂ :: ml₂]) =>
        match Qcompare (power m₁) (power m₂) with
        | Eq =>
            let c := add_coeff (coeff m₁) (coeff m₂) in
            if is_null_coeff c then loop ml₁ ml₂
            else [{| coeff := c; power := power m₁ |} :: loop ml₁ ml₂]
        | Lt =>
            [m₁ :: loop ml₁ [m₂ :: ml₂]]
        | Gt =>
            [m₂ :: loop [m₁ :: ml₁] ml₂]
        end
    end
  in
  {ps_monoms = loop (ps_monoms ps₁) (ps_monoms ps₂)}
;

value ps_mul add_coeff mul_coeff is_null_coeff ps₁ ps₂ =
  let ml =
    List.fold_left
      (fun a m₁ →
         List.fold_left
           (fun a m₂ →
              let c = mul_coeff m₁.coeff m₂.coeff in
              let p = Q.norm (Q.add m₁.power m₂.power) in
              [{coeff = c; power = p} :: a])
           a ps₂.ps_monoms)
      [] ps₁.ps_monoms
  in
  let ml = List.sort (fun m₁ m₂ → Q.compare m₁.power m₂.power) ml in
  {ps_monoms = merge_pow add_coeff is_null_coeff ml}
;
