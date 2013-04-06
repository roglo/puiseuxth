(* $Id: puiseux_series.ml,v 1.4 2013-04-06 22:51:30 deraugla Exp $ *)

open Pnums;

type monomial α = { coeff : α; power : Q.t };
type puiseux_series α = { ps_monoms : list (monomial α) };

value merge_pow₂ add_coeff is_null_coeff =
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

value ps_add add_coeff is_null_coeff ps₁ ps₂ =
  loop [] ps₁.ps_monoms ps₂.ps_monoms where rec loop rev_ml ml₁ ml₂ =
    match (ml₁, ml₂) with
    [ ([m₁ :: ml₁], [m₂ :: ml₂]) →
        let cmp = Q.compare m₁.power m₂.power in
        if cmp < 0 then
          loop [m₁ :: rev_ml] ml₁ [m₂ :: ml₂]
        else if cmp = 0 then
          let c = add_coeff m₁.coeff m₂.coeff in
          let rev_ml =
            if is_null_coeff c then rev_ml
            else [{coeff = c; power = m₁.power} :: rev_ml]
          in
          loop rev_ml ml₁ ml₂
        else
          loop [m₂ :: rev_ml] [m₁ :: ml₁] ml₂
    | ([], ml₂) → {ps_monoms = List.rev (List.rev_append ml₂ rev_ml)}
    | (ml₁, []) → {ps_monoms = List.rev (List.rev_append ml₁ rev_ml)} ]
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
  {ps_monoms = merge_pow₂ add_coeff is_null_coeff ml}
;
