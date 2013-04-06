(* $Id: puiseux_series.ml,v 1.2 2013-04-06 09:16:17 deraugla Exp $ *)

open Pnums;

type monomial₂ α = { coeff₂ : α; power₂ : Q.t };
type puiseux_series α = { monoms₂ : list (monomial₂ α) };

value merge_pow₂ add_coeff is_null_coeff =
  loop [] where rec loop rev_list =
    fun
    [ [m₁ :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [m₂ :: rev_list₂] →
              if Q.compare m₁.power₂ m₂.power₂ = 0 then
                let c = add_coeff m₁.coeff₂ m₂.coeff₂ in
                if is_null_coeff c then rev_list₂
                else [{coeff₂ = c; power₂ = m₁.power₂} :: rev_list₂]
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
  loop [] ps₁.monoms₂ ps₂.monoms₂ where rec loop rev_ml ml₁ ml₂ =
    match (ml₁, ml₂) with
    [ ([m₁ :: ml₁], [m₂ :: ml₂]) →
        let cmp = Q.compare m₁.power₂ m₂.power₂ in
        if cmp < 0 then
          loop [m₁ :: rev_ml] ml₁ [m₂ :: ml₂]
        else if cmp = 0 then
          let c = add_coeff m₁.coeff₂ m₂.coeff₂ in
          let rev_ml =
            if is_null_coeff c then rev_ml
            else [{coeff₂ = c; power₂ = m₁.power₂} :: rev_ml]
          in
          loop rev_ml ml₁ ml₂
        else
          loop [m₂ :: rev_ml] [m₁ :: ml₁] ml₂
    | ([], ml₂) → {monoms₂ = List.rev (List.rev_append ml₂ rev_ml)}
    | (ml₁, []) → {monoms₂ = List.rev (List.rev_append ml₁ rev_ml)} ]
;

value ps_mul add_coeff mul_coeff is_null_coeff ps₁ ps₂ =
  let ml =
    List.fold_left
      (fun a m₁ →
         List.fold_left
           (fun a m₂ →
              let c = mul_coeff m₁.coeff₂ m₂.coeff₂ in
              let p = Q.norm (Q.add m₁.power₂ m₂.power₂) in
              [{coeff₂ = c; power₂ = p} :: a])
           a ps₂.monoms₂)
      [] ps₁.monoms₂
  in
  let ml = List.sort (fun m₁ m₂ → Q.compare m₁.power₂ m₂.power₂) ml in
  {monoms₂ = merge_pow₂ add_coeff is_null_coeff ml}
;
