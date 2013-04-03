(* $Id: poly.ml,v 1.1 2013-04-03 08:51:42 deraugla Exp $ *)

type monomial α β = { coeff : α; power : β };
type polynomial α β = { monoms : list (monomial α β) };

value merge_pow₄₂ zero_coeff add_coeff cmp_coeff cmp_power =
  loop [] where rec loop rev_list =
    fun
    [ [m₁ :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [m₂ :: rev_list₂] →
              if cmp_power m₁.power m₂.power = 0 then
                let c = add_coeff m₁.coeff m₂.coeff in
                if cmp_coeff c zero_coeff = 0 then rev_list₂
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

value pol_mul₄₂ zero_coeff add_coeff mul_coeff cmp_coeff add_power cmp_power m₁ m₂ =
  let ml =
    List.fold_left
      (fun a m₁ →
         List.fold_left
           (fun a m₂ →
              let c = mul_coeff m₁.coeff m₂.coeff in
              let p = add_power m₁.power m₂.power in
              [{coeff = c; power = p} :: a])
           a m₂.monoms)
      [] m₁.monoms
  in
  let ml = List.sort (fun m₁ m₂ → cmp_power m₁.power m₂.power) ml in
  merge_pow₄₂ zero_coeff add_coeff cmp_coeff cmp_power ml
;
