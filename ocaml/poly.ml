(* $Id: poly.ml,v 1.3 2013-04-03 09:30:47 deraugla Exp $ *)

type monomial α β = { coeff : α; power : β };
type polynomial α β = { monoms : list (monomial α β) };

value merge_pow add_coeff is_null_coeff cmp_power =
  loop [] where rec loop rev_list =
    fun
    [ [m₁ :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [m₂ :: rev_list₂] →
              if cmp_power m₁.power m₂.power = 0 then
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

value pol_add add_coeff is_null_coeff cmp_power pol₁ pol₂ =
  loop [] pol₁.monoms pol₂.monoms where rec loop rev_ml ml₁ ml₂ =
    match (ml₁, ml₂) with
    [ ([m₁ :: ml₁], [m₂ :: ml₂]) →
        let cmp = cmp_power m₁.power m₂.power in
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
    | ([], ml₂) → {monoms = List.rev (List.rev_append ml₂ rev_ml)}
    | (ml₁, []) → {monoms = List.rev (List.rev_append ml₁ rev_ml)} ]
;

value pol_mul add_coeff mul_coeff is_null_coeff add_power cmp_power
  (p₁ : polynomial α β) (p₂ : polynomial α β) : polynomial α β
=
  let ml =
    List.fold_left
      (fun a m₁ →
         List.fold_left
           (fun a m₂ →
              let c = mul_coeff m₁.coeff m₂.coeff in
              let p = add_power m₁.power m₂.power in
              [{coeff = c; power = p} :: a])
           a p₂.monoms)
      [] p₁.monoms
  in
  let ml = List.sort (fun m₁ m₂ → cmp_power m₁.power m₂.power) ml in
  {monoms = merge_pow add_coeff is_null_coeff cmp_power ml}
;

value horner zero_coeff add_coeff mul_coeff x pol =
  let rml = List.rev pol.monoms in
  loop zero_coeff (List.hd rml).power rml where rec loop a deg ml =
    match ml with
    [ [m :: ml] →
        if deg = m.power then
          loop (add_coeff (mul_coeff a x) m.coeff) (deg - 1) ml
        else if deg < m.power then
          invalid_arg "horner 1"
        else
          loop (mul_coeff a x) (deg - 1) [m :: ml]
    | [] →
        if deg = 0 || deg = -1 then a
        else if deg < 0 then invalid_arg "horner 2"
        else loop (mul_coeff a x) (deg - 1) [] ]
;
