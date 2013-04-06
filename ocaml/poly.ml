(* $Id: poly.ml,v 1.14 2013-04-06 09:40:51 deraugla Exp $ *)

type monomial α = { coeff : α; power : int };
type polynomial α = { monoms : list (monomial α) };

type new_polynomial α = { al : list α };
(*
value np_of_p pol =
;
*)

value merge_pow add_coeff is_null_coeff =
  loop [] where rec loop rev_list =
    fun
    [ [m₁ :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [m₂ :: rev_list₂] →
              if compare m₁.power m₂.power = 0 then
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

value pol_add add_coeff is_null_coeff pol₁ pol₂ =
  loop [] pol₁.monoms pol₂.monoms where rec loop rev_ml ml₁ ml₂ =
    match (ml₁, ml₂) with
    [ ([m₁ :: ml₁], [m₂ :: ml₂]) →
        let cmp = compare m₁.power m₂.power in
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

value pol_mul add_coeff mul_coeff is_null_coeff pol₁ pol₂ =
  let ml =
    List.fold_left
      (fun a m₁ →
         List.fold_left
           (fun a m₂ →
              let c = mul_coeff m₁.coeff m₂.coeff in
              let p = m₁.power + m₂.power in
              [{coeff = c; power = p} :: a])
           a pol₂.monoms)
      [] pol₁.monoms
  in
  let ml = List.sort (fun m₁ m₂ → compare m₁.power m₂.power) ml in
  {monoms = merge_pow add_coeff is_null_coeff ml}
;

value apply_poly zero_v add_v_coeff mul_v_x pol x =
  match List.rev pol.monoms with
  [ [m₁ :: _] as rml →
      loop zero_v m₁.power rml where rec loop v deg ml =
        match ml with
        [ [m :: ml] →
            if deg = m.power then
              loop (add_v_coeff (mul_v_x v x) m.coeff) (deg - 1) ml
            else if deg < m.power then
              invalid_arg "apply_poly polynom ill ordered"
            else
              loop (mul_v_x v x) (deg - 1) [m :: ml]
        | [] →
            if deg < 0 then v else loop (mul_v_x v x) (deg - 1) [] ]
  | [] →
      invalid_arg "apply_poly empty polynom" ]
;
