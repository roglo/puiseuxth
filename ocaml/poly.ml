(* $Id: poly.ml,v 1.18 2013-04-06 11:17:39 deraugla Exp $ *)

type monomial α = { coeff : α; power : int };
type old_polynomial α = { monoms : list (monomial α) };

type polynomial α = { al : list α };
value p_of_op zero_coeff pol =
  loop [] 0 pol.monoms where rec loop rev_np deg ml =
    match ml with
    [ [m :: ml₁] →
        if m.power > deg then loop [zero_coeff :: rev_np] (deg + 1) ml
        else if m.power < deg then invalid_arg "p_of_op"
        else loop [m.coeff :: rev_np] (deg + 1) ml₁
    | [] →
        {al = List.rev rev_np} ]
;
value op_of_p is_zero_coeff pol =
  loop [] 0 pol.al where rec loop rev_ml deg cl =
    match cl with
    [ [c :: cl₁] →
        if is_zero_coeff c then loop rev_ml (deg + 1) cl₁
        else loop [{coeff = c; power = deg} :: rev_ml] (deg + 1) cl₁
    | [] →
        {monoms = List.rev rev_ml} ]
;

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

value pol_add zero_coeff add_coeff is_zero_coeff pol₁ pol₂ =
  let pol₁ = op_of_p is_zero_coeff pol₁ in
  let pol₂ = op_of_p is_zero_coeff pol₂ in
  loop [] pol₁.monoms pol₂.monoms where rec loop rev_ml ml₁ ml₂ =
    match (ml₁, ml₂) with
    [ ([m₁ :: ml₁], [m₂ :: ml₂]) →
        let cmp = compare m₁.power m₂.power in
        if cmp < 0 then
          loop [m₁ :: rev_ml] ml₁ [m₂ :: ml₂]
        else if cmp = 0 then
          let c = add_coeff m₁.coeff m₂.coeff in
          let rev_ml =
            if is_zero_coeff c then rev_ml
            else [{coeff = c; power = m₁.power} :: rev_ml]
          in
          loop rev_ml ml₁ ml₂
        else
          loop [m₂ :: rev_ml] [m₁ :: ml₁] ml₂
    | ([], ml₂) →
        p_of_op zero_coeff {monoms = List.rev (List.rev_append ml₂ rev_ml)}
    | (ml₁, []) →
        p_of_op zero_coeff {monoms = List.rev (List.rev_append ml₁ rev_ml)} ]
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

value apply_poly zero_v is_zero_v add_v_coeff mul_v_x pol x =
  let pol = op_of_p is_zero_v pol in
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
