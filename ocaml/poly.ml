(* $Id: poly.ml,v 1.24 2013-04-06 22:22:10 deraugla Exp $ *)

type polynomial α = { al : list α };

type old_monomial α = { coeff : α; power : int };

value p_of_op zero_coeff ml =
  loop [] 0 ml where rec loop rev_np deg ml =
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
        List.rev rev_ml ]
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

value pol_add add_coeff pol₁ pol₂ =
  loop [] pol₁.al pol₂.al where rec loop rev_al al₁ al₂ =
    match (al₁, al₂) with
    [ ([a₁ :: al₁], [a₂ :: al₂]) →
        let a = add_coeff a₁ a₂ in
        loop [a :: rev_al] al₁ al₂
    | ([], [a₂ :: al₂]) →
        {al = List.rev (List.rev_append al₂ [a₂ :: rev_al])}
    | ([a₁ :: al₁], []) →
        {al = List.rev (List.rev_append al₁ [a₁ :: rev_al])}
    | ([], []) →
        {al = List.rev rev_al} ]
;

value pol_mul zero_coeff add_coeff mul_coeff is_zero_coeff pol₁ pol₂ =
  let ml₁ = op_of_p is_zero_coeff pol₁ in
  let ml₂ = op_of_p is_zero_coeff pol₂ in
  let ml =
    List.fold_left
      (fun a m₁ →
         List.fold_left
           (fun a m₂ →
              let c = mul_coeff m₁.coeff m₂.coeff in
              let p = m₁.power + m₂.power in
              [{coeff = c; power = p} :: a])
           a ml₂)
      [] ml₁
  in
  let ml = List.sort (fun m₁ m₂ → compare m₁.power m₂.power) ml in
  p_of_op zero_coeff (merge_pow add_coeff is_zero_coeff ml)
;

value apply_poly zero_v add_v_coeff mul_v_x pol x =
  List.fold_right (fun c accu → add_v_coeff (mul_v_x accu x) c) pol.al
    zero_v
;
