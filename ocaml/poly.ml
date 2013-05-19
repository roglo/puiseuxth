(* $Id: poly.ml,v 1.29 2013-05-19 01:02:11 deraugla Exp $ *)

type polynomial α = { ml : list α };
type old_monomial α = { old_coeff : α; old_power : int };

value merge_pow add_coeff is_zero_coeff =
  loop [] where rec loop rev_list =
    fun
    [ [m₁ :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [m₂ :: rev_list₂] →
              if compare m₁.old_power m₂.old_power = 0 then
                let c = add_coeff m₁.old_coeff m₂.old_coeff in
                if is_zero_coeff c then rev_list₂
                else [{old_coeff = c; old_power = m₁.old_power} :: rev_list₂]
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
  loop [] pol₁.ml pol₂.ml where rec loop rev_al al₁ al₂ =
    match (al₁, al₂) with
    [ ([a₁ :: al₁], [a₂ :: al₂]) →
        let a = add_coeff a₁ a₂ in
        loop [a :: rev_al] al₁ al₂
    | ([], [a₂ :: al₂]) →
        {ml = List.rev (List.rev_append al₂ [a₂ :: rev_al])}
    | ([a₁ :: al₁], []) →
        {ml = List.rev (List.rev_append al₁ [a₁ :: rev_al])}
    | ([], []) →
        {ml = List.rev rev_al} ]
;

value pol_mul zero_coeff add_coeff mul_coeff is_zero_coeff pol₁ pol₂ =
  let (ml, _) =
    List.fold_left
      (fun (a, deg₁) c₁ →
         let (a, _) =
           List.fold_left
             (fun (a, deg₂) c₂ →
                let c = mul_coeff c₁ c₂ in
                let p = deg₁ + deg₂ in
                ([{old_coeff = c; old_power = p} :: a],  deg₂ + 1))
              (a, 0) pol₂.ml
         in
         (a, deg₁ + 1))
      ([], 0) pol₁.ml
  in
  let ml = List.sort (fun m₁ m₂ → compare m₁.old_power m₂.old_power) ml in
  let ml = merge_pow add_coeff is_zero_coeff ml in
  loop [] 0 ml where rec loop rev_np deg ml =
    match ml with
    [ [m :: ml₁] →
        if m.old_power > deg then loop [zero_coeff :: rev_np] (deg + 1) ml
        else if m.old_power < deg then invalid_arg "pol_mul"
        else loop [m.old_coeff :: rev_np] (deg + 1) ml₁
    | [] →
        {ml = List.rev rev_np} ]
;

value apply_poly zero_v add_v_coeff mul_v_x pol x =
  List.fold_right (fun c accu → add_v_coeff (mul_v_x accu x) c) pol.ml
    zero_v
;
