(* $Id: poly.ml,v 1.45 2013-05-30 18:59:30 deraugla Exp $ *)

#load "./pa_coq.cmo";

Record polynomial α := mkpol { al : list α; an : α };

type old_poly α = { ml : list α };
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

Definition pol_add (add_coeff : α → α → α) pol₁ pol₂ :=
  let fix loop al₁ al₂ :=
    match (al₁, al₂) with
    | ([], []) => mkpol () [] (add_coeff (an pol₁) (an pol₂))
    | ([], [a₂ :: bl₂]) =>
        mkpol () [add_coeff (an pol₁) a₂ :: bl₂] (an pol₂)
    | ([a₁ :: bl₁], []) =>
        mkpol () [add_coeff a₁ (an pol₂) :: bl₁] (an pol₁)
    | ([a₁ :: bl₁], [a₂ :: bl₂]) =>
        let r := loop bl₁ bl₂ in
        mkpol () [add_coeff a₁ a₂ :: al r] (an r)
    end
  in
  loop (al pol₁) (al pol₂);

value rec combine_pol mul_coeff c₁ deg₁ deg₂ ml cn cl =
  let p = deg₁ + deg₂ in
  match cl with
  | [] →
      let c = mul_coeff c₁ cn in
      [{old_coeff = c; old_power = p} :: ml]
  | [c₂ :: cl₂] →
      let c = mul_coeff c₁ c₂ in
      let ml = [{old_coeff = c; old_power = p} :: ml] in
      combine_pol mul_coeff c₁ deg₁ (succ deg₂) ml cn cl₂
  end
;

value pol_mul zero_coeff add_coeff mul_coeff is_zero_coeff pol₁ pol₂ =
  let ml =
    loop [] 0 pol₁.al where rec loop ml deg₁ cl =
      match cl with
      | [] → combine_pol mul_coeff pol₁.an deg₁ 0 ml pol₂.an pol₂.al
      | [c₁ :: cl₁] →
           let ml = combine_pol mul_coeff c₁ deg₁ 0 ml pol₂.an pol₂.al in
           loop ml (succ deg₁) cl₁
      end
  in
  let ml = List.sort (fun m₁ m₂ → compare m₁.old_power m₂.old_power) ml in
  let ml = merge_pow add_coeff is_zero_coeff ml in
  let rev_np =
    loop [] 0 ml where rec loop rev_np deg ml =
      match ml with
      | [m :: ml₁] →
          if m.old_power > deg then loop [zero_coeff :: rev_np] (deg + 1) ml
          else if m.old_power < deg then invalid_arg "pol_mul"
          else loop [m.old_coeff :: rev_np] (deg + 1) ml₁
      | [] →
          rev_np
      end
  in
  match rev_np with
  | [cn :: rev_cl] → {al = List.rev rev_cl; an = cn}
  | [] → assert False
  end
;

open Field;

value p2op fld p =
  match p.al with
  | [] → if fld.eq p.an fld.zero then {ml = []} else {ml = [an p]}
  | _ → {ml = p.al @ [p.an]}
  end
;
value op2p fld p =
  match List.rev p.ml with
  | [] → {al = []; an = fld.zero}
  | [m :: ml] → {al = List.rev ml; an = m}
  end
;

Definition apply_poly
    (zero_plus_v : β → α) (add_v_coeff : α → β → α) (mul_v_x : α → γ → α)
    (pol : polynomial β) (x : γ) :=
  List.fold_right (λ c accu, add_v_coeff (mul_v_x accu x) c)
    (al pol) (zero_plus_v (an pol));
