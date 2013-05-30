(* $Id: poly.ml,v 1.49 2013-05-30 20:10:53 deraugla Exp $ *)

#load "./pa_coq.cmo";

Record polynomial α := mkpol { al : list α; an : α };

value merge_pow add_coeff =
  loop [] where rec loop rev_list =
    fun
    [ [(c₁, p₁) :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [(c₂, p₂) :: rev_list₂] →
              if compare p₁ p₂ = 0 then
                let c = add_coeff c₁ c₂ in
                [(c, p₁) :: rev_list₂]
              else
                [(c₁, p₁) :: rev_list]
          | [] →
              [(c₁, p₁)] ]
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
      [(c, p) :: ml]
  | [c₂ :: cl₂] →
      let c = mul_coeff c₁ c₂ in
      let ml = [(c, p) :: ml] in
      combine_pol mul_coeff c₁ deg₁ (succ deg₂) ml cn cl₂
  end
;

value pol_mul zero_coeff add_coeff mul_coeff pol₁ pol₂ =
  let ml =
    loop [] 0 pol₁.al where rec loop ml deg₁ cl =
      match cl with
      | [] → combine_pol mul_coeff pol₁.an deg₁ 0 ml pol₂.an pol₂.al
      | [c₁ :: cl₁] →
           let ml = combine_pol mul_coeff c₁ deg₁ 0 ml pol₂.an pol₂.al in
           loop ml (succ deg₁) cl₁
      end
  in
  let ml = List.sort (fun (c₁, p₁) (c₂, p₂) → compare p₁ p₂) ml in
  let ml = merge_pow add_coeff ml in
  let rev_np =
    loop [] 0 ml where rec loop rev_np deg ml =
      match ml with
      | [(c, p) :: ml₁] →
          if p > deg then loop [zero_coeff :: rev_np] (deg + 1) ml
          else if p < deg then invalid_arg "pol_mul"
          else loop [c :: rev_np] (deg + 1) ml₁
      | [] →
          rev_np
      end
  in
  match rev_np with
  | [cn :: rev_cl] → {al = List.rev rev_cl; an = cn}
  | [] → assert False
  end
;

Definition apply_poly
    (zero_plus_v : β → α) (add_v_coeff : α → β → α) (mul_v_x : α → γ → α)
    (pol : polynomial β) (x : γ) :=
  List.fold_right (λ c accu, add_v_coeff (mul_v_x accu x) c)
    (al pol) (zero_plus_v (an pol));

type old_poly α = { ml : list α };
