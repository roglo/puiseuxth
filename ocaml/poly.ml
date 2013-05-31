(* $Id: poly.ml,v 1.51 2013-05-31 08:48:24 deraugla Exp $ *)

#load "./pa_coq.cmo";

Record polynomial α := mkpol { al : list α; an : α };

type comparison = [ Eq | Lt | Gt ];

value nat_compare i₁ i₂ =
  let c = compare i₁ i₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
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

Fixpoint insert_pol_term add_coeff c₁ p₁ ml :=
  match ml with
  | [] => [(c₁, p₁)]
  | [(c₂, p₂) :: ml₂] =>
      match nat_compare p₁ p₂ with
      | Eq => [(add_coeff c₁ c₂, p₂) :: ml₂]
      | Lt => [(c₁, p₁) :: ml]
      | Gt => [(c₂, p₂) :: insert_pol_term add_coeff c₁ p₁ ml₂]
      end
  end;

value rec combine_pol add_coeff mul_coeff c₁ pow₁ pow₂ ml cn cl =
  let p = pow₁ + pow₂ in
  match cl with
  | [] →
      let c = mul_coeff c₁ cn in
      insert_pol_term add_coeff c p ml
  | [c₂ :: cl₂] →
      let c = mul_coeff c₁ c₂ in
      let ml = insert_pol_term add_coeff c p ml in
      combine_pol add_coeff mul_coeff c₁ pow₁ (succ pow₂) ml cn cl₂
  end
;

value pol_mul zero_coeff add_coeff mul_coeff pol₁ pol₂ =
  let ml =
    loop [] 0 pol₁.al where rec loop ml pow₁ cl =
      match cl with
      | [] → combine_pol add_coeff mul_coeff pol₁.an pow₁ 0 ml pol₂.an pol₂.al
      | [c₁ :: cl₁] →
           let ml =
             combine_pol add_coeff mul_coeff c₁ pow₁ 0 ml pol₂.an pol₂.al
           in
           loop ml (succ pow₁) cl₁
      end
  in
  let rev_np =
    loop [] 0 ml where rec loop rev_np pow ml =
      match ml with
      | [(c, p) :: ml₁] →
          if p > pow then loop [zero_coeff :: rev_np] (pow + 1) ml
          else if p < pow then invalid_arg "pol_mul"
          else loop [c :: rev_np] (pow + 1) ml₁
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
