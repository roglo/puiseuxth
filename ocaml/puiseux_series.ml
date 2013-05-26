(* $Id: puiseux_series.ml,v 1.45 2013-05-26 23:19:52 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Printf;
open Pnums;

type series α = [ Term of α and Lazy.t (series α) | End ];

Record ps_monomial α := { coeff : α; power : Q };
Record puiseux_series α :=
  { ps_terms : series (ps_monomial α);
    ps_comden : I.t };
Record old_ps α := { old_ps_mon : list (ps_monomial α) };

type comparison = [ Eq | Lt | Gt ];

value qcompare q₁ q₂ =
  let c = Q.compare q₁ q₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
;

value merge_pow add_coeff is_null_coeff =
  loop [] where rec loop rev_list =
    fun
    [ [m₁ :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [m₂ :: rev_list₂] →
              if Q.compare m₁.power m₂.power = 0 then
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

value ops2ps ops =
  let terms =
    loop ops.old_ps_mon where rec loop =
      fun
      [ [] → End
      | [m₁ :: ml₁] → Term m₁ (loop ml₁) ]
  in
  let comden =
    loop ops.old_ps_mon where rec loop =
      fun
      [ [] → I.one
      | [m₁ :: ml₁] → I.lcm (Q.rden (power m₁)) (loop ml₁) ]
  in
  {ps_terms = terms; ps_comden = comden}
;

value ps2ops ps =
  let rec loop ms =
    match ms with
    | Term m₁ ms₁ → [m₁ :: loop (Lazy.force ms₁)]
    | End → []
    end
  in
  {old_ps_mon = loop ps.ps_terms}
;

Definition ps_add (add_coeff : α → α → α) (ps₁ : old_ps α) (ps₂ : old_ps α) :=
  let ps₁ := ops2ps ps₁ in
  let ps₂ := ops2ps ps₂ in
  let cofix loop₁ ms₁ ms₂ :=
    match Lazy.force ms₁ with
    | Term c₁ s₁ =>
        let cofix loop₂ ms₂ :=
          match Lazy.force ms₂ with
          | Term c₂ s₂ =>
              match Qcompare (power c₁) (power c₂) with
              | Eq =>
                  let c := add_coeff (coeff c₁) (coeff c₂) in
                  let m := {| coeff := c; power := power c₁ |} in
                  Term m (loop₁ s₁ s₂)
              | Lt =>
                  Term c₁ (loop₁ s₁ ms₂)
              | Gt =>
                  Term c₂ (loop₂ s₂)
              end
          | End => Lazy.force ms₁
          end
        in
        loop₂ ms₂
    | End => Lazy.force ms₂
    end
  in
  {| ps_terms := loop₁ (lazy (ps_terms ps₁)) (lazy (ps_terms ps₂));
     ps_comden := I.lcm (ps_comden ps₁) (ps_comden ps₂) |};

value old_ps_mul add_coeff mul_coeff is_null_coeff ps₁ ps₂ =
  let ml =
    List.fold_left
      (fun a m₁ →
         List.fold_left
           (fun a m₂ →
              let c = mul_coeff m₁.coeff m₂.coeff in
              let p = Q.norm (Q.add m₁.power m₂.power) in
              [{coeff = c; power = p} :: a])
           a ps₂.old_ps_mon)
      [] ps₁.old_ps_mon
  in
  let ml = List.sort (fun m₁ m₂ → Q.compare m₁.power m₂.power) ml in
  {old_ps_mon = merge_pow add_coeff is_null_coeff ml}
;
value ps_mul add_coeff mul_coeff is_null_coeff ops₁ ops₂ =
  old_ps_mul add_coeff mul_coeff is_null_coeff ops₁ ops₂
;

Definition ser_hd (s : series α) :=
  match s with
  | Term a _ => Some a
  | End => None
  end;

Definition ser_tl (s : series α) : option (series α) :=
  match s with
  | Term _ t => Some (Lazy.force t)
  | End => None
  end;

Fixpoint ser_nth_tl (n : nat) (s : series α) : option (series α) :=
  match n with
  | O => Some s
  | S m =>
      match ser_tl s with
      | None => None
      | Some t => ser_nth_tl m t
      end
  end;

Definition ser_nth (n : nat) (s : series α) : option α :=
  match ser_nth_tl n s with
  | None => None
  | Some t => ser_hd t
  end;

value map_option n s =
  fun
  [ None → n
  | Some x → s x ]
; 

type monom_search α = [ Found of α | Ended | Remaining ];

value rec find_monom p j s =
  match s with
  | Term t s₁ →
      match qcompare (power t) p with
      | Eq → Found t
      | Lt → find_monom p (j + 1) (Lazy.force s₁)
      | Gt → Remaining
      end
  | End →
      Ended
  end
;

value new_ps_mul add_coeff mul_coeff is_null_coeff ps₁ ps₂ =
  let s₁ = ps₁.ps_terms in
  let s₂ = ps₂.ps_terms in
  let comden = I.mul ps₁.ps_comden ps₂.ps_comden in
  let minp₁ = map_option Q.zero power (ser_nth 0 s₁) in
  let minp₂ = map_option Q.zero power (ser_nth 0 s₂) in
  let minp₁c = Q.rnum (Q.norm (Q.muli minp₁ comden)) in
  let minp₂c = Q.rnum (Q.norm (Q.muli minp₂ comden)) in
  let t =
    loop 0 where rec loop i =
      let cp_o =
        loop 0 i where rec loop i j =
          let p₁ = Q.make (I.addi minp₁c i) comden in
          let p₂ = Q.make (I.addi minp₂c j) comden in
          let m₁o = find_monom p₁ 0 s₁ in
          let m₂o = find_monom p₂ 0 s₂ in
          match (m₁o, m₂o) with
          | (Ended, _) | (_, Ended) →
              match j with
              | 0 → Ended
              | _ → loop (succ i) (pred j)
              end
          | (Remaining, _) | (_, Remaining) →
              match j with
              | 0 → Remaining
              | _ → loop (succ i) (pred j)
              end
          | (Found m₁, Found m₂) →
              let p = Q.norm (Q.add (power m₁) (power m₂)) in
              let c =
                let c = mul_coeff (coeff m₁) (coeff m₂) in
                match j with
                | 0 → c
                | _ →
                    match loop (succ i) (pred j) with
                    | Ended | Remaining → c
                    | Found (c₁, p₁) →
                        let _ = assert (Q.eq p p₁) in
                        add_coeff c c₁
                    end
                end
              in
              Found (c, p)
          end
      in
      match cp_o with
      | Ended → End
      | Remaining → loop (succ i)
      | Found (c, p) →
          if is_null_coeff c then loop (succ i)
          else
            let m = {coeff = c; power = p} in
            Term m (loop (succ i))
      end
  in
  {ps_terms = t; ps_comden = comden}
;

(*
value ps_mul add_coeff mul_coeff is_null_coeff ops₁ ops₂ =
  ps2ops (new_ps_mul add_coeff mul_coeff is_null_coeff (ops2ps ops₁)
    (ops2ps ops₂))
;
*)
