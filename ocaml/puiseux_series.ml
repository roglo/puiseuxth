(* $Id: puiseux_series.ml,v 1.30 2013-05-24 10:54:26 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Printf;
open Pnums;

type series α = [ Term of α and Lazy.t (series α) | End ];

Record ps_monomial α := { coeff : α; power : Q };
Record puiseux_series α := { ps_monoms : series (ps_monomial α) };
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
  let rec loop =
    fun
    [ [] → End
    | [m₁ :: ml₁] → Term m₁ (loop ml₁) ]
  in
  {ps_monoms = loop ops.old_ps_mon}
;

value ps2ops ps =
  let rec loop ms =
    match ms with
    | Term m₁ ms₁ → [m₁ :: loop (Lazy.force ms₁)]
    | End → []
    end
  in
  {old_ps_mon = loop ps.ps_monoms}
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
  {| ps_monoms := loop₁ (lazy (ps_monoms ps₁)) (lazy (ps_monoms ps₂)) |};

Definition ser_hd α (s : series α) :=
  match s with
  | Term a _ => Some a
  | End => None
  end;

Definition ser_tl α (s : series α) : option (series α) :=
  match s with
  | Term _ t => Some (Lazy.force t)
  | End => None
  end;

Fixpoint ser_nth_tl α (n : nat) (s : series α) : option (series α) :=
  match n with
  | O => Some s
  | S m =>
      match ser_tl α s with
      | None => None
      | Some t => ser_nth_tl α m t
      end
  end;

Definition ser_nth α (n : nat) (s : series α) : option α :=
  match ser_nth_tl α n s with
  | None => None
  | Some t => ser_hd α t
  end;

value not_none =
  fun
  [ None → failwith "not_none"
  | Some v → v ]
;

value new_ps_mul add_coeff mul_coeff ps₁ ps₂ =
  let s₁ = ps₁.ps_monoms in
  let s₂ = ps₂.ps_monoms in
  let α = () in
  let sum_pow i j =
    match (ser_nth α i s₁, ser_nth α j s₂) with
    | (None, _) | (_, None) → None
    | (Some t₁, Some t₂) → Some (Q.norm (Q.add (power t₁) (power t₂)))
    end
  in
  let ml =
    loop (-1) (-1) (-1) (-1) where rec loop m₁ mm₁ m₂ mm₂ =
      let (i₁, j₁) = (succ m₁, 0) in
      let (i₂, j₂) = (0, succ m₂) in
      let (i₃, j₃) = (succ mm₂, succ mm₁) in
      let sum₁ = sum_pow i₁ j₁ in
      let sum₂ = sum_pow i₂ j₂ in
      let sum₃ = sum_pow i₃ j₃ in
      match (sum₁, sum₂, sum₃) with
      | (None, None, None) → End
      | (None, None, Some _) → failwith "new_ps_mul 2"
      | (None, Some p₂, None) →
          let t₁ = not_none (ser_nth α i₂ s₁) in
          let t₂ = not_none (ser_nth α j₂ s₂) in
          let c = mul_coeff (coeff t₁) (coeff t₂) in
          Term {coeff = c; power = p₂} (loop m₁ mm₁ (succ m₂) mm₂)
      | (None, Some _, Some _) → failwith "new_ps_mul 4"
      | (Some p₁, None, None) →
          let t₁ = not_none (ser_nth α i₁ s₁) in
          let t₂ = not_none (ser_nth α j₁ s₂) in
          let c = mul_coeff (coeff t₁) (coeff t₂) in
          Term {coeff = c; power = p₁} (loop (succ m₁) mm₁ m₂ mm₂)
      | (Some _, None, Some _) → failwith "new_ps_mul 6"
      | (Some _, Some _, None) → failwith "new_ps_mul 7"
      | (Some p₁, Some p₂, Some p₃) →
          if (i₁, j₁) = (i₂, j₂) && (i₁, j₁) = (i₃, j₃) then
            let t₁ = not_none (ser_nth α i₁ s₁) in
            let t₂ = not_none (ser_nth α j₁ s₂) in
            let c = mul_coeff (coeff t₁) (coeff t₂) in
            Term {coeff = c; power = p₁} (loop i₁ j₃ j₂ i₃)
          else
            failwith
              (sprintf "new_ps_mul 8 (%d,%d)(%d,%d)(%d,%d)" i₁ j₁ i₂ j₂ i₃ j₃)
      end
  in
  {ps_monoms = ml}
;
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
(*
value ps_mul add_coeff mul_coeff is_null_coeff ops₁ ops₂ =
  ps2ops (new_ps_mul add_coeff mul_coeff (ops2ps ops₁) (ops2ps ops₂))
;
*)
value ps_mul add_coeff mul_coeff is_null_coeff ops₁ ops₂ =
  old_ps_mul add_coeff mul_coeff is_null_coeff ops₁ ops₂
;
(**)
