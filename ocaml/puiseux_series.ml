(* $Id: puiseux_series.ml,v 1.11 2013-05-22 20:21:06 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Pnums;

Record stream α := { hd : 'a; tl : Lazy.t (option (stream α)) };

Record ps_monomial α := { coeff : α; power : Q };
Record puiseux_series α := { ps_monoms : option (stream (ps_monomial α)) };
Record old_ps α :=  { old_ps_mon : list (ps_monomial α) };

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
  match ops.old_ps_mon with
  | [] → {ps_monoms = None}
  | [m :: ml] →
      let s =
        loop m ml where rec loop m =
          fun
          [ [] → {hd = m; tl = lazy None}
          | [m₁ :: ml₁] → {hd = m; tl = lazy (Some (loop m₁ ml₁))} ]
      in
      {ps_monoms = Some s}
  end;

value ps2ops ps =
  match ps.ps_monoms with
  | None → {old_ps_mon = []}
  | Some s →
      let rec loop s =
        match Lazy.force s.tl with
        | None → [s.hd]
        | Some s₁ → [s.hd :: loop s₁]
        end
      in
      {old_ps_mon = loop s}
  end
;

Definition ps_add add_coeff is_null_coeff ps₁ ps₂ :=
  let fix loop ms₁ ms₂ :=
    match (ms₁, ms₂) with
    | (None, None) => None
    | (None, Some _) => ms₂
    | (Some _, None) => ms₁
    | (Some s₁, Some s₂) =>
        match Qcompare (power (hd s₁)) (power (hd s₂)) with
        | Eq =>
            let c := add_coeff (coeff (hd s₁)) (coeff (hd s₂)) in
            if is_null_coeff c then
              loop (Lazy.force (tl s₁)) (Lazy.force (tl s₂))
            else
              let m := {| coeff := c; power := power (hd s₁) |} in
              let ms :=
                lazy (loop (Lazy.force (tl s₁)) (Lazy.force (tl s₂)))
              in
              Some {| hd := m; tl := ms |}
        | Lt =>
            Some {| hd := hd s₁; tl := lazy (loop (Lazy.force (tl s₁)) ms₂) |}
        | Gt =>
            Some {| hd := hd s₂; tl := lazy (loop ms₁ (Lazy.force (tl s₂))) |}
        end
    end
  in
  let ps₁ := ops2ps ps₁ in
  let ps₂ := ops2ps ps₂ in
  {ps_monoms = loop (ps_monoms ps₁) (ps_monoms ps₂)}
;

value ps_mul add_coeff mul_coeff is_null_coeff ps₁ ps₂ =
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
