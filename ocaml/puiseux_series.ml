(* $Id: puiseux_series.ml,v 1.8 2013-05-22 17:23:05 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Pnums;

type stream α = {hd : 'a; tl : Lazy.t (option (stream α))};

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

(*
Definition ps_add add_coeff is_null_coeff ps₁ ps₂ :=
  let fix loop ml₁ ml₂ :=
    match (ml₁, ml₂) with
    | (None, None) => failwith "ps_add 1"
    | (None, Some _) => ml₂
    | (Some _, None) => failwith "ps_add 3"
    | (Some _, Some _) => failwith "ps_add 4"
    end
  in
  ps2ops {ps_monoms = loop (ops2ps ps₁).ps_monoms (ops2ps ps₂).ps_monoms}
(*
    match Qcompare (power ml₁.hd) (power ml₂.hd) with
    | Eq => failwith "Eq"
    | Lt => failwith "Lt"
    | Gt => failwith "Gt"
    end
*)
(**)
    match (ml₁, ml₂) with
    | ([], ml₂) => ml₂
    | (ml₁, []) => ml₁
    | ([m₁ :: ml₁], [m₂ :: ml₂]) =>
        match Qcompare (power m₁) (power m₂) with
        | Eq =>
            let c := add_coeff (coeff m₁) (coeff m₂) in
            if is_null_coeff c then loop ml₁ ml₂
            else [{| coeff := c; power := power m₁ |} :: loop ml₁ ml₂]
        | Lt =>
            [m₁ :: loop ml₁ [m₂ :: ml₂]]
        | Gt =>
            [m₂ :: loop [m₁ :: ml₁] ml₂]
        end
    end
;
*)

Definition ps_add add_coeff is_null_coeff ps₁ ps₂ :=
  let fix loop ml₁ ml₂ :=
    match (ml₁, ml₂) with
    | ([], ml₂) => ml₂
    | (ml₁, []) => ml₁
    | ([m₁ :: ml₁], [m₂ :: ml₂]) =>
        match Qcompare (power m₁) (power m₂) with
        | Eq =>
            let c := add_coeff (coeff m₁) (coeff m₂) in
            if is_null_coeff c then loop ml₁ ml₂
            else [{| coeff := c; power := power m₁ |} :: loop ml₁ ml₂]
        | Lt =>
            [m₁ :: loop ml₁ [m₂ :: ml₂]]
        | Gt =>
            [m₂ :: loop [m₁ :: ml₁] ml₂]
        end
    end
  in
  {old_ps_mon = loop ps₁.old_ps_mon ps₂.old_ps_mon}
;
(**)

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
