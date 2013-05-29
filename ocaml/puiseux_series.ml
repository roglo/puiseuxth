(* $Id: puiseux_series.ml,v 1.69 2013-05-29 07:59:03 deraugla Exp $ *)

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

value icompare i₁ i₂ =
  let c = I.compare i₁ i₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
;

value qof2nat = Q.make;

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

(*
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
*)

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

Definition map_option n s v :=
  match v with
  | None => n
  | Some x => s x
  end;

(* ps_mul *)

value insert_ij i s₁ j s₂ ssl =
  insert ssl where rec insert ssl =
    match ssl with
    | [] → [(i, s₁, j, s₂)]
    | [(i₁, s₁₁, j₁, s₂₁) :: ssl₁] →
       if i < i₁ then [(i, s₁, j, s₂) :: ssl]
       else if i > i₁ then [(i₁, s₁₁, j₁, s₂₁) :: insert ssl₁]
       else if j < j₁ then [(i, s₁, j, s₂) :: ssl]
       else if j > j₁ then [(i₁, s₁₁, j₁, s₂₁) :: insert ssl₁]
       else ssl
    end
;

value insert_sum sum (i, s₁, j, s₂) sl =
  insert sl where rec insert sl =
    match sl with
    | [] → [(sum, [(i, s₁, j, s₂)])]
    | [(sum₁, ssl₁) :: l] →
        match icompare sum sum₁ with
        | Eq → [(sum₁, insert_ij i s₁ j s₂ ssl₁) :: l]
        | Lt → [(sum, [(i, s₁, j, s₂)]) :: sl]
        | Gt → [(sum₁, ssl₁) :: insert l]
        end
    end
;        

value not_none =
  fun
  [ None → failwith "not none"
  | Some x → x ]
;

value ps_mul add_coeff mul_coeff ps₁ ps₂ =
  let s₁ = ps_terms ps₁ in
  let s₂ = ps_terms ps₂ in
  let comden = I.mul (ps_comden ps₁) (ps_comden ps₂) in
  let minp₁ = map_option Q.zero (λ ps, power ps) (ser_nth 0 s₁) in
  let minp₂ = map_option Q.zero (λ ps, power ps) (ser_nth 0 s₂) in
  let p₁c = Qnum (Q.norm (Q.muli minp₁ comden)) in
  let p₂c = Qnum (Q.norm (Q.muli minp₂ comden)) in
  let fst_sum = I.add p₁c p₂c in
  let t =
    loop [(fst_sum, [(0, s₁, 0, s₂)])] where rec loop sum_fifo =
      match sum_fifo with
      | [] → End
      | [(sum, ssl₁) :: sl] →
          let m =
            loop ssl₁ where rec loop =
              fun
              [ [] → assert False
              | [(_, s₁, _, s₂)] →
                  let m₁ = not_none (ser_hd s₁) in
                  let m₂ = not_none (ser_hd s₂) in
                  let c = mul_coeff (coeff m₁) (coeff m₂) in
                  let p = Q.norm (Qplus (power m₁) (power m₂)) in
                  {coeff = c; power = p}
              | [(_, s₁, _, s₂) :: ssl] →
                  let m = loop ssl in
                  let m₁ = not_none (ser_hd s₁) in
                  let m₂ = not_none (ser_hd s₂) in
                  let c₁ = mul_coeff (coeff m₁) (coeff m₂) in
                  let _ =
                    assert
                      (Q.eq (power m) (Q.norm (Qplus (power m₁) (power m₂))))
                  in
                  {coeff = add_coeff c₁ (coeff m); power = power m} ]
          in
          let sl =
            List.fold_left
              (fun sl (i, s₁, j, s₂) →
                 match ser_tl s₁ with
                 | Some s₁ →
                     match (ser_hd s₁, ser_hd s₂) with
                     | (Some m₁, Some m₂) →
                         let p₁c =
                           Qnum (Q.norm (Q.muli (power m₁) comden)) in
                        let p₂c =
                          Qnum (Q.norm (Q.muli (power m₂) comden)) in
                        let sum = I.add p₁c p₂c in
                        insert_sum sum (S i, s₁, j, s₂) sl
                     | _ → sl
                     end
                 | None → sl
                 end)
              sl ssl₁
          in
          let sl =
            List.fold_left
              (fun sl (i, s₁, j, s₂) →
                 match ser_tl s₂ with
                 | Some s₂ →
                     match (ser_hd s₁, ser_hd s₂) with
                     | (Some m₁, Some m₂) →
                         let p₁c =
                           Qnum (Q.norm (Q.muli (power m₁) comden)) in
                        let p₂c =
                          Qnum (Q.norm (Q.muli (power m₂) comden)) in
                        let sum = I.add p₁c p₂c in
                        insert_sum sum (i, s₁, S j, s₂) sl
                     | _ → sl
                     end
                 | None → sl
                 end)
              sl ssl₁
          in
          Term m (loop sl)
      end
  in
  {ps_terms = t; ps_comden = comden}
;

value ps_mul add_coeff mul_coeff is_null_coeff ops₁ ops₂ =
  ps2ops (ps_mul add_coeff mul_coeff (ops2ps ops₁) (ops2ps ops₂))
;
