(* $Id: puiseux_series.ml,v 1.67 2013-05-29 02:28:20 deraugla Exp $ *)

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

Definition map_option n s v :=
  match v with
  | None => n
  | Some x => s x
  end;

Inductive monom_search α :=
  | Found : ps_monomial α → monom_search α
  | Remaining : Q → monom_search α
  | Ended : monom_search α;

Fixpoint find_monom p (s : series (ps_monomial α)) n :=
  match n with
  | O => Ended
  | S n₁ =>
      match s with
      | Term t s₁ =>
          match Qcompare (power t) p with
          | Eq => Found t
          | Lt => find_monom p (Lazy.force s₁) n₁
          | Gt => Remaining (power t)
          end
      | End =>
         Ended
      end
  end;

Definition scan_diag (add_coeff : α → α → α) (mul_coeff : α → α → α)
    minp₁c minp₂c comden s₁ s₂ :=
  let fix loop_ij i j :=
    let p₁ := I.addi minp₁c i in
    let p₂ := I.addi minp₂c j in
    let m₁o := find_monom (qof2nat p₁ comden) s₁ (S i) in
    let m₂o := find_monom (qof2nat p₂ comden) s₂ (S j) in
    let ms₁ :=
      match m₁o with
      | Found m₁ =>
          match m₂o with
          | Found m₂ =>
              let c := mul_coeff (coeff m₁) (coeff m₂) in
              let p := Q.norm (Qplus (power m₁) (power m₂)) in
              Found {| coeff := c; power := p |}
          | Remaining p => Remaining Q.zero
          | Ended => Ended
          end
      | Remaining p =>
          match m₂o with
          | Found _ => Remaining p
          | Remaining _ => Remaining p
          | Ended => Ended
          end
      | Ended => Ended
      end
    in
    match j with
    | O => ms₁
    | S j₁ =>
        let ms₂ := loop_ij (S i) j₁ in
        match ms₁ with
        | Found m₁ =>
            match ms₂ with
            | Found m₂ =>
                let c := add_coeff (coeff m₁) (coeff m₂) in
                Found {| coeff := c; power := power m₁ |}
            | Remaining _ => ms₁
            | Ended => ms₁
            end
        | Remaining p =>
            match ms₂ with
            | Found _ => ms₂
            | Remaining _ => Remaining p
            | Ended => Remaining p
            end
        | Ended => ms₂
        end
    end
  in
  loop_ij;

Definition new_ps_mul add_coeff mul_coeff ps₁ ps₂ :=
  let s₁ := ps_terms ps₁ in
  let s₂ := ps_terms ps₂ in
  let comden := I.mul (ps_comden ps₁) (ps_comden ps₂) in
  let minp₁ := map_option Q.zero (λ ps, power ps) (ser_nth 0 s₁) in
  let minp₂ := map_option Q.zero (λ ps, power ps) (ser_nth 0 s₂) in
  let p₁c := Qnum (Q.norm (Q.muli minp₁ comden)) in
  let p₂c := Qnum (Q.norm (Q.muli minp₂ comden)) in
  let t :=
    let cofix loop_sum psum :=
      let cp_o := scan_diag add_coeff mul_coeff p₁c p₂c comden s₁ s₂ 0 psum in
      match cp_o with
      | Ended => End
      | Remaining p =>
(*
          loop_sum (S psum)
*)
          let n := I.to_int (I.sub (Qnum (Q.norm (Q.muli p comden))) p₁c) in
if n ≤ psum then loop_sum (S psum) else
          loop_sum n
(**)
      | Found m => Term m (loop_sum (S psum))
      end
    in
    loop_sum O
  in
  {| ps_terms := t; ps_comden := comden |};

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

(*
value new_new_ps_mul add_coeff mul_coeff ps₁ ps₂ =
  let s₁ = ps_terms ps₁ in
  let s₂ = ps_terms ps₂ in
  let ini_s₁ = s₁ in
  let ini_s₂ = s₂ in
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
          let psum = I.to_int (I.sub sum fst_sum) in
          let cp_o =
... perhaps ssl₁ is enough!!! (i.e. no need to scan_diag)
            scan_diag add_coeff mul_coeff p₁c p₂c comden ini_s₁ ini_s₂ 0 psum
          in
          match cp_o with
          | Ended → End
          | Remaining _ → assert False
          | Found m →
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
      end
  in
  {ps_terms = t; ps_comden = comden}
;
*)

(**)
value ps_mul add_coeff mul_coeff is_null_coeff ops₁ ops₂ =
  ps2ops (new_ps_mul add_coeff mul_coeff (ops2ps ops₁) (ops2ps ops₂))
;
(**)
