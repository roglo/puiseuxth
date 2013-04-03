(* $Id: roots.ml,v 1.60 2013-04-03 09:19:38 deraugla Exp $ *)

open Printf;
open Pnums;
open Poly_fun;
open Poly_tree;
open Poly;
open Field;

value verbose = ref False;

value list_of_polynomial zero pol =
  loop 0 pol.monoms where rec loop deg =
    fun
    [ [m :: ml] →
        if m.power > deg then [zero :: loop (deg + 1) [m :: ml]]
        else if m.power = deg then [m.coeff :: loop (deg + 1) ml]
        else invalid_arg "list_of_polynomial"
    | [] -> [] ]
;

value cubic_root n =
  let (is_neg, n) = if I.lt n I.zero then (True, I.neg n) else (False, n) in
  let dl = factor n in
  let v =
    loop I.zero 0 dl where rec loop cf cc =
      fun
      [ [d :: dl] →
          if I.eq d cf then
            if cc = 2 then I.mul cf (loop I.zero 0 dl)
            else loop cf (cc + 1) dl
          else if cc = 0 then loop d 1 dl
          else failwith "1 cubic_root"
      | [] →
          if cc = 0 then I.one
          else failwith "2 cubic_root" ]
  in
  if is_neg then I.neg v else v
;

value subst_roots_of_unity k pow (r, n) =
  match pow with
  [ 2 →
      match k.to_q r with
      [ Some rq →
          let rn = Q.rnum rq in
          let rd = Q.rden rq in
          let r =
            if I.eq rd I.one && I.eq rn I.one then k.one
            else
              let d = I.mul rn rd in
              k.normalise (k.of_a (A₂.make Q.zero (Q.make I.one rd) d))
          in
          let r₁ = r in
          let r₂ = k.neg r in
          Some [(r₁, n); (r₂, n)]
      | None →
          None ]
  | 3 →
      match k.to_q r with
      [ Some rq →
          let rn = Q.rnum rq in
          let rd = Q.rden rq in
          let r =
            if I.eq rd I.one then
              if I.eq rn I.one then k.one
              else if I.eq rn I.minus_one then k.minus_one
              else failwith (sprintf "<< $int:I.ts %s$ ** (1/3) >>" (I.ts rn))
            else
              let rn = I.mul rn (I.mul rd rd) in
              let n = cubic_root rn in
              let d = rd in
              k.of_q (Q.norm (Q.make n d))
          in
          let plus_½ = Q.make I.one I.two in
          let minus_½ = Q.neg plus_½ in
          let ω = k.of_a (A₂.make minus_½ plus_½ (I.of_int (-3))) in
          let ω₂ = k.of_a (A₂.make minus_½ minus_½ (I.of_int (-3))) in
          let r₁ = r in
          let r₂ = k.mul r ω in
          let r₃ = k.mul r ω₂ in
          Some [(r₁, n); (r₂, n); (r₃, n)]
      | None →
          failwith (sprintf "cannot compute ∛%s" (k.to_string r)) ]
  | pow →
      None ]
;

value int_polyn_of_polyn apol =
  let qpol_opt =
    try
      let ml =
        List.map
          (fun m →
             if Q.eq m.coeff.A₂.b Q.zero then
               {coeff = m.coeff.A₂.a; power = m.power}
             else
               raise Exit)
          apol.monoms
      in
      Some {monoms = ml}
    with
    [ Exit → None ]
  in
  match qpol_opt with
  [ Some qpol →
      let l =
        List.fold_left (fun l m → I.lcm l (Q.rden m.coeff)) I.one qpol.monoms
      in
      let ml =
        List.map
          (fun m →
             {coeff = I.mul (Q.rnum m.coeff) (I.div l (Q.rden m.coeff));
              power = m.power})
          qpol.monoms
      in
      Some {monoms = ml}
  | None → None ]
;

value derivative =
  fun
  [ [] → []
  | [_ :: cl] →
      let (_, rev_cl) =
        List.fold_left
          (fun (n, rev_cl) c → (I.succ n, [I.mul c n :: rev_cl]))
          (I.one, []) cl
      in
      List.rev rev_cl ]
;

value rec list_uniq cmp =
  fun
  [ [a; b :: l] →
      if cmp a b = 0 then list_uniq cmp [b :: l]
      else [a :: list_uniq cmp [b :: l]]
  | [a] → [a]
  | [] → [] ]
;

value divisors_of a =
  let fl = factor a in
  let r =
    loop [I.one] fl where rec loop list =
      fun
      [ [f :: fl] →
          List.rev_append (loop (List.map (I.mul f) list) fl) (loop list fl)
      | [] →
          list ]
  in
  list_uniq I.compare (List.sort I.compare r)
;

value eval_poly coeffs x =
  List.fold_right (fun c a → Q.add (Q.mul a x) (Q.of_i c)) coeffs Q.zero
;

value rat_roots coeffs =
  match coeffs with
  [ [] | [_] → []
  | _ →
      let a₀ = List.hd coeffs in
      let an = List.hd (List.rev coeffs) in
      let div₀ = divisors_of (I.abs a₀) in
      let divn = divisors_of (I.abs an) in
      loop div₀ where rec loop =
        fun
        [ [a :: div₀] →
            loopn divn where rec loopn =
              fun
              [ [b :: divn] →
                  if I.eq (I.gcd (I.abs a) b) I.one then
                    let l = loopn divn in
                    let l =
                      let q = Q.make a b in
                      if I.eq (Q.rnum (eval_poly coeffs q)) I.zero then
                        [q :: l]
                      else l
                    in
                    let l =
                      let q = Q.make (I.neg a) b in
                      if I.eq (Q.rnum (eval_poly coeffs q)) I.zero then
                        [q :: l]
                      else l
                    in
                    l
                  else loopn divn
              | [] → loop div₀ ]
        | [] → [] ] ]
;

value roots_of_2nd_deg_polynom_with_algebraic_coeffs k a b c =
  let Δ = A₂.norm (A₂.sub (A₂.mul b b) (A₂.mul (A₂.muli a (I.of_int 4)) c)) in
  let Δ = if I.eq Δ.A₂.d I.zero then Δ.A₂.a else failwith "Δ not rational" in
  let (Δ_i, Δ_den) = (I.mul (Q.rnum Δ) (Q.rden Δ), Q.rden Δ) in
  if I.eq Δ_i I.zero then
    let r = A₂.norm (A₂.div (A₂.neg b) (A₂.muli a I.two)) in
    [(k.of_a r, 2)]
  else
    List.map
      (fun d →
         let r =
           A₂.norm
             (A₂.div
                (A₂.add (A₂.neg b) (A₂.make Q.zero (Q.make d Δ_den) Δ_i))
                (A₂.muli a I.two))
         in
         (k.of_a r, 1))
      [I.one; I.minus_one]
;

value rec non_zero_roots_of_int_coeffs k coeffs =
  let (mrl, coeffs) =
    let dcoeffs = derivative coeffs in
    let pg = poly_gcd coeffs dcoeffs in
    match pg with
    [ [] | [_] → ([], coeffs)
    | _ →
        let mrl = non_zero_roots_of_int_coeffs k pg in
(*
        let _ = printf "%d root(s):" (List.length rl) in
        let _ =
          List.iter
            (fun (r, m) →
               printf " %s%s" (k.to_string r)
                 (if m > 1 then sprintf " (mult %d)" m else ""))
            rl
        in
        let _ = printf "\n%!" in
*)
        List.fold_left
          (fun (mrl, coeffs) (r, m) →
             match k.to_q r with
             [ Some rq →
                 let b = [I.neg (Q.rnum rq); Q.rden rq] in
                 let (coeffs, m) =
                   loop coeffs 0 where rec loop coeffs m =
                     let (quo, rem) = poly_eucl_div coeffs b in
                     match rem with
                     [ [] →
                         if List.length quo < List.length b then (quo, m + 1)
                         else loop quo (m + 1)
                     | _ → (coeffs, m) ]
                 in
                 ([(r, m) :: mrl], coeffs)
             | None →
                 ([(r, m) :: mrl], coeffs) ])
          ([], coeffs) mrl ]
  in
  let rl =
    let rl =
      match coeffs with
      [ [b; a] → [Q.norm (Q.make (I.neg b) a)]
      | _ → rat_roots coeffs ]
    in
    let coeffs =
      if rl <> [] then
        List.fold_left
          (fun coeffs r →
             let (coeffs, rem) =
               let b = [I.neg (Q.rnum r); Q.rden r] in
               poly_eucl_div coeffs b
             in
             let _ = assert (rem = []) in
             coeffs)
           coeffs rl
      else coeffs
    in
    let rl = List.map (fun r → (k.of_q r, 1)) rl in
    let rl' =
      match List.length coeffs - 1 with
      [ 0 → []
      | 2 →
          let a = A₂.of_i (List.nth coeffs 2) in
          let b = A₂.of_i (List.nth coeffs 1) in
          let c = A₂.of_i (List.nth coeffs 0) in
          roots_of_2nd_deg_polynom_with_algebraic_coeffs k a b c
      | deg →
          failwith (sprintf "cannot compute roots deg %d" deg) ]
    in
    rl @ rl'
  in
  mrl @ rl
;

value zero_roots k coeffs =
  let (zero_mult, coeffs) =
    loop 0 coeffs where rec loop zm =
      fun
      [ [c :: cl] when I.eq c I.zero → loop (zm + 1) cl
      | cl → (zm, cl) ]
  in
  let rl = if zero_mult > 0 then [(k.zero, zero_mult)] else [] in
  (rl, coeffs)
;

value roots_of_int_coeffs k coeffs =
  let (rl₁, coeffs) = zero_roots k coeffs in
  let rl₂ = non_zero_roots_of_int_coeffs k coeffs in
  rl₁ @ rl₂
;

value coeff_of_degree n pol =
  try (List.find (fun m → m.power = n) pol.monoms).coeff with
  [ Not_found → A₂.zero ]
;

(*
value find_algebr_nb k pol =
  loop pol.monoms where rec loop =
    fun
    [ [m :: ml] →
        match k.to_a m.coeff with
        [ Some x → if I.eq x.A₂.d I.zero then loop ml else Some x
        | None → loop ml ]
    | [] → None ]
;
*)

value roots_of_c_coeffs k pol coeffs =
  match coeffs with
  [ [] | [_] → Some []
  | [b; a] →
      let r = k.div (k.neg b) a in
      Some [(r, 1)]
  | [c; b; a] →
      match (k.to_a a, k.to_a b, k.to_a c) with
      [ (Some a, Some b, Some c) →
          Some (roots_of_2nd_deg_polynom_with_algebraic_coeffs k a b c)
      | _ →
          let t = tree_of_y_polyn k {monoms = List.rev pol.monoms} in
          failwith
            (sprintf "cannot compute roots of '%s'"
               (string_of_tree k True "x" "y" t)) ]
  | _ → do {
(**)
      None
(*
      let algeb_nb = find_algebr_nb k pol in
      match algeb_nb with
      [ Some x →
          let yt = Mult (Const (k.of_a x)) (Ypower 1) in
          let polyn = tree_of_y_polyn k {monoms = List.rev pol.monoms} in
          let polyn₂ = substitute_y k yt polyn in
          let polyn₂ = normalise k polyn₂ in
          let pol = xy_polyn_of_tree k polyn₂ in
          let pol_opt =
            try
              let cnl =
                List.map
                  (fun my →
                     let cpl = my.coeff.monoms in
                     let py = my.power in
                     match cpl with
                     [ [mx] →
                         if Q.eq mx.power Q.zero then
                           {coeff = mx.coeff; power = py}
                         else
                           raise Exit
                     | _ →
                         raise Exit ])
                  pol.monoms
              in
              Some {monoms = cnl}
            with
            [ Exit → None ]
          in
          match pol_opt with
          [ Some pol →
              let t = tree_of_y_polyn k pol in
              failwith
                (sprintf "not impl substituted polynomial %s"
                   (string_of_tree k True "x" "y" t))
          | None →
              failwith
                (sprintf "cannot compute roots of '%s'\n%!"
                   (string_of_tree k True "x" "y" polyn)) ]
      | None →
          let t = tree_of_y_polyn k {monoms = List.rev pol.monoms} in
          failwith
            (sprintf "cannot compute roots of '%s'\n%!"
               (string_of_tree k True "x" "y" t)) ];
*)
    } ]
;

value roots_of_polynom_with_algebraic_coeffs k power_gcd pol apol = do {
  let degree = (List.hd (List.rev apol.monoms)).power in
  let rl_opt =
    match degree with
    [ 1 →
        let a = coeff_of_degree 1 apol in
        let b = coeff_of_degree 0 apol in
        let r = A₂.div (A₂.neg b) a in
        Some [(k.of_a r, 1)]
    | 2 →
        let a = coeff_of_degree 2 apol in
        let b = coeff_of_degree 1 apol in
        let c = coeff_of_degree 0 apol in
        Some (roots_of_2nd_deg_polynom_with_algebraic_coeffs k a b c)
    | _ →
        match int_polyn_of_polyn apol with
        [ Some ipol → do {
            let coeffs = list_of_polynomial I.zero ipol in
            let rl = roots_of_int_coeffs k coeffs in
            let nb_roots = List.fold_left (fun c (_, m) → c + m) 0 rl in
            assert (nb_roots < List.length coeffs);
            if nb_roots < List.length coeffs - 1 then do {
              if verbose.val then do {
                printf
                  "found only %d root(s) in polynomial of degree %d\n%!"
                  nb_roots (List.length coeffs - 1);
              }
              else ();
            }
            else ();
            Some rl
          }
        | None → do {
            let coeffs = list_of_polynomial k.zero pol in
            roots_of_c_coeffs k pol coeffs
          } ] ]
  in
  match rl_opt with
  [ Some rl →
      let rl_opt =
        if power_gcd = 1 then Some rl
        else
          let rll_opt =
            try
              let rll =
                List.map
                  (fun r →
                     match subst_roots_of_unity k power_gcd r with
                     [ Some rl → rl
                     | None → raise Exit ])
                  rl
              in
              Some rll
            with
            [ Exit → None ]
          in
          match rll_opt with
          [ Some rll → Some (List.concat rll)
          | None → None ]
      in
      match rl_opt with
      [ Some rl → do {
          if verbose.val then do {
            if rl <> [] then printf "roots:\n%!" else ();
            List.iter
              (fun (r, m) →
                 printf "  c = %s%s\n%!" (k.to_string r)
                   (if m > 1 then sprintf " (multiplicity %d)" m else ""))
              rl;
          }
          else ();
          Some rl
        }
      | None → None ]
  | None → None ]
};

value float_roots_of_unity k pow = do {
  let pol =
    let m₁ = {coeff = k.minus_one; power = 0} in
    let m₂ = {coeff = k.one; power = pow} in
    {monoms = [m₁; m₂]}
  in
  let fnl = list_of_polynomial k.zero pol in
  let rl = k.cpoly_roots (List.map k.to_complex fnl) in
  List.map k.complex_round_zero rl
};

value roots_of_polynom_with_float_coeffs k power_gcd pol = do {
  let ml =
    List.map (fun m → {coeff = k.to_complex m.coeff; power = m.power})
      pol.monoms
  in
  let complex_zero = k.to_complex k.zero in
  let fpl = list_of_polynomial complex_zero {monoms = ml} in
  let rl = k.cpoly_roots (List.rev fpl) in
  let rl = List.map k.complex_round_zero rl in
  if verbose.val then do {
    List.iter
      (fun r → printf "cpoly root: %s\n%!" (k.complex_to_string False r)) rl;
  }
  else ();
  let rl =
    if power_gcd = 1 then rl
    else do {
      let rou = float_roots_of_unity k power_gcd in
      if verbose.val then do {
        List.iter
          (fun r →
             printf "root of unity: %s\n%!" (k.complex_to_string False r))
          rou
      }
      else ();
      let rll =
        List.map
          (fun r →
             let r = k.of_complex r in
             let r = k.nth_root r power_gcd in
             List.map
               (fun ru →
                  let ru = k.of_complex ru in
                  k.mul r ru)
               rou)
          rl
      in
      let rl = List.concat rll in
      let rl = List.map k.float_round_zero rl in
      List.map k.to_complex rl
    }
  in
  let rl = List.map k.of_complex rl in
  let rl =
    List.fold_right
      (fun r rnl →
         match rnl with
         [ [(r₁, n₁) :: rnl₁] →
             if k.eq r r₁ then [(r₁, n₁+1) :: rnl₁]
             else [(r, 1) :: rnl]
         | [] → [(r, 1) :: rnl] ])
(*
      rl []
*)
      (List.sort k.compare rl) []
(**)
  in
  if verbose.val then do {
    if rl <> [] then printf "roots:\n%!" else ();
    List.iter
      (fun (r, m) →
         printf "  c = %s%s\n%!" (k.to_string r)
           (if m > 1 then sprintf " (multiplicity %d)" m else ""))
      rl;
  }
  else ();
  rl
};

value roots_of_polynom_with_irreduc_coeffs_and_exp k power_gcd pol =
  let apol_opt =
    try
      let ml =
        List.map
          (fun m →
             match k.to_a m.coeff with
             [ Some a → {coeff = a; power = m.power}
             | None → raise Exit ])
          pol.monoms
      in
      Some {monoms = ml}
    with
    [ Exit → None ]
  in
  match apol_opt with
  [ Some apol →
      match roots_of_polynom_with_algebraic_coeffs k power_gcd pol apol with
      [ Some rl → rl
      | None → do {
          if verbose.val then
            printf "Failed formally resolving roots: now using floats\n\n%!"
          else ();
          roots_of_polynom_with_float_coeffs k power_gcd pol
        } ]
  | None → roots_of_polynom_with_float_coeffs k power_gcd pol ]
;

value roots k pol = do {
  let power_gcd = List.fold_left (fun gp m → gcd gp m.power) 0 pol.monoms in
  let g = List.fold_left (fun g m → k.gcd g m.coeff) k.zero pol.monoms in
  let ml =
    List.map
      (fun m → {coeff = k.div m.coeff g; power = m.power / power_gcd})
      pol.monoms
  in
  if verbose.val then do {
    let rev_pol = {monoms = List.rev ml} in
    let t = tree_of_y_polyn k rev_pol in
    if power_gcd = 1 then
      printf "resolving %s=0\n%!" (string_of_tree k True "x" "c" t)
    else
      printf "resolving %s=0 and c=z%s\n%!" (string_of_tree k True "x" "z" t)
        (sup_string_of_string ("1/" ^ soi power_gcd))
  }
  else ();
  let pol = {monoms = ml} in
  roots_of_polynom_with_irreduc_coeffs_and_exp k power_gcd pol
};
