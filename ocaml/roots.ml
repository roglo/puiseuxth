(* $Id: roots.ml,v 1.82 2013-05-30 19:29:45 deraugla Exp $ *)

open Printf;
open Pnums;
open Poly_fun;
open Poly_tree;
open Poly;
open Field;

value verbose = ref False;

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
      match k.ext.to_q r with
      [ Some rq →
          let rn = Q.rnum rq in
          let rd = Q.rden rq in
          let r =
            if I.eq rd I.one && I.eq rn I.one then k.one
            else
              let d = I.mul rn rd in
              k.ext.normalise (k.ext.of_a (A₂.make Q.zero (Q.make I.one rd) d))
          in
          let r₁ = r in
          let r₂ = k.neg r in
          Some [(r₁, n); (r₂, n)]
      | None →
          None ]
  | 3 →
      match k.ext.to_q r with
      [ Some rq →
          let rn = Q.rnum rq in
          let rd = Q.rden rq in
          let r =
            if I.eq rd I.one then
              if I.eq rn I.one then k.one
              else if I.eq rn I.minus_one then k.ext.minus_one
	      else if I.eq rn I.zero then k.zero
              else failwith (sprintf "<< $int:I.ts %s$ ** (1/3) >>" (I.ts rn))
            else
              let rn = I.mul rn (I.mul rd rd) in
              let n = cubic_root rn in
              let d = rd in
              k.ext.of_q (Q.norm (Q.make n d))
          in
          let plus_½ = Q.make I.one I.two in
          let minus_½ = Q.neg plus_½ in
          let ω = k.ext.of_a (A₂.make minus_½ plus_½ (I.of_int (-3))) in
          let ω₂ = k.ext.of_a (A₂.make minus_½ minus_½ (I.of_int (-3))) in
          let r₁ = r in
          let r₂ = k.mul r ω in
          let r₃ = k.mul r ω₂ in
          Some [(r₁, n); (r₂, n); (r₃, n)]
      | None →
          failwith (sprintf "cannot compute ∛%s" (k.ext.to_string r)) ]
  | pow →
      None ]
;

value int_polyn_of_polyn apol =
  let qpol_opt =
    try
      let ml =
        List.map
          (fun m → if Q.eq m.A₂.b Q.zero then m.A₂.a else raise Exit)
          apol.ml
      in
      Some {ml = ml}
    with
    [ Exit → None ]
  in
  match qpol_opt with
  [ Some qpol →
      let l = List.fold_left (fun l m → I.lcm l (Q.rden m)) I.one qpol.ml in
      let ml =
        List.map (fun m → I.mul (Q.rnum m) (I.div l (Q.rden m))) qpol.ml
      in
      Some {ml = ml}
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
    [(k.ext.of_a r, 2)]
  else
    List.map
      (fun d →
         let r =
           A₂.norm
             (A₂.div
                (A₂.add (A₂.neg b) (A₂.make Q.zero (Q.make d Δ_den) Δ_i))
                (A₂.muli a I.two))
         in
         (k.ext.of_a r, 1))
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
               printf " %s%s" (k.ext.to_string r)
                 (if m > 1 then sprintf " (mult %d)" m else ""))
            rl
        in
        let _ = printf "\n%!" in
*)
        List.fold_left
          (fun (mrl, coeffs) (r, m) →
             match k.ext.to_q r with
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
    let rl = List.map (fun r → (k.ext.of_q r, 1)) rl in
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
  try List.nth pol.ml n with
  [ Failure _ → A₂.zero ]
;

value roots_of_c_coeffs k coeffs =
  match coeffs with
  [ [] | [_] → Some []
  | [b; a] →
      let r = k.div (k.neg b) a in
      Some [(r, 1)]
  | [c; b; a] →
      match (k.ext.to_a a, k.ext.to_a b, k.ext.to_a c) with
      [ (Some a, Some b, Some c) →
          Some (roots_of_2nd_deg_polynom_with_algebraic_coeffs k a b c)
      | _ →
          None ]
  | _ → do {
      None } ]
;

value roots_of_polynom_with_algebraic_coeffs k power_gcd pol apol = do {
  let degree = List.length apol.ml - 1 in
  let rl_opt =
    match degree with
    [ 1 →
        let a = coeff_of_degree 1 apol in
        let b = coeff_of_degree 0 apol in
        let r = A₂.div (A₂.neg b) a in
        Some [(k.ext.of_a r, 1)]
    | 2 →
        let a = coeff_of_degree 2 apol in
        let b = coeff_of_degree 1 apol in
        let c = coeff_of_degree 0 apol in
        Some (roots_of_2nd_deg_polynom_with_algebraic_coeffs k a b c)
    | _ →
        match int_polyn_of_polyn apol with
        [ Some ipol → do {
            let rl = roots_of_int_coeffs k ipol.ml in
            let nb_roots = List.fold_left (fun c (_, m) → c + m) 0 rl in
            assert (nb_roots < List.length ipol.ml);
            if nb_roots < List.length ipol.ml - 1 then do {
              if verbose.val then do {
                printf
                  "found only %d root(s) in polynomial of degree %d\n%!"
                  nb_roots (List.length ipol.ml - 1);
              }
              else ();
            }
            else ();
            Some rl
          }
        | None →
            roots_of_c_coeffs k pol.ml ] ]
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
                 printf "  c = %s%s\n%!" (k.ext.to_string r)
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
    loop [] 0 where rec loop rev_al deg =
      if deg = pow then {ml = List.rev [k.one :: rev_al]}
      else if deg = 0 then loop [k.ext.minus_one :: rev_al] (deg + 1)
      else loop [k.zero :: rev_al] (deg + 1)
  in
  let rl = k.ext.cpoly_roots (List.map k.ext.to_complex pol.ml) in
  List.map k.ext.complex_round_zero rl
};

value roots_of_polynom_with_float_coeffs k power_gcd pol = do {
  let ml = List.map k.ext.to_complex pol.ml in
  let rl = k.ext.cpoly_roots (List.rev ml) in
  let rl = List.map k.ext.complex_round_zero rl in
  if verbose.val then do {
    List.iter
      (fun r → printf "cpoly root: %s\n%!" (k.ext.complex_to_string False r))
      rl;
  }
  else ();
  let rl =
    if power_gcd = 1 then rl
    else do {
      let rou = float_roots_of_unity k power_gcd in
      if verbose.val then do {
        List.iter
          (fun r →
             printf "root of unity: %s\n%!" (k.ext.complex_to_string False r))
          rou
      }
      else ();
      let rll =
        List.map
          (fun r →
             let r = k.ext.of_complex r in
             let r = k.ext.nth_root r power_gcd in
             List.map
               (fun ru →
                  let ru = k.ext.of_complex ru in
                  k.mul r ru)
               rou)
          rl
      in
      let rl = List.concat rll in
      let rl = List.map k.ext.float_round_zero rl in
      List.map k.ext.to_complex rl
    }
  in
  let rl = List.map k.ext.of_complex rl in
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
      (List.sort k.ext.compare rl) []
(**)
  in
  if verbose.val then do {
    if rl <> [] then printf "roots:\n%!" else ();
    List.iter
      (fun (r, m) →
         printf "  c = %s%s\n%!" (k.ext.to_string r)
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
             match k.ext.to_a m with
             [ Some a → a
             | None → raise Exit ])
          pol.ml
      in
      Some {ml = ml}
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
  let cl = pol.al @ [pol.an] in
  let (power_gcd, _) =
    List.fold_left
      (fun (gp, deg) m →
         let gp = if k.eq k.zero m then gp else gcd gp deg in
         (gp, deg + 1))
      (0, 0) cl
  in
  let g = List.fold_left (fun g c → k.ext.gcd g c) k.zero cl in
  let ml =
    let (rev_ml, _) =
      List.fold_left
        (fun (rev_ml, deg) m →
           let rev_ml =
             if deg mod power_gcd = 0 then [k.div m g :: rev_ml] else rev_ml
           in
           (rev_ml, deg + 1))
        ([], 0) cl
    in
    List.rev rev_ml
  in
  if verbose.val then do {
    let pol = {ml = ml} in
    let t = rev_tree_of_polyn k pol in
    if power_gcd = 1 then
      printf "resolving %s=0\n%!" (string_of_tree k True "x" "c" t)
    else
      printf "resolving %s=0 and c=z%s\n%!" (string_of_tree k True "x" "z" t)
        (sup_string_of_string ("1/" ^ soi power_gcd))
  }
  else ();
  let pol = {ml = ml} in
  roots_of_polynom_with_irreduc_coeffs_and_exp k power_gcd pol
};
