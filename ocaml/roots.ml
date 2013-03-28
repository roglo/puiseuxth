(* $Id: roots.ml,v 1.4 2013-03-28 21:37:59 deraugla Exp $ *)

open Printf;
open Pnums;
open Poly_fun;
open Poly_tree;
open Field;

value quiet = ref True;

value rebuild_add_list_z k cpl =
  let rebuild_add t (c₁, p₁) =
    if k.eq c₁ k.zero then t
    else
       let t₁ =
         if p₁ = 0 then Const c₁
         else if k.eq c₁ k.one then Ypower p₁
         else if k.eq c₁ k.minus_one then Neg (Ypower p₁)
         else Mult (Const c₁) (Ypower p₁)
       in
       let t_is_null =
         match t with
         [ Const c → k.eq c k.zero
         | _ → False ]
       in
       if t_is_null then t₁
       else
         match without_initial_neg k t₁ with
         [ Some t₁ → Minus t t₁
         | None → Plus t t₁ ]
  in
  List.fold_left rebuild_add (Const k.zero) cpl
;

value list_of_deg_list zero cnl =
  loop 0 cnl where rec loop deg =
    fun
    [ [(c, n) :: cnl] →
        if n > deg then [zero :: loop (deg + 1) [(c, n) :: cnl]]
        else if n = deg then [c :: loop (deg + 1) cnl]
        else invalid_arg "list_of_deg_list"
    | [] -> [] ]
;

value epsilon_round eps r =
  let re = if abs_float r.re ≤ eps then 0. else r.re in
  let im = if abs_float r.im ≤ eps then 0. else r.im in
  {re = re; im = im}
;

value wrap_prec prec f a = do {
  Cpoly.Mfl.set_prec prec;
(*
  let eps = Cpoly.Mfl.to_float (Cpoly.Mfl.epsilon_float prec) in
*)
  let eps = sqrt epsilon_float in
(**)
  let rl = f a in
  List.map (epsilon_round eps) rl
};

value float_roots_of_unity prec pow = do {
  let fnl = list_of_deg_list 0 [(-1, 0); (1, pow)] in
  wrap_prec prec Cpoly.iroots fnl
};

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
              k.norm (k.of_a (A₂.make Q.zero (Q.make I.one rd) d))
          in
          let r₁ = r in
          let r₂ = k.neg r in
          [(r₁, n); (r₂, n)]
      | None →
          failwith (sprintf "cannot compute √%s" (k.to_string r)) ]
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
          [(r₁, n); (r₂, n); (r₃, n)]
      | None →
          failwith (sprintf "cannot compute ∛%s" (k.to_string r)) ]
  | pow →
      failwith (sprintf "not impl subst_roots_of_unity %d" pow) ]
;

value int_coeffs_of_polyn anl =
  let qnl_opt =
    try
      let qnl =
        List.map
          (fun (x, p) →
             if Q.eq x.A₂.b Q.zero then (x.A₂.a, p) else raise Exit)
          anl
      in
      Some qnl
    with
    [ Exit → None ]
  in
  match qnl_opt with
  [ Some qnl →
      let l =
        List.fold_left (fun l (q, _) → I.lcm l (Q.rden q)) I.one qnl
      in
      let cnl =
        List.map (fun (c, n) → (I.mul (Q.rnum c) (I.div l (Q.rden c)), n)) qnl
      in
      Some cnl
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

value coeff_of_degree n anl =
  try fst (List.find (fun (_, d) → d = n) anl) with
  [ Not_found → A₂.zero ]
;

value find_algebr_nb k pnl =
  loop pnl where rec loop =
    fun
    [ [(c, _) :: l] →
        match k.to_a c with
        [ Some x → if I.eq x.A₂.d I.zero then loop l else Some x
        | None → loop l ]
    | [] → None ]
;

value roots_of_c_coeffs k cpl coeffs =
  match coeffs with
  [ [] | [_] → []
  | [b; a] →
      let r = k.div (k.neg b) a in
      [(r, 1)]
  | [c; b; a] →
      match (k.to_a a, k.to_a b, k.to_a c) with
      [ (Some a, Some b, Some c) →
          roots_of_2nd_deg_polynom_with_algebraic_coeffs k a b c
      | _ →
          let polyn = rebuild_add_list_z k cpl in
          failwith
            (sprintf "cannot compute roots of '%s'"
               (string_of_tree k True "x" "y" polyn)) ]
  | _ → do {
      let algeb_nb = find_algebr_nb k cpl in
      match algeb_nb with
      [ Some x →
          let t = Mult (Const (k.of_a x)) (Ypower 1) in
          let polyn = rebuild_add_list_z k cpl in
          let polyn₂ = substitute_y k t polyn in
          let polyn₂ = normalize k polyn₂ in
          let cplpl = group k polyn₂ in
          let cnl_opt =
            try
              let cnl =
                List.map
                  (fun (cpl, py) →
                     match cpl with
                     [ [(c, px)] →
                         if Q.eq px Q.zero then (c, py) else raise Exit
                     | _ →
                         raise Exit ])
                  cplpl
              in
              Some cnl
            with
            [ Exit → None ]
          in
          match cnl_opt with
          [ Some cnl →
              let polyn = rebuild_add_list_z k cnl in
              failwith
                (sprintf "not impl substituted polynomial %s"
                   (string_of_tree k True "x" "y" polyn))
          | None →
              failwith
                (sprintf "cannot compute roots of '%s'\n%!"
                   (string_of_tree k True "x" "y" polyn)) ]
      | None →
          let polyn = rebuild_add_list_z k cpl in
          failwith
            (sprintf "cannot compute roots of '%s'\n%!"
               (string_of_tree k True "x" "y" polyn)) ];
    } ]
;

value roots_of_polynom_with_float_coeffs k power_gcd cpl = do {
  let prec = 200 in
  let cpl = List.rev_map (fun (n, p) → (k.to_complex n, p)) cpl in
  let fpl = list_of_deg_list complex_zero cpl in
  let rl = wrap_prec prec Cpoly.roots (List.rev fpl) in
  if not quiet.val then do {
    List.iter
      (fun r → printf "cpoly root: %s\n%!" (complex_to_string False r)) rl;
  }
  else ();
  let rl =
    if power_gcd = 1 then rl
    else do {
      let rou = float_roots_of_unity prec power_gcd in
      if not quiet.val then do {
        List.iter
          (fun r → printf "root of unity: %s\n%!" (complex_to_string False r))
          rou
      }
      else ();
      let p = {re = 1. /. float power_gcd; im = 0.} in
      let rll =
        List.map
          (fun r →
             List.map (fun u → complex_mul (complex_power r p) u) rou)
          rl
      in
      let rl = List.concat rll in
      List.map (epsilon_round epsilon_float) rl
    }
  in
  let rl = List.map k.of_complex rl in
  let rl =
    List.fold_right
      (fun r rnl →
         match rnl with
         [ [(r₁, n₁) :: rnl₁] →
             if r = r₁ then [(r₁, n₁+1) :: rnl₁]
             else [(r, 1) :: rnl]
         | [] → [(r, 1) :: rnl] ])
      (List.sort compare rl) []
  in
  if not quiet.val then do {
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

value roots_of_polynom_with_algebraic_coeffs k power_gcd cpl apl = do {
  let degree = snd (List.hd (List.rev apl)) in
  let rl =
    match degree with
    [ 1 →
        let a = coeff_of_degree 1 apl in
        let b = coeff_of_degree 0 apl in
        let r = A₂.div (A₂.neg b) a in
        [(k.of_a r, 1)]
    | 2 →
        let a = coeff_of_degree 2 apl in
        let b = coeff_of_degree 1 apl in
        let c = coeff_of_degree 0 apl in
        roots_of_2nd_deg_polynom_with_algebraic_coeffs k a b c
    | _ →
        match int_coeffs_of_polyn apl with
        [ Some cnl → do {
            let coeffs = list_of_deg_list I.zero cnl in
            let rl = roots_of_int_coeffs k coeffs in
            let nb_roots = List.fold_left (fun c (_, m) → c + m) 0 rl in
            assert (nb_roots < List.length coeffs);
            if nb_roots < List.length coeffs - 1 then do {
              if not quiet.val then do {
                printf
                  "found only %d root(s) in polynomial of degree %d\n%!"
                  nb_roots (List.length coeffs - 1);
              }
              else ();
            }
            else ();
            rl
          }
        | None → do {
            let coeffs = list_of_deg_list k.zero (List.rev cpl) in
            roots_of_c_coeffs k cpl coeffs
          } ] ]
  in
  let rl =
    if power_gcd = 1 then rl
    else
      let rll = List.map (subst_roots_of_unity k power_gcd) rl in
      List.concat rll
  in
  if not quiet.val then do {
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

value roots_of_polynom_with_irreduc_coeffs_and_exp k power_gcd cpl =
  let apl_opt =
    try
      let apl =
        List.rev_map
          (fun (c, p) →
             match k.to_a c with
             [ Some a → (a, p)
             | None → raise Exit ])
          cpl
      in
      Some apl
    with
    [ Exit → None ]
  in
  match apl_opt with
  [ Some apl → roots_of_polynom_with_algebraic_coeffs k power_gcd cpl apl
  | None → roots_of_polynom_with_float_coeffs k power_gcd cpl ]
;

value roots k cpl = do {
  let power_gcd = List.fold_left (fun gp (_, p) → gcd gp p) 0 cpl in
  let g = List.fold_left (fun g (c, _) → k.gcd g c) k.zero cpl in
  let cpl = List.map (fun (c, p) → (k.div c g, p / power_gcd)) cpl in
  if not quiet.val then do {
    let polyn = rebuild_add_list_z k cpl in
    if power_gcd = 1 then
      printf "resolving %s=0\n%!" (string_of_tree k True "x" "c" polyn)
    else
      printf "resolving %s=0 and c=z%s\n%!"
        (string_of_tree k True "x" "z" polyn)
        (sup_string_of_string ("1/" ^ soi power_gcd))
  }
  else ();
  roots_of_polynom_with_irreduc_coeffs_and_exp k power_gcd cpl
};
