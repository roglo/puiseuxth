(* $Id: puiseux.ml,v 1.88 2013-04-03 18:08:07 deraugla Exp $ *)

open Printf;
open Pnums;
open Field;
open Poly_parse;
open Poly_print;
open Poly_tree;
open Poly;
open Roots;

value valuation pol =
  match pol.monoms with
  [ [mx :: _] → mx.power
  | [] → match () with [] ]
;

value valuation_coeff pol =
  match pol.monoms with
  [ [mx :: _] → mx.coeff
  | [] → match () with [] ]
;

type slope_to α = { xy₂ : (α * α); slope : α; skip : int };

value rec minimise_slope k (x₁, y₁) slt_min₁ skip₁ =
  fun
  [ [(x₂, y₂) :: xyl₂] →
      let sl₁₂ = k.normalise (k.div (k.sub y₂ y₁) (k.sub x₂ x₁)) in
      let slt_min =
        if k.le sl₁₂ slt_min₁.slope then
          {xy₂ = (x₂, y₂); slope = sl₁₂; skip = skip₁}
        else
          slt_min₁
      in
      minimise_slope k (x₁, y₁) slt_min (succ skip₁) xyl₂
  | [] →
      slt_min₁ ]
;

value rec next_points k rev_list nb_pts_to_skip (x₁, y₁) =
  fun
  [ [(x₂, y₂) :: xyl₂] →
      match nb_pts_to_skip with
      [ 0 →
          let slt_min =
            let sl₁₂ = k.normalise (k.div (k.sub y₂ y₁) (k.sub x₂ x₁)) in
            let slt_min = {xy₂ = (x₂, y₂); slope = sl₁₂; skip = 0} in
            minimise_slope k (x₁, y₁) slt_min 1 xyl₂
          in
          next_points k [slt_min.xy₂ :: rev_list] slt_min.skip slt_min.xy₂ xyl₂
      | n →
          next_points k rev_list (n - 1) (x₁, y₁) xyl₂ ]
  | [] →
      List.rev rev_list ]
;

value lower_convex_hull k xyl =
  match xyl with
  [ [xy₁ :: xyl₁] → [xy₁ :: next_points k [] 0 xy₁ xyl₁]
  | [] → [] ]
;

value gamma_beta_list k pol =
  let rec loop rev_gbl =
    fun
    [ [(x₁, y₁) :: ([(x₂, y₂) :: _] as xyl₁)] →
        let γ = k.normalise (k.div (k.sub y₂ y₁) (k.sub x₁ x₂)) in
        let β = k.normalise (k.add (k.mul γ x₁) y₁) in
        loop [(γ, β) :: rev_gbl] xyl₁
    | [_] | [] →
        List.rev rev_gbl ]
  in
  let xyl =
    List.map (fun my → (k.of_i (I.of_int my.power), valuation my.coeff))
      pol.monoms
  in
  let ch = lower_convex_hull k xyl in
  loop [] ch
;

value zero_is_root p =
  match p.monoms with
  [ [m :: _] → m.power > 0
  | [] → False ]
;

value start_red = "\027[31m";
value end_red = "\027[m";

value arg_polynom = ref None;
value arg_y = ref "y";
value arg_fname = ref "";
value arg_nb_steps = ref 5;
value arg_lang = ref False;
value arg_eval_sol = ref None;
value arg_all_mpfr = ref False;
value arg_debug = ref False;
value arg_end = ref False;

type branch α β =
  { initial_polynom : polynomial (polynomial α β) int;
    initial_tree: tree α;
    cγl : list (α * β);
    step : int;
    rem_steps : int;
    vx : string;
    vy : string;
    pol : polynomial (polynomial α β) int }
;

value cut_long at_middle s =
  if cut_long_strings.val then
    let len = utf8_strlen s in
    if len > 73 then
      if at_middle then
        sprintf "%s ... %s" (utf8_sub_string s 0 35)
          (utf8_sub_string s (len - 35) 35)
      else
        sprintf "%s ..." (utf8_sub_string s 0 70)
    else s
  else s
;

value rec list_take n l =
  if n ≤ 0 then []
  else
    match l with
    [ [x :: l] → [x :: list_take (n-1) l]
    | [] → [] ]
;

value polyn_of_tree k t =
  let pol = y_polyn_of_tree k t in
  {monoms =
   List.map (fun m → {coeff = x_polyn_of_tree k m.coeff; power = m.power})
     pol.monoms}
;

value string_of_pol k pol =
  string_of_tree k True "x" "y" (tree_of_x_polyn k pol)
;

value norm_add k x y = k.normalise (k.add x y);
value norm_mul k x y = k.normalise (k.mul x y);

value x_pol_add k kq =
  pol_add (norm_add k) (fun c → k.eq c k.zero) kq.compare
;

value x_pol_mul k kq =
  pol_mul (norm_add k) (norm_mul k) (k.eq k.zero) (norm_add kq) kq.compare
;

value apply_poly_x_pol k kq =
  apply_poly {monoms = []} (x_pol_add k kq) (x_pol_mul k kq)
;

value apply_poly_xy_pol k kq =
  apply_poly
    {monoms = []}
    (fun pol c →
       let polc = {monoms = [{coeff = c; power = 0}]} in
       pol_add
         (pol_add k.add (k.eq k.zero) kq.compare)
         (fun pol → pol.monoms = [])
         compare
         pol polc)
    (pol_mul
       (pol_add k.add (k.eq k.zero) kq.compare)
       (pol_mul k.add (norm_mul k) (k.eq k.zero) (norm_add kq) kq.compare)
       (fun pol → pol.monoms = [])
       \+ compare)
;

value map_polynom k f pol =
  let rev_ml =
    List.fold_left
      (fun rev_ml m →
         let c =
           let rev_ml =
             List.fold_left
               (fun rev_ml m →
                  let c = f k m.coeff in
                  if k.eq c k.zero then do {
                    if verbose.val then do {
                      printf "Warning: cancelling small coefficient: %s\n%!"
                        (k.to_string m.coeff)
                    }
                    else ();
                    rev_ml
                  }
                  else [m :: rev_ml])
               [] m.coeff.monoms
           in
           {monoms = List.rev rev_ml}
         in
         if c.monoms = [] then rev_ml
         else
           let m = {coeff = c; power = m.power} in
           [m :: rev_ml])
       [] pol.monoms
  in
  {monoms = List.rev rev_ml}
;

value xy_float_round_zero k pol =
  map_polynom k (fun k c → k.float_round_zero c) pol
;

value float_round_zero k pol =
  let ml =
    List.fold_left
      (fun ml m →
         let c = k.float_round_zero m.coeff in
         if k.eq c k.zero then ml
         else
           let m = {coeff = c; power = m.power} in
           [m :: ml])
       [] pol.monoms
  in
  {monoms = List.rev ml}
;

value print_solution k kq br finite nth cγl = do {
  let (rev_sol, _) =
    List.fold_left
      (fun (sol, γsum) (c, γ) →
         let γsum = kq.normalise (kq.add γsum γ) in
         ([{coeff = c; power = γsum} :: sol], γsum))
      ([], kq.zero) (List.rev cγl)
  in
  let sol = {monoms = List.rev rev_sol} in
  let tsol = tree_of_x_polyn k sol in
  let inf_nth = inf_string_of_string (soi nth) in
  printf "solution: %s%s%s = %s%s%s\n%!"
    (if arg_eval_sol.val <> None || verbose.val then start_red else "")
    br.vy inf_nth
    (airy_string_of_tree k (not arg_lang.val) br.vx br.vy tsol)
    (if finite then "" else " + ...")
    (if arg_eval_sol.val <> None || verbose.val then end_red else "");
  match arg_eval_sol.val with
  [ Some nb_terms →
      let pol = apply_poly_x_pol k kq br.initial_polynom sol in
      let pol = float_round_zero k pol in
      let pol₂ =
        if nb_terms > 0 then {monoms = list_take nb_terms pol.monoms}
        else pol
      in
      let t = tree_of_x_polyn k pol₂ in
      let ellipses =
        if nb_terms = 0 then ""
        else if List.length pol.monoms > nb_terms then " + ..."
        else ""
      in
      printf "f(%s,%s%s) = %s%s\n\n%!" br.vx br.vy inf_nth
        (string_of_tree k (not arg_lang.val) br.vx br.vy t)
        ellipses
  | None → () ]
};

value cancel_constant_term_if_any k t =
  match Poly_tree.flatten t [] with
  [ [t₁ :: tl₁] →
      let td = term_descr_of_term k t₁ in
      if Q.eq td.xpow Q.zero && td.ypow = 0 then do {
        if verbose.val then
          printf "Warning: cancelling constant term: %s\n%!"
            (k.to_string td.const)
        else ();
        match tl₁ with
        [ [t₂ :: tl₂] → List.fold_left (fun t₁ t₂ → Plus t₁ t₂) t₂ tl₂
        | [] → t₁ ]
      }
      else t
  | [] → t ]
;

value puiseux_iteration k kq br r m γ β nth_sol = do {
  if verbose.val then
    let ss = inf_string_of_string (string_of_int br.step) in
    printf "\nc%s = %s  r%s = %d\n\n%!" ss (k.to_string r) ss m
  else ();
  let y =
    let cpy = Plus (Const r) (Ypower 1) in
    if I.eq (Q.rnum γ) I.zero then cpy
    else Mult (xpower γ) cpy
  in
  let xmβ = xpower (Q.neg β) in
  if verbose.val then
    let ss = inf_string_of_string (string_of_int br.step) in
    let ss₁ = inf_string_of_string (string_of_int (br.step - 1)) in
    printf "f%s(%s,%s) = %sf%s(%s,%s) =\n%!" ss br.vx br.vy
      (string_of_tree k True br.vx br.vy xmβ)
      (if br.step = 1 then "" else ss₁) br.vx
      (string_of_tree k True br.vx br.vy y)
  else ();
  let cγl = [(r, γ) :: br.cγl] in
(*
  let pol =
    let y =
      {monoms =
         [{coeff = {monoms = [{coeff = r; power = γ}]}; power = 0};
          {coeff = {monoms = [{coeff = k.one; power = γ}]}; power = 1}]}
    in
    apply_poly_xy_pol k kq br.pol y
  in
  let t = tree_of_xy_polyn k pol in
  printf "\n*** pol = %s\n%!" (string_of_tree k True "x" "y" t);
*)
  let t = tree_of_xy_polyn k br.pol in
  let t = substitute_y k y t in
(*
  printf "*** tpl = %s\n\n%!" (string_of_tree k True "x" "y" (normalise k t));
*)
  let t = Mult xmβ t in
  match try Some (normalise k t) with [ Overflow → None ] with
  [ Some t → do {
      let t = cancel_constant_term_if_any k t in
      if verbose.val then
        let s = string_of_tree k True br.vx br.vy t in
        let s = cut_long True s in
        printf "  %s\n%!" s
      else ();
      let pol = polyn_of_tree k t in
      let pol = xy_float_round_zero k pol in
      let finite = zero_is_root pol in
      if br.rem_steps = 0 || finite then do {
        if verbose.val then do {
          printf "\n";
          if finite then printf "zero is root !\n%!" else ();
        }
        else (); 
        incr nth_sol;
        print_solution k kq br finite nth_sol.val cγl;
        None
      }
      else if br.rem_steps > 0 then Some (pol, cγl)
      else None
    }
  | None → do {
      if verbose.val then do {
        printf "\noverflow!\n";
        printf "displaying solution up to previous step\n";
        printf "\n%!";
      }
      else ();
      incr nth_sol;
      print_solution k kq br False nth_sol.val cγl;
      None
    } ]
};

value rec puiseux_branch k kq br nth_sol (γ, β) =
  let ss = inf_string_of_string (string_of_int br.step) in
  let hl =
    List.filter
      (fun m →
         let αi = valuation m.coeff in
         let βi = Q.norm (Q.add (Q.muli γ (I.of_int m.power)) αi) in
         Q.eq β βi)
      br.pol.monoms
  in
  let j = (List.hd hl).power in
  let q = List.fold_left (fun q m → gcd q (m.power - j)) 0 hl in
  let _ =
    if verbose.val then do {
      printf "γ%s = %-4s" ss (Q.to_string γ);
      printf "  β%s = %-3s" ss (Q.to_string β);
      printf "  %d pts" (List.length hl);
      printf "  j%s=%d" ss j;
      printf "  k%s=%d" ss (List.hd (List.rev hl)).power;
      printf "  q%s=%d" ss q;
      printf "\n%!";
    }
    else ()
  in
  let ml =
    List.map (fun m → {coeff = valuation_coeff m.coeff; power = m.power - j})
      hl
  in
  let rl = roots k {monoms = ml} in
  if rl = [] then do {
    incr nth_sol;
    print_solution k kq br False nth_sol.val br.cγl;
  }
  else
    List.iter
      (fun (r, m) →
         if k.eq r k.zero then ()
         else
           match puiseux_iteration k kq br r m γ β nth_sol with
           [ Some (pol, cγl) → next_step k kq br nth_sol pol cγl
           | None → () ])
      rl

and next_step k kq br nth_sol pol cγl =
  let gbl = gamma_beta_list kq pol in
  let gbl_f = List.filter (fun (γ, β) → not (Q.le γ Q.zero)) gbl in
  if gbl_f = [] then do {
    if verbose.val then do {
      List.iter
        (fun (γ, β) → printf "γ %s β %s\n%!" (Q.to_string γ) (Q.to_string β))
        gbl
    }
    else ();
    failwith "no strictly positive γ value"
  }
  else
    List.iter
      (fun (γ, β) → do {
         if verbose.val then printf "\n%!" else ();
         let br =
           {initial_polynom = br.initial_polynom;
            initial_tree = br.initial_tree;
            cγl = cγl; step = br.step + 1;
            rem_steps = br.rem_steps - 1;
            vx = br.vx; vy = br.vy; pol = pol}
         in
         puiseux_branch k kq br nth_sol (γ, β)
       })
      gbl_f
;

value print_line_equal () =
  if verbose.val then
    printf "\n============================================================\n"
  else ()
;

value puiseux k kq nb_steps vx vy t =
  let pol = polyn_of_tree k t in
  let gbl = gamma_beta_list kq pol in
  let rem_steps = nb_steps - 1 in
  let nth_sol = ref 0 in
  List.iter
    (fun (γ₁, β₁) → do {
       print_line_equal ();
       let br =
         {initial_polynom = pol; initial_tree = t; cγl = []; step = 1;
          rem_steps = rem_steps; vx = vx; vy = vy; pol = pol}
       in
       puiseux_branch k kq br nth_sol (γ₁, β₁)
     })
    gbl
;

value anon_fun s =
  match arg_polynom.val with
  [ None → arg_polynom.val := Some s
  | Some _ → do {
      eprintf "puiseux: one polynomial at a time\n";
      eprintf "use option --help for usage\n%!";
      exit 2
    } ]
;
value usage = "usage: puiseux <options> [--] \"polynomial\"";

value arg_parse () =
  loop 1 where rec loop i =
    if i ≥ Array.length Sys.argv then ()
    else if arg_end.val then do {
      anon_fun Sys.argv.(i);
      loop (i + 1)
    }
    else if
      List.mem Sys.argv.(i) ["--y-var"; "-y"] &&
      i + 1 < Array.length Sys.argv
    then do {
      let v = Sys.argv.(i+1) in
      if String.length v = 1 then arg_y.val := String.make 1 v.[0]
      else do {
        eprintf "puiseux: bad argument for option --y-var\n";
        eprintf "use option --help for usage\n%!";
        exit 2
      };
      loop (i + 2)
    }
    else if
      List.mem Sys.argv.(i) ["--eval-sol"; "-e"] &&
      i + 1 < Array.length Sys.argv
    then do {
      match
        try Some (int_of_string Sys.argv.(i+1)) with [ Failure _ → None ]
      with
      [ Some nb_terms → arg_eval_sol.val := Some nb_terms
      | None → do {
          eprintf "puiseux: option --eval-sol requires a number\n";
          eprintf "use option --help for usage\n%!";
          exit 2
        } ];
      loop (i + 2)
    }
    else if
      List.mem Sys.argv.(i) ["--file"; "-f"] &&
      i + 1 < Array.length Sys.argv
    then do {
      arg_fname.val := Sys.argv.(i+1);
      loop (i + 2)
    }
    else if
      List.mem Sys.argv.(i) ["--nb-steps"; "-n"] &&
      i + 1 < Array.length Sys.argv
    then do {
      let v = Sys.argv.(i+1) in
      match try
        let v = int_of_string v in
        if v ≤ 0 then None else Some v
      with [ Failure _ → None ] with
      [ Some v → arg_nb_steps.val := v
      | None → do {
          eprintf "puiseux: option --nb-steps requires a number ≥ 1\n";
          eprintf "use option --help for usage\n%!";
          exit 2
        } ];
      loop (i + 2)
    }
    else if List.mem Sys.argv.(i) ["--all-mpfr"; "-a"] then do {
      (* undocumented *)
      arg_all_mpfr.val := True;
      loop (i + 1)
    }
    else if List.mem Sys.argv.(i) ["--cut-long"; "-c"] then do {
      cut_long_strings.val := True;
      loop (i + 1)
    }
    else if List.mem Sys.argv.(i) ["--debug"; "-d"] then do {
      arg_debug.val := True;
      loop (i + 1)
    }
    else if List.mem Sys.argv.(i) ["--prog-lang"; "-l"] then do {
      arg_lang.val := True;
      loop (i + 1)
    }
    else if List.mem Sys.argv.(i) ["--verbose"; "-v"] then do {
      verbose.val := True;
      loop (i + 1)
    }
    else if List.mem Sys.argv.(i) ["--with-sqrt-x"; "-w"] then do {
      with_sqrt_x.val := True;
      loop (i + 1)
    }
    else if List.mem Sys.argv.(i) ["--version"] then do {
      printf "Puiseux version %s\n%!" Version.id;
      exit 0;
    }
    else if Sys.argv.(i) = "--" then do {
      arg_end.val := True;
    }
    else if List.mem Sys.argv.(i) ["-h"; "--help"] then do {
      eprintf "%s\n" usage;
      eprintf "Options:\n";
      eprintf "-c, --cut-long        Cut too long lines in verbose mode\n";
      eprintf "-d, --debug           Debug mode\n";
      eprintf "-e, --eval-sol <n>    ";
      eprintf "Eval polynial on solutions; display <n> terms\n";
      eprintf "-f, --file <name>     ";
      eprintf "Read polynomial in file, 1 monomial by line\n";
      eprintf "-h, --help            Display this list of options\n";
      eprintf "-l, --prog-lang       ";
      eprintf "Display in programming language style, with * and ^\n";
      eprintf "-n, --nb-steps <num>  Number of steps (default: 5)\n";
      eprintf "-v, --verbose         Display computation details\n";
      eprintf "-w, --with-sqrt-x     Display x¹ᐟ² and x¹ᐟ³ as √x and ∛x\n";
      eprintf "-y, --y-var <char>    Name of y variable\n";
      eprintf "--                    End of options\n";
      eprintf "--version             Display program version and exit\n";
      eprintf "\n";
      eprintf "If the polynomial starts with '-', use a leading space.\n%!";
      eprintf "E.g. write ' -x+2xy' instead of '-x+2xy'.\n%!";
      eprintf "Or use option '--'.\n%!";
      flush stderr;
      exit 0;
    }
    else if Sys.argv.(i) <> "" && Sys.argv.(i).[0] = '-' then do {
      eprintf "unknown option '%s'\n%!" Sys.argv.(i);
      eprintf "use option --help for usage\n%!";
      exit 2;
    }
    else do {
      anon_fun Sys.argv.(i);
      loop (i + 1)
    }
;

value kq : field Q.t unit =
  {zero = Q.zero; one = Q.one; add = Q.add; sub = Q.sub; neg = Q.neg;
   mul = Q.mul; div = Q.div;
   minus_one = Q.neg Q.one ; normalise = Q.norm;
   nth_root _ = failwith "kq.nth_root"; compare = Q.compare;
   eq = Q.eq; le = Q.le; lt = Q.lt; gcd _ = failwith "kq.gcd";
   neg_factor _ = failwith "kq.neg_factor";
   of_i = Q.of_i; of_q x = x; of_a _ = failwith "kq.of_a";
   of_complex _ = failwith "kq.of_complex";
   of_float_string _ = failwith "kq.of_float_string";
   to_q x = Some x; to_a _ = failwith "kq.to_a";
   to_complex _ = failwith "kq.to_complex"; to_string = Q.to_string;
   float_round_zero _ = failwith "kq.float_round_zero";
   complex_round_zero _ = failwith "kq.complex_round_zero";
   complex_mul _ = failwith "kq.complex_mul";
   cpoly_roots _ = failwith "kq.cpoly_roots";
   complex_to_string _ = failwith "kq.complex_to_string"}
;

value kc () =
  {zero = C.zero; one = C.one; add = C.add; sub = C.sub; neg = C.neg;
   mul = C.mul; div = C.div;
   minus_one = C.minus_one; compare = C.compare; eq = C.eq;
   le _ = failwith "kc.le"; lt _ = failwith "kc.lt"; gcd = C.gcd;
   normalise = C.normalise; nth_root = C.nth_root; neg_factor = C.neg_factor;
   of_i = C.of_i; of_q = C.of_q; of_a = C.of_a; of_complex = C.of_complex;
   of_float_string = C.of_float_string; to_q = C.to_q; to_a = C.to_a;
   to_complex = C.to_complex; to_string = C.to_string arg_lang.val;
   float_round_zero = C.float_round_zero;
   complex_round_zero = C.complex_round_zero; complex_mul = C.complex_mul;
   cpoly_roots = C.cpoly_roots; complex_to_string = C.complex_to_string}
;

value km () =
  {zero = M.zero; one = M.one; add = M.add; sub = M.sub; neg = M.neg;
   mul = M.mul; div = M.div;
   minus_one = M.minus_one; compare = M.compare; eq = M.eq;
   le _ = failwith "km.le"; lt _ = failwith "km.lt"; gcd = M.gcd;
   normalise = M.normalise; nth_root = M.nth_root; neg_factor = M.neg_factor;
   of_i = M.of_i; of_q = M.of_q; of_a = M.of_a; of_complex = M.of_complex;
   of_float_string = M.of_float_string; to_q = M.to_q; to_a = M.to_a;
   to_complex = M.to_complex; to_string = M.to_string arg_lang.val;
   float_round_zero = M.float_round_zero;
   complex_round_zero = M.complex_round_zero; complex_mul = M.complex_mul;
   cpoly_roots = M.cpoly_roots; complex_to_string = M.complex_to_string}
;

value main () = do {
  arg_parse ();
  if arg_polynom.val <> None && arg_fname.val <> "" then do {
    eprintf "puiseux: option -f and \"polynomial\" are incompatible\n%!";
    eprintf "use option --help for usage\n%!";
    exit 2
  }
  else ();
  let vy = arg_y.val in
  try do {
    let p =
      if arg_fname.val <> "" then do {
        if not (Sys.file_exists arg_fname.val) then do {
           eprintf "puiseux: unknown file '%s'\n%!" arg_fname.val;
           exit 2
        }
        else ();
        try parse_poly_in_file vy arg_fname.val with
        [ Ploc.Exc loc e → do {
            eprintf "File \"%s\", location (%d,%d)\n%!" arg_fname.val
              (Ploc.first_pos loc) (Ploc.last_pos loc);
            raise e;
          } ]
      }
      else
        let s =
          match arg_polynom.val with
          [ None → do {
              eprintf "puiseux: missing polynomial\n%!";
              eprintf "use option --help for usage\n%!";
              exit 2
            }
          | Some s → s ]
        in
        try parse_poly s with
        [ Ploc.Exc loc e -> do {
            eprintf "%s\n" Sys.argv.(1);
            eprintf "at location (%d,%d)\n%!" (Ploc.first_pos loc)
              (Ploc.last_pos loc);
            raise e;
          } ]
    in
    if verbose.val then do {
      let inp_txt = string_of_expr True p in
      printf "input:\n";
      printf "%s\n\n%!" inp_txt;
    }
    else ();
    let vl = List.rev (find_vars p) in
    let vl_no_y = List.filter (fun v → v <> vy && v <> "i") vl in
    let vx =
      match vl_no_y with
      [ [vx] → vx
      | [] → if vy = "x" then "y" else "x"
      | _ → do {
          if List.mem vy vl then do {
            eprintf "Too many variables:%!";
            List.iter (fun v → eprintf " %s%!" v) vl_no_y;
            eprintf "\n%!";
          }
          else do {
            eprintf "No y variable detected.\n%!";
            eprintf "Your variables are:%!";
            List.iter (fun v → eprintf " %s%!" v) vl_no_y;
            eprintf "\n%!";
            eprintf "Which one is 'y'? Name it 'y' or use option -y.\n%!";
          };
          exit 2
        } ]
    in
    if arg_all_mpfr.val then do {
      Cpoly.Mfl.set_prec 200;
      let k = km () in
      let t = tree_of_ast k vx vy p in
      let t = normalise k t in
      let norm_txt = string_of_tree k True vx vy t in
      if verbose.val then do {
        printf "normalised:\n";
        printf "%s\n%!" norm_txt;
      }
      else do {
        printf "equation: %s = 0\n\n%!" norm_txt;
      };
      puiseux k kq arg_nb_steps.val vx vy t;
    }
    else do {
      let k = kc () in
      let t = tree_of_ast k vx vy p in
      let t = normalise k t in
      let norm_txt = string_of_tree k True vx vy t in
      if verbose.val then do {
        printf "normalised:\n";
        printf "%s\n%!" norm_txt;
      }
      else do {
        printf "equation: %s = 0\n\n%!" norm_txt;
      };
      puiseux k kq arg_nb_steps.val vx vy t;
    }
  }
  with e →
    match e with
    [ Stream.Error s → do {
        flush stdout;
        eprintf "Syntax error: %s\n%!" s;
        exit 2
      }
    | Poly_lex.Lexer_error s → do {
        flush stdout;
        eprintf "Lexer error: %s\n%!" s;
        exit 2
      }
    | e →
        if arg_debug.val then raise e
        else do {
          flush stdout;
          eprintf "Program internal error: ";
          eprintf "please report or use option '-d'.\n%!";
          exit 2
        } ]
};

if Sys.interactive.val then () else main ();
