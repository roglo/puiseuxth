(* $Id: puiseux.ml,v 1.142 2013-04-06 18:01:22 deraugla Exp $ *)

#load "./pa_coq.cmo";

open Printf;
open Pnums;
open Field;
open Poly_parse;
open Poly_print;
open Poly_tree;
open Poly;
open Puiseux_series;
open Roots;

type slope_to α = { xy₂ : (α * α); slope : α; skip : int };

Fixpoint minimise_slope xy₁ xy_min sl_min sk_min skip₁ xyl :=
  let (x₁, y₁) := (xy₁ : (Q.t * Q.t)) in
  match xyl with
  | [(x₂, y₂) :: xyl₂] =>
      let sl₁₂ := Q.norm (Q.div (Q.sub y₂ y₁) (Q.sub x₂ x₁)) in
      if Q.le sl₁₂ sl_min then
        minimise_slope xy₁ (x₂, y₂) sl₁₂ skip₁ (succ skip₁) xyl₂
      else
        minimise_slope xy₁ xy_min sl_min sk_min (succ skip₁) xyl₂
  | [] =>
      (xy_min, sk_min)
  end;

Fixpoint next_points rev_list nb_pts_to_skip xy₁ xyl₁ :=
  let (x₁, y₁) := (xy₁ : (Q.t * Q.t)) in
  match xyl₁ with
  | [(x₂, y₂) :: xyl₂] =>
      match nb_pts_to_skip with
      | 0 =>
          let (xy, skip) :=
           let sl₁₂ := Q.norm (Q.div (Q.sub y₂ y₁) (Q.sub x₂ x₁)) in
            minimise_slope xy₁ (x₂, y₂) sl₁₂ 0 1 xyl₂
          in
          next_points [xy :: rev_list] skip xy xyl₂
      | n =>
          next_points rev_list (n - 1) xy₁ xyl₂
      end
  | [] =>
      List.rev rev_list
  end;

Definition lower_convex_hull xyl :=
  match xyl with
  | [xy₁ :: xyl₁] => [xy₁ :: next_points [] 0 xy₁ xyl₁]
  | [] => []
  end
;

Definition valuation (ps : puiseux_series α) :=
  match ps.ps_monoms with
  | [mx :: _] => mx.power₂
  | [] => match () with end
  end
;

Definition valuation_coeff k (ps : puiseux_series α) :=
  match ps.ps_monoms with
  | [mx :: _] => mx.coeff₂
  | [] => match () with end
  end
;

Definition gamma_beta_list (pol : polynomial (puiseux_series α)) :=
  let xyl :=
    let (rev_xyl, _) :=
      List.fold_left
        (fun (rev_xyl, deg) ps →
           let rev_xyl =
             if ps.ps_monoms = [] then rev_xyl
             else [(Q.of_i (I.of_int deg), valuation ps) :: rev_xyl]
           in
           (rev_xyl, deg + 1))
        ([], 0) pol.al
    in
    List.rev rev_xyl
  in
  let fix loop rev_gbl xyl :=
    match xyl with
    | [(x₁, y₁) :: ([(x₂, y₂) :: _] as xyl₁)] =>
        let γ := Q.norm (Q.div (Q.sub y₂ y₁) (Q.sub x₁ x₂)) in
        let β := Q.norm (Q.add (Q.mul γ x₁) y₁) in
        loop [(γ, β) :: rev_gbl] xyl₁
    | [_] | [] =>
        List.rev rev_gbl
    end
  in
  let ch := lower_convex_hull xyl in
  loop [] ch
;

value zero_is_root opol =
  match opol.monoms with
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

type branch α =
  { initial_polynom : polynomial (puiseux_series α);
    cγl : list (α * Q.t);
    step : int;
    rem_steps : int;
    vx : string;
    vy : string;
    pol : polynomial (puiseux_series α) }
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

value norm f k x y = k.normalise (f x y);

value apply_poly_x_pol k pol =
  apply_poly {ps_monoms = []}
    (fun ps → ps_add (norm k.add k) (k.eq k.zero) ps)
    (ps_mul (norm k.add k) (norm k.mul k) (k.eq k.zero)) pol
;

value apply_poly_xy_pol k pol =
  apply_poly
    {al = []}    
    (fun pol ps →
       pol_add
         {ps_monoms = []}
         (ps_add k.add (k.eq k.zero))
         (fun ps → ps.ps_monoms = [])
         pol
         {al = [ps]})
    (pol_mul
       {ps_monoms = []}
       (ps_add k.add (k.eq k.zero))
       (ps_mul k.add (norm k.mul k) (k.eq k.zero))
       (fun ps → ps.ps_monoms = []))
    pol
;

value map_old_polynom k f opol =
  let rev_ml =
    List.fold_left
      (fun rev_ml m →
         let c =
           let rev_ml =
             List.fold_left
               (fun rev_ml m →
                  let c = f k m.coeff₂ in
                  if k.eq c k.zero then do {
                    if verbose.val then do {
                      printf "Warning: cancelling small coefficient: %s\n%!"
                        (k.to_string m.coeff₂)
                    }
                    else ();
                    rev_ml
                  }
                  else [m :: rev_ml])
               [] m.coeff.ps_monoms
           in
           {ps_monoms = List.rev rev_ml}
         in
         if c.ps_monoms = [] then rev_ml
         else
           let m = {coeff = c; power = m.power} in
           [m :: rev_ml])
       [] opol.monoms
  in
  {monoms = List.rev rev_ml}
;

value xy_float_round_zero k pol =
  let opol = op_of_p (fun ps → ps.ps_monoms = []) pol in
  map_old_polynom k (fun k c → k.float_round_zero c) opol
;

value float_round_zero k ps =
  let ml =
    List.fold_left
      (fun ml m →
         let c = k.float_round_zero m.coeff₂ in
         if k.eq c k.zero then ml
         else
           let m = {coeff₂ = c; power₂ = m.power₂} in
           [m :: ml])
       [] ps.ps_monoms
  in
  {ps_monoms = List.rev ml}
;

value string_of_puiseux_series k opt vx ps =
  let t = tree_of_puiseux_series k ps in
  string_of_tree k opt vx "?" t
;

value airy_string_of_puiseux_series k opt vx pol =
  let t = tree_of_puiseux_series k pol in
  airy_string_of_tree k opt vx "?" t
;

value string_of_ps_polyn k opt vx vy pol =
  let t = tree_of_ps_polyn k pol in
  string_of_tree k opt vx vy t
;

value print_solution k br nth cγl finite sol = do {
  let inf_nth = inf_string_of_string (soi nth) in
  printf "solution: %s%s%s = %s%s%s\n%!"
    (if arg_eval_sol.val <> None || verbose.val then start_red else "")
    br.vy inf_nth
    (airy_string_of_puiseux_series k (not arg_lang.val) br.vx sol)
    (if finite then "" else " + ...")
    (if arg_eval_sol.val <> None || verbose.val then end_red else "");
  match arg_eval_sol.val with
  [ Some nb_terms →
      let ps = apply_poly_x_pol k br.initial_polynom sol in
      let ps = float_round_zero k ps in
      let ps₂ =
        if nb_terms > 0 then {ps_monoms = list_take nb_terms ps.ps_monoms}
        else ps
      in
      let ellipses =
        if nb_terms = 0 then ""
        else if List.length ps.ps_monoms > nb_terms then " + ..."
        else ""
      in
      printf "f(%s,%s%s) = %s%s\n\n%!" br.vx br.vy inf_nth
        (string_of_puiseux_series k (not arg_lang.val) br.vx ps₂)
        ellipses
  | None → () ]
};

value cancel_pol_constant_term_if_any k pol =
  let opol = op_of_p (fun ps → ps.ps_monoms = []) pol in
  match opol.monoms with
  [ [m :: ml] →
      if m.power = 0 then
        match m.coeff.ps_monoms with
        [ [m₁ :: ml₁] →
            if Q.eq m₁.power₂ Q.zero then do {
              if verbose.val then
                printf "Warning: cancelling constant term: %s\n%!"
                  (k.to_string m₁.coeff₂)
              else ();
              let p₁ = {ps_monoms = ml₁} in
              let m = {coeff = p₁; power = m.power} in
              p_of_op {ps_monoms = []} {monoms = [m :: ml]}
            }
            else pol
        | [] → pol ]
      else pol
  | [] → pol ]
;

value pol_div_x_power pol p =
  let opol = op_of_p (fun ps → ps.ps_monoms = []) pol in
  let ml =
    List.map
      (fun pol →
         let ml =
           List.map
             (fun m →
                {coeff₂ = m.coeff₂; power₂ = Q.norm (Q.sub m.power₂ p)})
             pol.coeff.ps_monoms
         in
         {coeff = {ps_monoms = ml}; power = pol.power})
      opol.monoms
  in
  p_of_op {ps_monoms = []} {monoms = ml}
;

type choice α β =
  [ Left of α
  | Right of β ]
;

value make_solution cγl =
  let (rev_sol, _) =
    List.fold_left
      (fun (sol, γsum) (c, γ) →
         let γsum = Q.norm (Q.add γsum γ) in
         ([{coeff₂ = c; power₂ = γsum} :: sol], γsum))
      ([], Q.zero) (List.rev cγl)
  in
  {ps_monoms = List.rev rev_sol}
;

value puiseux_iteration k br r m γ β sol_list = do {
  if verbose.val then do {
    let ss = inf_string_of_string (string_of_int br.step) in
    printf "\nc%s = %s  r%s = %d\n\n%!" ss (k.to_string r) ss m;
    let y =
      let cpy = Plus (Const r) (Ypower 1) in
      if I.eq (Q.rnum γ) I.zero then cpy
      else Mult (xpower γ) cpy
    in
    let xmβ = xpower (Q.neg β) in
    let ss₁ = inf_string_of_string (string_of_int (br.step - 1)) in
    printf "f%s(%s,%s) = %sf%s(%s,%s) =\n%!" ss br.vx br.vy
      (string_of_tree k True br.vx br.vy xmβ)
      (if br.step = 1 then "" else ss₁) br.vx
      (string_of_tree k True br.vx br.vy y)
  }
  else ();
  let opol =
    let y =
      {monoms =
         [{coeff = {ps_monoms = [{coeff₂ = r; power₂ = γ}]}; power = 0};
          {coeff = {ps_monoms = [{coeff₂ = k.one; power₂ = γ}]}; power = 1}]}
    in
    let y = p_of_op {ps_monoms = []} y in
    let pol = apply_poly_xy_pol k br.pol y in
    let pol = pol_div_x_power pol β in
    let pol = cancel_pol_constant_term_if_any k pol in
    xy_float_round_zero k pol
  in
  if verbose.val then
    let pol = p_of_op {ps_monoms = []} opol in
    let s = string_of_ps_polyn k True br.vx br.vy pol in
    let s = cut_long True s in
    printf "  %s\n%!" s
  else ();
  let finite = zero_is_root opol in
  let cγl = [(r, γ) :: br.cγl] in
  if br.rem_steps = 0 || finite then do {
    if verbose.val then do {
      printf "\n";
      if finite then printf "zero is root !\n%!" else ();
    }
    else ();
    let sol = make_solution cγl in
    print_solution k br (succ (List.length sol_list)) cγl finite sol;
    Left [(sol, finite) :: sol_list]
  }
  else if br.rem_steps > 0 then Right (opol, cγl)
  else Left sol_list
};

value rec puiseux_branch k br sol_list (γ, β) =
  let f = k.ac_field in
  let ss = inf_string_of_string (string_of_int br.step) in
  let hl =
    let (rev_hl, _) =
      List.fold_left
        (fun (rev_hl, deg) c →
           let rev_hl =
             if c.ps_monoms = [] then rev_hl
             else
               let αi = valuation c in
               let βi = Q.norm (Q.add (Q.muli γ (I.of_int deg)) αi) in
               if Q.eq β βi then [(c, deg) :: rev_hl] else rev_hl
           in
           (rev_hl, deg + 1))
        ([], 0) br.pol.al
    in
    List.rev rev_hl
  in
  let j = snd (List.hd hl) in
  let q = List.fold_left (fun q h → gcd q (snd h - j)) 0 hl in
  let _ =
    if verbose.val then do {
      printf "γ%s = %-4s" ss (Q.to_string γ);
      printf "  β%s = %-3s" ss (Q.to_string β);
      printf "  %d pts" (List.length hl);
      printf "  j%s=%d" ss j;
      printf "  k%s=%d" ss (snd (List.hd (List.rev hl)));
      printf "  q%s=%d" ss q;
      printf "\n%!";
    }
    else ()
  in
  let ml =
    List.map
      (fun (c, deg) → {coeff = valuation_coeff f c; power = deg - j})
      hl
  in
  let rl = k.ac_roots (p_of_op f.zero {monoms = ml}) in
  if rl = [] then do {
    let sol = make_solution br.cγl in
    print_solution f br (succ (List.length sol_list)) br.cγl False sol;
    [(sol, False) :: sol_list]
  }
  else
    List.fold_left
      (fun sol_list (r, m) →
         if f.eq r f.zero then sol_list
         else
           match puiseux_iteration f br r m γ β sol_list with
           [ Right (pol, cγl) → next_step k br sol_list pol cγl
           | Left sol_list → sol_list ])
      sol_list rl

and next_step k br sol_list opol cγl =
  let pol = p_of_op {ps_monoms = []} opol in
  let gbl = gamma_beta_list pol in
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
    List.fold_left
      (fun sol_list (γ, β) → do {
         if verbose.val then printf "\n%!" else ();
         let br =
           {initial_polynom = br.initial_polynom;
            cγl = cγl; step = br.step + 1;
            rem_steps = br.rem_steps - 1;
            vx = br.vx; vy = br.vy; pol = pol}
         in
         puiseux_branch k br sol_list (γ, β)
       })
      sol_list gbl_f
;

value print_line_equal () =
  if verbose.val then
    printf "\n============================================================\n"
  else ()
;

value puiseux k nb_steps vx vy pol =
  let gbl = gamma_beta_list pol in
  let rem_steps = nb_steps - 1 in
  let _rev_sol_list =
    List.fold_left
      (fun sol_list (γ₁, β₁) → do {
         print_line_equal ();
         let br =
           {initial_polynom = pol; cγl = []; step = 1;
            rem_steps = rem_steps; vx = vx; vy = vy; pol = pol}
         in
         puiseux_branch k br sol_list (γ₁, β₁)
       })
      [] gbl
  in
  ()
(*
  List.iter
    (fun (pol, finite) →
       printf "sol %s%s\n%!" (airy_string_of_puiseux_series k True "x" pol)
         (if finite then "" else " + ..."))
    (List.rev _rev_sol_list)
*)
;

value is_zero_tree k =
  fun
  [ Const c → k.eq k.zero c
  | _ → False ]
;

value polyn_of_tree k t =
  let pol = tree_polyn_of_tree k t in
  let opol = op_of_p (is_zero_tree k) pol in
  let opol =
    {monoms =
     List.map
       (fun m → {coeff = puiseux_series_of_tree k m.coeff; power = m.power})
       opol.monoms}
  in
  p_of_op {ps_monoms = []} opol
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

value kc () =
  let fc =
    {zero = C.zero; one = C.one; add = C.add; sub = C.sub; neg = C.neg;
     mul = C.mul; div = C.div;
     minus_one = C.minus_one; compare = C.compare; eq = C.eq; gcd = C.gcd;
     normalise = C.normalise; nth_root = C.nth_root; neg_factor = C.neg_factor;
     of_i = C.of_i; of_q = C.of_q; of_a = C.of_a; of_complex = C.of_complex;
     of_float_string = C.of_float_string; to_q = C.to_q; to_a = C.to_a;
     to_complex = C.to_complex; to_string = C.to_string arg_lang.val;
     float_round_zero = C.float_round_zero;
     complex_round_zero = C.complex_round_zero; complex_mul = C.complex_mul;
     cpoly_roots = C.cpoly_roots; complex_to_string = C.complex_to_string}
  in
  {ac_field = fc; ac_roots = roots fc}
;

value km () =
  let fm =
    {zero = M.zero; one = M.one; add = M.add; sub = M.sub; neg = M.neg;
     mul = M.mul; div = M.div;
     minus_one = M.minus_one; compare = M.compare; eq = M.eq; gcd = M.gcd;
     normalise = M.normalise; nth_root = M.nth_root; neg_factor = M.neg_factor;
     of_i = M.of_i; of_q = M.of_q; of_a = M.of_a; of_complex = M.of_complex;
     of_float_string = M.of_float_string; to_q = M.to_q; to_a = M.to_a;
     to_complex = M.to_complex; to_string = M.to_string arg_lang.val;
     float_round_zero = M.float_round_zero;
     complex_round_zero = M.complex_round_zero; complex_mul = M.complex_mul;
     cpoly_roots = M.cpoly_roots; complex_to_string = M.complex_to_string}
  in
  {ac_field = fm; ac_roots = roots fm}
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
      let f = k.ac_field in
      let t = tree_of_ast f vx vy p in
      let t = normalise f t in
      let norm_txt = string_of_tree f True vx vy t in
      if verbose.val then do {
        printf "normalised:\n";
        printf "%s\n%!" norm_txt;
      }
      else do {
        printf "equation: %s = 0\n\n%!" norm_txt;
      };
      let pol = polyn_of_tree f t in
      puiseux k arg_nb_steps.val vx vy pol;
    }
    else do {
      let k = kc () in
      let f = k.ac_field in
      let t = tree_of_ast f vx vy p in
      let t = normalise f t in
      let norm_txt = string_of_tree f True vx vy t in
      if verbose.val then do {
        printf "normalised:\n";
        printf "%s\n%!" norm_txt;
      }
      else do {
        printf "equation: %s = 0\n\n%!" norm_txt;
      };
      let pol = polyn_of_tree f t in
      puiseux k arg_nb_steps.val vx vy pol;
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
