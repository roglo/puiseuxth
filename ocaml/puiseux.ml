(* $Id: puiseux.ml,v 1.8 2013-03-28 20:10:11 deraugla Exp $ *)

open Printf;
open Pnums;
open Field;
open Poly_parse;
open Poly_print;
open Poly_tree;
open Roots;

value valuation k t =
  let tnl = const_pow_list_x k t in
  match tnl with
  [ [(_, n) :: _] → n
  | [] → match () with [] ]
;

value valuation_coeff k t =
  let tnl = const_pow_list_x k t in
  match tnl with
  [ [(t, n) :: _] → t
  | [] → match () with [] ]
;

type slope_to α = { xy₂ : (α * α); slope : α; skip : int };

value rec minimise_slope (x₁, y₁) slt_min₁ skip₁ =
  fun
  [ [(x₂, y₂) :: xyl₂] →
      let sl₁₂ = Q.norm (Q.div (Q.sub y₂ y₁) (Q.sub x₂ x₁)) in
      let slt_min =
        if Q.le sl₁₂ slt_min₁.slope then
          {xy₂ = (x₂, y₂); slope = sl₁₂; skip = skip₁}
        else
          slt_min₁
      in
      minimise_slope (x₁, y₁) slt_min (succ skip₁) xyl₂
  | [] →
      slt_min₁ ]
;

value rec next_points rev_list nb_pts_to_skip (x₁, y₁) =
  fun
  [ [(x₂, y₂) :: xyl₂] →
      match nb_pts_to_skip with
      [ 0 →
          let slt_min =
            let sl₁₂ = Q.norm (Q.div (Q.sub y₂ y₁) (Q.sub x₂ x₁)) in
            let slt_min = {xy₂ = (x₂, y₂); slope = sl₁₂; skip = 0} in
            minimise_slope (x₁, y₁) slt_min 1 xyl₂
          in
          next_points [slt_min.xy₂ :: rev_list] slt_min.skip slt_min.xy₂ xyl₂
      | n →
          next_points rev_list (n - 1) (x₁, y₁) xyl₂ ]
  | [] →
      List.rev rev_list ]
;

value lower_convex_hull xyl =
  match xyl with
  [ [xy₁ :: xyl₁] → [xy₁ :: next_points [] 0 xy₁ xyl₁]
  | [] → [] ]
;

value gamma_beta_list_of_lower_convex_hull =
  loop [] where rec loop rev_gbl =
    fun
    [ [(x₁, y₁) :: xyl₁] →
        match xyl₁ with
        [ [(x₂, y₂) :: xyl₂] →
            let γ = Q.norm (Q.div (Q.sub y₂ y₁) (Q.sub x₁ x₂)) in
            let β = Q.norm (Q.add (Q.mul γ x₁) y₁) in
            loop [(γ, β) :: rev_gbl] xyl₁
        | [] →
            List.rev rev_gbl ]
    | [] →
        List.rev rev_gbl ]
;

value gamma_beta_list (k : field _) t =
  let tnl = tree_pow_list_y k t in
  let xyl =
    List.map (fun (ai, i) → (Q.of_i (I.of_int i), valuation k ai)) tnl
  in
  let ch = lower_convex_hull xyl in
  gamma_beta_list_of_lower_convex_hull ch
;

value zero_is_root =
  fun
  [ [(_, n) :: _] → n > 0
  | [] → False ]
;

value start_red = "\027[31m";
value end_red = "\027[m";

value xpower r = Xpower (I.to_int (Q.rnum r)) (I.to_int (Q.rden r));

value rebuild_add_list_x k cpl =
  let rebuild_add t (c₁, p₁) =
    if C.eq c₁ C.zero then t
    else
       let t₁ =
         if Q.eq p₁ Q.zero then Const c₁
         else
           let xp = xpower p₁ in
           if C.eq c₁ C.one then xp
           else if C.eq c₁ C.minus_one then Neg xp
           else Mult (Const c₁) xp
       in
       let t₁ =
         match without_initial_neg k t₁ with
         [ Some t₁ → Neg t₁
         | None → t₁ ]
       in
       let t_is_null =
         match t with
         [ Const c → C.eq c C.zero
         | _ → False ]
       in
       if t_is_null then t₁
       else
         match without_initial_neg k t₁ with
         [ Some t₁ → Minus t t₁
         | None → Plus t t₁ ]
  in
  List.fold_left rebuild_add (Const C.zero) cpl
;

value arg_polynom = ref None;
value arg_y = ref "y";
value arg_fname = ref "";
value arg_nb_steps = ref 5;
value arg_lang = ref False;
value arg_debug = ref False;
value arg_end = ref False;

value print_solution k vx vy finite nth cγl =
  let (rev_sol, _) =
    List.fold_left
      (fun (sol, γsum) (c, γ) →
         let γsum = Q.norm (Q.add γsum γ) in
         ([(c, γsum) :: sol], γsum))
      ([], Q.zero) (List.rev cγl)
  in
  let sol = rebuild_add_list_x k (List.rev rev_sol) in
  printf "solution: %s%s%s = %s%s%s\n%!"
    (if not quiet.val then start_red else "") vy
    (inf_string_of_string (soi nth))
    (airy_string_of_tree k (not arg_lang.val) vx vy sol)
    (if finite then "" else " + ...")
    (if not quiet.val then end_red else "")
;

value cancel_constant_term_if_any k t =
  match Poly_tree.flatten t [] with
  [ [t₁ :: tl₁] →
      let td = term_descr_of_term k t₁ in
      if Q.eq td.xpow Q.zero && td.ypow = 0 then do {
        if not quiet.val then
          printf "Warning: cancelling constant term: %s\n%!"
            (C.to_string False td.const)
        else ();
        match tl₁ with
        [ [t₂ :: tl₂] → List.fold_left (fun t₁ t₂ → Plus t₁ t₂) t₂ tl₂
        | [] → t₁ ]
      }
      else t
  | [] → t ]
;

type branch α =
  { cγl : list (α * Q.t);
    step : int;
    rem_steps : int;
    vx : string;
    vy : string;
    t : tree α;
    tnl : list (tree α * int) }
;

value puiseux_iteration k br r m γ β nth_sol = do {
  let ss = inf_string_of_string (string_of_int br.step) in
  if not quiet.val then
    printf "\nc%s = %s  r%s = %d\n\n%!" ss (C.to_string False r) ss m
  else ();
  let y =
    let cpy = Plus (Const r) (Ypower 1) in
    if I.eq (Q.rnum γ) I.zero then cpy
    else Mult (xpower γ) cpy
  in
  let xmβ = xpower (Q.neg β) in
  let ss₁ = inf_string_of_string (string_of_int (br.step - 1)) in
  if not quiet.val then
    printf "f%s(%s,%s) = %sf%s(%s,%s) =\n%!" ss br.vx br.vy
      (string_of_tree k True br.vx br.vy xmβ)
      (if br.step = 1 then "" else ss₁) br.vx
      (string_of_tree k True br.vx br.vy y)
  else ();
  let t = substitute_y k y br.t in
  let t = Mult xmβ t in
(*
let _ = printf "t = %s\n%!" (string_of_tree True "x" "y" t) in
*)
  let cγl = [(r, γ) :: br.cγl] in
  match try Some (normalize k t) with [ Overflow → None ] with
  [ Some t → do {
      if not quiet.val then
        let s = string_of_tree k True br.vx br.vy t in
        let s =
          if cut_long_strings.val then
            let len = utf8_strlen s in
            if len > 73 then
              sprintf "%s ... %s" (utf8_sub_string s 0 35)
                (utf8_sub_string s (len - 35) 35)
            else s
          else s
        in
        printf "  %s\n%!" s
      else ();
      let t = cancel_constant_term_if_any k t in
      let tnl = tree_pow_list_y k t in
      let finite = zero_is_root tnl in
      if br.rem_steps = 0 || finite then do {
        if not quiet.val then do {
          printf "\n";
          if finite then printf "zero is root !\n%!" else ();
        }
        else (); 
        incr nth_sol;
        print_solution k br.vx br.vy finite nth_sol.val cγl;
        None
      }
      else if br.rem_steps > 0 then Some (t, cγl)
      else None
    }
  | None → do {
      if not quiet.val then do {
        printf "\noverflow!\n";
        printf "displaying solution up to previous step\n";
        printf "\n%!";
      }
      else ();
      incr nth_sol;
      print_solution k br.vx br.vy False nth_sol.val cγl;
      None
    } ]
};

value rec puiseux_branch k br nth_sol (γ, β) =
  let ss = inf_string_of_string (string_of_int br.step) in
  let hl =
    List.filter
      (fun (ai, i) →
         let αi = valuation k ai in
         let βi = Q.norm (Q.add (Q.muli γ (I.of_int i)) αi) in
         Q.eq β βi)
      br.tnl
  in
  let j = snd (List.hd hl) in
  let q = List.fold_left (fun q (ah, h) → gcd q (h - j)) 0 hl in
  let _ =
    if not quiet.val then do {
      printf "γ%s = %-4s" ss (Q.to_string γ);
      printf "  β%s = %-3s" ss (Q.to_string β);
      printf "  %d pts" (List.length hl);
      printf "  j%s=%d" ss j;
      printf "  q%s=%d" ss q;
      printf "\n%!";
    }
    else ()
  in
  let cpl = List.rev_map (fun (ah, h) → (valuation_coeff k ah, h - j)) hl in
  let rl = roots k cpl in
  if rl = [] then do {
    incr nth_sol;
    print_solution k br.vx br.vy False nth_sol.val br.cγl;
  }
  else
    List.iter
      (fun (r, m) →
         if C.eq r C.zero then ()
         else
           match puiseux_iteration k br r m γ β nth_sol with
           [ Some (t, cγl) → next_step k br nth_sol t cγl
           | None → () ])
      rl

and next_step k br nth_sol t cγl =
  let gbl = gamma_beta_list k t in
  let tnl = tree_pow_list_y k t in
  let gbl_f = List.filter (fun (γ, β) → not (Q.le γ Q.zero)) gbl in
  if gbl_f = [] then do {
    if not quiet.val then do {
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
         if not quiet.val then printf "\n%!" else ();
         let br =
           {cγl = cγl; step = br.step + 1;
            rem_steps = br.rem_steps - 1;
            vx = br.vx; vy = br.vy; t = t; tnl = tnl}
         in
         puiseux_branch k br nth_sol (γ, β)
       })
      gbl_f
;

value print_line_equal () =
  if not quiet.val then
    printf "\n============================================================\n"
  else ()
;

value puiseux k nb_steps vx vy t =
  let gbl = gamma_beta_list k t in
  let tnl = tree_pow_list_y k t in
  let rem_steps = nb_steps - 1 in
  let nth_sol = ref 0 in
  List.iter
    (fun (γ₁, β₁) → do {
       print_line_equal ();
       let br =
         {cγl = []; step = 1; rem_steps = rem_steps; vx = vx; vy = vy;
          t = t; tnl = tnl}
       in
       puiseux_branch k br nth_sol (γ₁, β₁)
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
    else if List.mem Sys.argv.(i) ["--prog-lang"; "-l"] then do {
      arg_lang.val := True;
      loop (i + 1)
    }
    else if List.mem Sys.argv.(i) ["--with-sqrt-x"; "-w"] then do {
      with_sqrt_x.val := True;
      loop (i + 1)
    }
    else if List.mem Sys.argv.(i) ["--verbose"; "-v"] then do {
      quiet.val := False;
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
      eprintf "-y, --y-var <char>    Name of y variable\n";
      eprintf "-f, --file <name>     Read polynomial in file, 1 monom/line\n";
      eprintf "-n, --nb-steps <num>  Number of steps (default: 5)\n";
      eprintf "-v, --verbose         Display computation details\n";
      eprintf "-l, --prog-lang       Display prog lang style with *, ^\n";
      eprintf "-w, --with-sqrt-x     Display x¹ᐟ² and x¹ᐟ³ as √x and ∛x\n";
      eprintf "-c, --cut-long        Cut too long lines in verbose mode\n";
      eprintf "-d, --debug           Debug mode\n";
      eprintf "-h, --help            Display this list of options\n";
      eprintf "--                    End of options\n";
      eprintf "--version             Display version and exit\n";
      eprintf "\n";
      eprintf "If the polynomial starts with '-', use a leading space.\n%!";
      eprintf "E.g. write it ' -x+2xy' instead of '-x+2xy'.\n%!";
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
    if not quiet.val then do {
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
    let k =
      let imul i a = C.muli a (I.of_int i) in
      {zero = C.zero; one = C.one; add = C.add; sub = C.add; neg = C.neg;
       mul = C.mul; div = C.div; minus_one = C.minus_one; eq = C.eq;
       imul = imul; norm = C.norm; neg_factor = C.neg_factor;
       of_i = C.of_i; to_string = C.to_string arg_lang.val}
    in
    let t = tree_of_ast k vx vy p in
    let t = normalize k t in
    let norm_txt = string_of_tree k True vx vy t in
    if not quiet.val then do {
      printf "normalized:\n";
      printf "%s\n%!" norm_txt;
    }
    else do {
      printf "equation: %s = 0\n\n%!" norm_txt;
    };
    puiseux k arg_nb_steps.val vx vy t;
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
