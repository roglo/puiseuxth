(* $Id: puiseux.ml,v 1.219 2013-05-19 01:14:25 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

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

Record polynomial α := { al : list α; an : α };

Definition valuation α (ps : puiseux_series α) :=
  match ps.ps_monoms with
  | [mx :: _] => mx.power
  | [] => Q.make (I.of_int 1) (I.of_int 0)
  end
;

Definition valuation_coeff α f (ps : puiseux_series α) :=
  match ps.ps_monoms with
  | [mx :: _] => mx.coeff
  | [] => f.zero
  end
;

type comparison = [ Lt | Eq | Gt ];

value qcompare q₁ q₂ =
  let c = Q.compare q₁ q₂ in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
;

value qnat i = Q.of_i (I.of_int i);

Definition slope_expr pt₁ pt₂ :=
  Q.norm (Qdiv (Qminus (snd pt₂) (snd pt₁)) (Qminus (fst pt₂) (fst pt₁)));

Record min_sl :=
  { slope : Q;
    end_pt : (Q * Q);
    seg : list (Q * Q);
    rem_pts : list (Q * Q) };

Record hull_seg := ahs
  { pt : (Q * Q);
    oth : list (Q * Q) };

Fixpoint minimise_slope pt₁ pt₂ pts₂ :=
  let sl₁₂ := slope_expr pt₁ pt₂ in
  match pts₂ with
  | [] =>
      {| slope := sl₁₂; end_pt := pt₂; seg := []; rem_pts := [] |}
  | [pt₃ :: pts₃] =>
      let ms := minimise_slope pt₁ pt₃ pts₃ in
      match Qcompare sl₁₂ (slope ms) with
      | Eq =>
          {| slope := slope ms; end_pt := end_pt ms; seg := [pt₂ :: seg ms];
             rem_pts := rem_pts ms |}
      | Lt =>
          {| slope := sl₁₂; end_pt := pt₂; seg := []; rem_pts := pts₂ |}
      | Gt =>
          ms
      end
  end;

Fixpoint next_ch_points n pts :=
  match n with
  | O => []
  | S n =>
      match pts with
      | [] => []
      | [pt₁] => [{| pt := pt₁; oth := [] |}]
      | [pt₁; pt₂ :: pts₂] =>
          let ms := minimise_slope pt₁ pt₂ pts₂ in
          let hsl := next_ch_points n [end_pt ms :: rem_pts ms] in
          [{| pt := pt₁; oth := seg ms |} :: hsl]
      end
  end;

Definition lower_convex_hull_points pts :=
  next_ch_points (List.length pts) pts;

Fixpoint list_map_pairs (f : α → α → β) l :=
  match l with
  | [] => []
  | [x₁] => []
  | [x₁ :: ([x₂ :: l₂] as l₁)] => [f x₁ x₂ :: list_map_pairs f l₁]
  end;

Record newton_segment := mkns
  { γ : Q;
    β : Q;
    ini_pt : (Q * Q);
    fin_pt : (Q * Q);
    oth_pts : list (Q * Q) };

Fixpoint all_points_of_ps_polynom α pow psl (psn : puiseux_series α) :=
  match psl with
  | [ps₁ :: psl₁] =>
      [(Qnat pow, ps₁) :: all_points_of_ps_polynom α (S pow) psl₁ psn]
  | [] =>
      [(Qnat pow, psn)]
  end;

Fixpoint filter_non_zero_ps α fld (dpl : list (Q * puiseux_series α)) :=
  match dpl with
  | [(pow, ps) :: dpl₁] =>
      if ps.ps_monoms = [] then filter_non_zero_ps α fld dpl₁
      else [(pow, valuation α ps) :: filter_non_zero_ps α fld dpl₁]
  | [] =>
      []
  end;

Definition points_of_ps_polynom_gen α fld pow cl cn :=
  filter_non_zero_ps α fld (all_points_of_ps_polynom α pow cl cn);

Definition points_of_ps_polynom α fld pol :=
  points_of_ps_polynom_gen α fld 0%nat (al pol) (an pol);

Definition newton_segment_of_pair hsj hsk :=
  let αj := snd (pt hsj) in
  let αk := snd (pt hsk) in
  let γ :=
    Q.norm (Q.div (Q.sub αj αk) (Q.sub (fst (pt hsk)) (fst (pt hsj))))
  in
  let β := Q.norm (Q.add αj (Q.mul (fst (pt hsj)) γ)) in
  mkns γ β (pt hsj) (pt hsk) (oth hsj);

Definition newton_segments α fld pol :=
  let gdpl := points_of_ps_polynom α fld pol in
  list_map_pairs newton_segment_of_pair (lower_convex_hull_points gdpl);

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
    cγl : list (α * Q);
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
    | [x :: l] → [x :: list_take (n-1) l]
    | [] → []
    end
;

value norm f k x y = k.normalise (f x y);

value apply_poly_x_pol k pol =
  apply_poly {ps_monoms = []}
    (fun ps → ps_add (norm k.add k) (k.eq k.zero) ps)
    (ps_mul (norm k.add k) (norm k.mul k) (k.eq k.zero)) pol
;

value apply_poly_xy_pol k pol =
  apply_poly
    {ml = []}    
    (fun pol ps →
       pol_add (ps_add k.add (k.eq k.zero)) pol {ml = [ps]})
    (pol_mul
       {ps_monoms = []}
       (ps_add k.add (k.eq k.zero))
       (ps_mul k.add (norm k.mul k) (k.eq k.zero))
       (fun ps → ps.ps_monoms = []))
    pol
;

value map_polynom k f pol =
  let al =
    List.map
      (fun ps →
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
            [] ps.ps_monoms
         in
         {ps_monoms = List.rev rev_ml})
      pol.ml
  in
  {ml = al}
;

value xy_float_round_zero k pol =
  map_polynom k (fun k c → k.float_round_zero c) pol
;

value float_round_zero k ps =
  let ml =
    List.fold_left
      (fun ml m →
         let c = k.float_round_zero m.coeff in
         if k.eq c k.zero then ml
         else
           let m = {coeff = c; power = m.power} in
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

value pofp p = {ml = p.al @ [p.an]};
value ptop p =
  match List.rev p.ml with
  | [] → failwith "ptop"
  | [m :: ml] → {al = List.rev ml; an = m}
  end
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
  | Some nb_terms →
      let ps = apply_poly_x_pol k (pofp br.initial_polynom) sol in
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
  | None → ()
  end
};

value cancel_pol_constant_term_if_any k pol =
  match pol.ml with
  | [] → pol
  | [m :: ml] →
      match m.ps_monoms with
      [ [m₁ :: ml₁] →
          if Q.eq m₁.power Q.zero then do {
            if verbose.val then
              printf "Warning: cancelling constant term: %s\n%!"
                (k.to_string m₁.coeff)
            else ();
            let m = {ps_monoms = ml₁} in
            {ml = [m :: ml]}
          }
          else pol
      | [] → pol ]
  end
;

value pol_div_x_power pol p =
  let ml =
    List.map
      (fun ps →
         let ml =
           List.map
             (fun m →
                {coeff = m.coeff; power = Q.norm (Q.sub m.power p)})
             ps.ps_monoms
         in
         {ps_monoms = ml})
      pol.ml
  in
  {ml = ml}
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
         ([{coeff = c; power = γsum} :: sol], γsum))
      ([], Q.zero) (List.rev cγl)
  in
  {ps_monoms = List.rev rev_sol}
;

value zero_is_root pol =
  match pol.ml with
  [ [ps :: _] → ps.ps_monoms = []
  | [] → False ]
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
  let pol =
    let y =
      {ml =
         [{ps_monoms = [{coeff = r; power = γ}]};
          {ps_monoms = [{coeff = k.one; power = γ}]}]}
    in
    let pol = apply_poly_xy_pol k (pofp br.pol) y in
    let pol = pol_div_x_power pol β in
    let pol = cancel_pol_constant_term_if_any k pol in
    xy_float_round_zero k pol
  in
  if verbose.val then
    let s = string_of_ps_polyn k True br.vx br.vy pol in
    let s = cut_long True s in
    printf "  %s\n%!" s
  else ();
  let finite = zero_is_root pol in
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
  else if br.rem_steps > 0 then Right (pol, cγl)
  else Left sol_list
};

value ti q = I.to_int (Q.rnum q);

Fixpoint list_nth n l default :=
  match n with
  | 0 => match l with
         | [] => default
         | [x :: _] => x
         end
  | S m => match l with
           | [] => default
           | [_ :: t] => list_nth m t default
           end
  end;

Definition characteristic_polynomial α fld pol ns :=
  let j := ti (fst ns.ini_pt) in
  let k := ti (fst ns.fin_pt) in
  let fix loop deg dpl :=
    match dpl with
    | [] =>
        if k - j > deg then
          [fld.zero :: loop (deg + 1) []]
        else
          let kps := list_nth k pol.al pol.an in
          [(valuation_coeff α fld kps)]
    | [(x, y) :: dpl₁] =>
        let hdeg := ti x in
        if hdeg - j > deg then
          [fld.zero :: loop (deg + 1) dpl]
        else
          let ps := list_nth hdeg pol.al pol.an in
          let c := valuation_coeff α fld ps in
          [c :: loop (deg + 1) dpl₁]
    end
  in
  let cl := loop 1 ns.oth_pts in
  let jps := list_nth j pol.al pol.an in
  {| ml := [valuation_coeff α fld jps :: cl] |}
;

value rec puiseux_branch af br sol_list ns =
  let γ = ns.γ in
  let β = ns.β in
  let (j, αj) = ns.ini_pt in
  let (k, αk) = ns.fin_pt in
  let j = ti j in
  let k = ti k in
  let dpl = ns.oth_pts in
  let f = af.ac_field in
  let ss = inf_string_of_string (string_of_int br.step) in
  let q = List.fold_left (fun q h → gcd q (ti (fst h) - j)) (k - j) dpl in
  let _ =
    if verbose.val then do {
      printf "γ%s = %-4s" ss (Q.to_string γ);
      printf "  β%s = %-3s" ss (Q.to_string β);
      printf "  %d pts" (List.length dpl + 2);
      printf "  j%s=%d" ss j;
      printf "  k%s=%d" ss k;
      printf "  q%s=%d" ss q;
      printf "\n%!";
    }
    else ()
  in
  let pol = characteristic_polynomial () f br.pol ns in
  let rl = af.ac_roots pol in
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
           [ Right (pol, cγl) → next_step af br sol_list pol cγl
           | Left sol_list → sol_list ])
      sol_list rl

and next_step k br sol_list pol cγl =
  let gbl = newton_segments () () (ptop pol) in
  let gbl_f = List.filter (fun ns → not (Q.le (γ ns) Q.zero)) gbl in
  if gbl_f = [] then do {
    if verbose.val then do {
      List.iter
        (fun ns →
           printf "γ %s β %s\n%!" (Q.to_string (γ ns)) (Q.to_string (β ns)))
        gbl
    }
    else ();
    failwith "no strictly positive γ value"
  }
  else
    let pol = ptop pol in
    List.fold_left
      (fun sol_list ns → do {
         if verbose.val then printf "\n%!" else ();
         let br =
           {initial_polynom = br.initial_polynom;
            cγl = cγl; step = br.step + 1;
            rem_steps = br.rem_steps - 1;
            vx = br.vx; vy = br.vy; pol = pol}
         in
         puiseux_branch k br sol_list ns
       })
      sol_list gbl_f
;

value print_line_equal () =
  if verbose.val then
    printf "\n============================================================\n"
  else ()
;

value puiseux k nb_steps vx vy pol =
  let gbl = newton_segments () () pol in
  if gbl = [] then failwith "no finite γ value"
  else
    let rem_steps = nb_steps - 1 in
    let rev_sol_list =
      List.fold_left
        (fun sol_list gbdpl → do {
           print_line_equal ();
           let br =
             {initial_polynom = pol; cγl = []; step = 1;
              rem_steps = rem_steps; vx = vx; vy = vy; pol = pol}
           in
           puiseux_branch k br sol_list gbdpl
         })
        [] gbl
    in
(*
    List.iter
      (fun (pol, finite) →
         printf "sol %s%s\n%!" (airy_string_of_puiseux_series k True "x" pol)
           (if finite then "" else " + ..."))
      (List.rev _rev_sol_list)
*)
    List.rev rev_sol_list
;

value is_zero_tree k =
  fun
  [ Const c → k.eq k.zero c
  | _ → False ]
;

value polyn_of_tree k t =
  let pol = tree_polyn_of_tree k t in
  {ml =
     List.map
       (fun t →
          if is_zero_tree k t then {ps_monoms = []}
          else puiseux_series_of_tree k t)
       pol.ml}
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

value ps_of_int k i =
  {ps_monoms = [{coeff = k.of_i (I.of_int i); power = Q.zero}]}
;

value k_ps k =
  let fc =
    let f = k.ac_field in
    let zero = ps_of_int f 0 in
    let one = ps_of_int f 1 in
    let sub = ps_add (norm f.sub f) (f.eq f.zero) in
    let neg = sub zero in
    {zero = zero; one = one;
     add = ps_add (norm f.add f) (f.eq f.zero);
     sub = sub; neg = neg;
     mul = ps_mul f.add (norm f.mul f) (f.eq f.zero);
     div _ = failwith "k_ps.div not impl";
     minus_one = neg one;
     compare _ = failwith "k_ps.compare not impl";
     eq _ = failwith "k_ps.eq not impl";
     gcd _ = failwith "k_ps.gcd not impl";
     normalise _ = failwith "k_ps.normalise not impl";
     nth_root _ = failwith "k_ps.nth_root not impl";
     neg_factor _ = failwith "k_ps.neg_factor not impl";
     of_i _ = failwith "k_ps.of_i not impl";
     of_q _ = failwith "k_ps.of_q not impl";
     of_a _ = failwith "k_ps.of_a not impl";
     of_complex _ = failwith "k_ps.of_complex not impl";
     of_float_string _ = failwith "k_ps.of_float_string not impl";
     to_q _ = failwith "k_ps.to_q not impl";
     to_a _ = failwith "k_ps.to_a not impl";
     to_complex _ = failwith "k_ps.to_complex not impl";
     to_string _ = failwith "k_ps.to_string arg_lang.val not impl";
     float_round_zero _ = failwith "k_ps.float_round_zero not impl";
     complex_round_zero _ = failwith "k_ps.complex_round_zero not impl";
     complex_mul _ = failwith "k_ps.complex_mul not impl";
     cpoly_roots _ = failwith "k_ps.cpoly_roots not impl";
     complex_to_string _ = failwith "k_ps.complex_to_string not impl"}
  in
  let roots pol =
    let rl = puiseux k 5 "x" "y" (ptop pol) in
    List.map (fun (r, inf) → (r, 0)) rl
  in
  {ac_field = fc; ac_roots = roots}
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
    let (vx, more) =
      match vl_no_y with
      [ [vx] → (vx, [])
      | [] → (if vy = "x" then "y" else "x", [])
      | [vx; v] → (vx, [v])
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
    match more with
    [ [] →
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
          let _ : list _ = puiseux k arg_nb_steps.val vx vy (ptop pol) in
          ()
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
          let _ : list _ = puiseux k arg_nb_steps.val vx vy (ptop pol) in
          ()
        }
    | [_] → do {
        let k = k_ps (kc ()) in
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
        let _ : list _ = puiseux k arg_nb_steps.val vx vy (ptop pol) in
        ()
      }
    | [_; _ :: _] →
        match () with [] ]
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
