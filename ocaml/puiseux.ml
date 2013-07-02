(* $Id: puiseux.ml,v 1.393 2013-07-02 02:30:12 deraugla Exp $ *)

(* Most of notations are Robert Walker's ones *)

#load "./pa_coq.cmo";

open Printf;

open Pnums;
open Convex_hull;
open Coq;
open Field;
open Old_puiseux_series;
open Poly_parse;
open Poly_print;
open Poly_tree;
open Poly;
open Puiseux_series;
open Roots;
open Series;

type choice α β =
  [ Left of α
  | Right of β ]
;

value pos_to_nat x = x;

Record algeb_closed_field α β :=
  { ac_field : field α;
    ac_roots : polynomial α → list (α * nat) };

Definition degree (pol : polynomial α) := List.length (al pol).

value qnat i = Q.of_i (I.of_int i);
value nofq q =
  let r = I.to_int (Q.rnum q) in
  if r < 0 then 0 else r
;

Fixpoint all_points_of_ps_polynom α pow psl (psn : puiseux_series α) :=
  match psl with
  | [ps₁ … psl₁] =>
      [(Qnat pow, ps₁) … all_points_of_ps_polynom (S pow) psl₁ psn]
  | [] =>
      [(Qnat pow, psn)]
  end.

Fixpoint filter_non_zero_ps α fld (dpl : list (Q * puiseux_series α)) :=
  match dpl with
  | [(pow, ps) … dpl₁] =>
      match valuation fld ps with
      | Some v => [(pow, v) … filter_non_zero_ps fld dpl₁]
      | None => filter_non_zero_ps fld dpl₁
      end
  | [] =>
      []
  end.

Definition points_of_ps_polynom_gen α fld pow cl (cn : puiseux_series α) :=
  filter_non_zero_ps fld (all_points_of_ps_polynom pow cl cn).

Definition points_of_ps_polynom α fld (pol : polynomial (puiseux_series α)) :=
  points_of_ps_polynom_gen fld 0%nat (al pol) (an pol).

(* *)

Record newton_segment := mkns
  { γ : Q;
    β : Q;
    ini_pt : (Q * Q);
    fin_pt : (Q * Q);
    oth_pts : list (Q * Q) };

Fixpoint list_map_pairs α β (f : α → α → β) l :=
  match l with
  | [] => []
  | [x₁] => []
  | [x₁ … ([x₂ … l₂] as l₁)] => [f x₁ x₂ … list_map_pairs f l₁]
  end.

Definition newton_segment_of_pair hsj hsk :=
  let αj := snd (pt hsj) in
  let αk := snd (pt hsk) in
  let γ :=
    Q.norm (Q.div (Q.sub αj αk) (Q.sub (fst (pt hsk)) (fst (pt hsj))))
  in
  let β := Q.norm (Q.add αj (Q.mul (fst (pt hsj)) γ)) in
  mkns γ β (pt hsj) (pt hsk) (oth hsj);

Definition newton_segments α fld (pol : polynomial (puiseux_series α)) :=
  let gdpl := points_of_ps_polynom fld pol in
  list_map_pairs newton_segment_of_pair (lower_convex_hull_points gdpl).

value start_red () = if cut_long_strings.val then "" else "\027[31m";
value end_red () = if cut_long_strings.val then "" else "\027[m";

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

CoFixpoint series_series_take α n (s : series α) :=
  match n with
  | O => End _
  | S n₁ =>
      match s with
      | Term a t => Term a (series_series_take n₁ t)
      | End => End _
      end
  end.

Fixpoint series_take n s :=
  match n with
  | O => []
  | S n₁ =>
      match s with
      | Term x s₁ => [x … series_take n₁ s₁]
      | End => []
      end
  end.

value string_of_old_puiseux_series fld opt cancel_zeroes vx nb_terms ps =
  let ps₂ =
    if nb_terms > 0 then
      ms_of_ps fld
        {ops_terms = series_series_take nb_terms ps.ops_terms;
         ops_comden = ps.ops_comden}
    else
      ms_of_ps fld ps
  in
  let ellipses =
    if nb_terms = 0 then ""
    else if series_nth nb_terms ps.ops_terms <> None then " + ..."
    else ""
  in
  let t = tree_of_puiseux_series fld cancel_zeroes ps₂ in
  string_of_tree fld opt vx "?" t ^ ellipses
;

value airy_string_of_puiseux_series k opt vx ps =
  let t = tree_of_puiseux_series k True ps in
  airy_string_of_tree k opt vx "?" t
;

value string_of_ps_polyn k opt cancel_zeroes vx vy pol =
  let t = tree_of_ps_polyn k cancel_zeroes pol in
  string_of_tree k opt vx vy t
;

Definition apply_poly_with_ps (fld : field α) :=
  apply_poly (λ ps, ps) (ps_add fld) (ps_mul fld).

Definition apply_poly_with_ps_poly α (fld : field α) pol :=
  apply_poly
    (λ ps, {| al := []; an := ps |})
    (λ pol ps, pol_add (ps_add fld) pol {| al := []; an := ps |})
    (pol_mul
       {| ps_terms := End _; ps_valnum := I.zero; ps_comden := I.one |}
       (ps_add fld) (ps_mul fld))
    pol.

Definition float_round_zero fld ps :=
  let ps := ops_of_ms ps in
  let s :=
    let cofix loop s :=
      match s with
      | Term m s₁ =>
          let c := fld.ext.float_round_zero (coeff m) in
          if fld.is_zero c then loop s₁
          else
            Term {coeff = c; power = power m} (loop s₁)
      | End =>
          End
      end
    in
    loop (ops_terms ps)
  in
  {ops_terms = s; ops_comden = ops_comden ps};

value print_solution fld br nth cγl finite sol = do {
  let inf_nth = inf_string_of_string (soi nth) in
  printf "solution: %s%s%s = %s%s%s\n%!"
    (if arg_eval_sol.val <> None || verbose.val then start_red () else "")
    br.vy inf_nth
    (airy_string_of_puiseux_series fld (not arg_lang.val) br.vx sol)
    (if finite then "" else " + ...")
    (if arg_eval_sol.val <> None || verbose.val then end_red () else "");
  match arg_eval_sol.val with
  | Some nb_terms →
      let ps = apply_poly_with_ps fld br.initial_polynom sol in
      let ps = float_round_zero fld ps in
      printf "f(%s,%s%s) = %s\n\n%!" br.vx br.vy inf_nth
        (string_of_old_puiseux_series fld (not arg_lang.val) True br.vx
           nb_terms ps)
  | None → ()
  end
};

Definition mul_x_power_minus α p (ps : puiseux_series α) :=
  {| ps_terms :=
       ps_terms ps;
     ps_valnum :=
       Z.sub (ps_valnum ps) (Qnum (Qmult p (inject_Z (Zpos (ps_comden ps)))));
     ps_comden :=
       ps_comden ps |}.

Definition pol_mul_x_power_minus α p (pol : polynomial (puiseux_series α)) :=
  let cl := List.map (mul_x_power_minus p) (al pol) in
  let cn := mul_x_power_minus p (an pol) in
  {| al := cl; an := cn |}.

value make_solution fld rev_cγl =
  let t =
    loop Q.zero (List.rev rev_cγl) where rec loop γsum cγl =
      match cγl with
      | [] → End
      | [(c, γ) … cγl₁] →
          let γsum = Q.norm (Q.add γsum γ) in
          Term {coeff = c; power = γsum} (loop γsum cγl₁)
      end
  in
  let d =
    loop (List.rev rev_cγl) where rec loop cγl =
      match cγl with
      | [] → I.one
      | [(c, γ) … cγl₁] → I.lcm (Q.rden γ) (loop cγl₁)
      end
  in
  ms_of_ps fld {ops_terms = t; ops_comden = d}
;

Definition zero_is_root α fld (pol : polynomial (puiseux_series α)) :=
  match al pol with
  | [] => false
  | [ps … _] =>
      match series_head (is_zero fld) 0 (ps_terms ps) with
      | Some _ => false
      | None => true
      end
  end.

Definition f₁ α (fld : field α) f β γ c :=
  let y :=
    {| al :=
         [{| ps_terms := Term c (End _);
             ps_valnum := Qnum γ;
             ps_comden := Qden γ |}];
       an :=
         {| ps_terms := Term (one fld) (End _);
            ps_valnum := Qnum γ;
            ps_comden := Qden γ |} |}
  in
  let pol := apply_poly_with_ps_poly fld f y in
  pol_mul_x_power_minus β pol.

Fixpoint list_nth n l default :=
  match n with
  | 0 => match l with
         | [] => default
         | [x … _] => x
         end
  | S m => match l with
           | [] => default
           | [_ … t] => list_nth m t default
           end
  end.

Fixpoint make_char_pol α (fld : field α) cdeg dcl n :=
  match n with
  | O => []
  | S n₁ =>
      match dcl with
      | [] =>
          [zero fld … make_char_pol fld (S cdeg) [] n₁]
      | [(deg, coeff) … dcl₁] =>
          if eq_nat_dec deg cdeg then
            [coeff … make_char_pol fld (S cdeg) dcl₁ n₁]
          else
            [zero fld … make_char_pol fld (S cdeg) dcl n₁]
      end
    end.

Definition deg_coeff_of_point α (fld : field α) pol (pt : (Q * Q)) :=
  let h := nofq (fst pt) in
  let ps := list_nth h (al pol) (an pol) in
  let c := valuation_coeff fld ps in
  (h, c).

Definition characteristic_polynomial α (fld : field α) pol ns :=
  let dcl := List.map (deg_coeff_of_point fld pol) [ini_pt ns … oth_pts ns] in
  let j := nofq (fst (ini_pt ns)) in
  let k := nofq (fst (fin_pt ns)) in
  let cl := make_char_pol fld j dcl (k - j) in
  let kps := list_nth k (al pol) (an pol) in
  {| al := cl; an := valuation_coeff fld kps |}.

Definition puiseux_step α psumo acf (pol : polynomial (puiseux_series α)) :=
  let nsl₁ := newton_segments (ac_field acf) pol in
  let (nsl, psum) :=
    match psumo with
    | Some psum =>
        (List.filter (λ ns, negb (Qle_bool (γ ns) Q.zero)) nsl₁, psum)
    | None =>
        (nsl₁, Q.zero)
    end
  in
  match nsl with
  | [] => None
  | [ns … _] =>
      let fld := ac_field acf in
      let cpol := characteristic_polynomial fld pol ns in
      let (c, r) := List.hd (ac_roots acf cpol) in
      let pol₁ := f₁ fld pol (β ns) (γ ns) c in
      let p := Qplus psum (γ ns) in
      Some ({| coeff := c; power := p |}, pol₁)
  end.

CoFixpoint puiseux_loop α psumo acf (pol : polynomial (puiseux_series α)) :=
  match puiseux_step psumo acf pol with
  | Some (t, pol₁) =>
      Term t
        (if zero_is_root (ac_field acf) pol₁ then End _
         else puiseux_loop (Some (power t)) acf pol₁)
  | None =>
      End _
  end.

Fixpoint puiseux_comden α n cd (s : series (term α)) :=
  match n with
  | O => cd
  | S n₁ =>
      match s with
      | Term t ss => puiseux_comden n₁ (Plcm cd (Qden (Qred (power t)))) ss
      | End => cd
      end
  end.

Definition puiseux_root α acf niter (pol : polynomial (puiseux_series α)) :
    puiseux_series α :=
  let s := puiseux_loop None acf pol in
  let cd := puiseux_comden niter I.one s in
  {| ps_terms := term_series_to_coeff_series (zero (ac_field acf)) cd s;
     ps_valnum :=
       match s with
       | Term t _ => Qnum (Qred (Qmult (power t) (Qmake (Zpos cd) I.one)))
       | End => I.zero
       end;
     ps_comden := cd |}.

(* *)

value puiseux_iteration fld br r m γ β sol_list = do {
  if verbose.val then do {
    let ss = inf_string_of_string (string_of_int br.step) in
    printf "\nc%s = %s  r%s = %d\n\n%!" ss (fld.ext.to_string r) ss m;
    let y =
      let cpy = Plus (Const r) (Ypower 1) in
      if I.eq (Q.rnum γ) I.zero then cpy
      else Mult (xpower γ) cpy
    in
    let xmβ = xpower (Q.neg β) in
    let ss₁ = inf_string_of_string (string_of_int (br.step - 1)) in
    printf "f%s(%s,%s) = %sf%s(%s,%s) =\n%!" ss br.vx br.vy
      (string_of_tree fld True br.vx br.vy xmβ)
      (if br.step = 1 then "" else ss₁) br.vx
      (string_of_tree fld True br.vx br.vy y)
  }
  else ();
  let pol = f₁ fld br.pol β γ r in
  if verbose.val then
    let s = string_of_ps_polyn fld True True br.vx br.vy pol in
    let s = cut_long True s in
    printf "  %s\n%!" s
  else ();
  let finite = zero_is_root fld pol in
  let cγl = [(r, γ) … br.cγl] in
  if br.rem_steps = 0 || finite then do {
    if verbose.val then do {
      printf "\n";
      if finite then printf "zero is root !\n%!" else ();
    }
    else ();
    let sol = make_solution fld cγl in
    print_solution fld br (succ (List.length sol_list)) cγl finite sol;
    Left [(sol, finite) … sol_list]
  }
  else if br.rem_steps > 0 then Right (pol, cγl)
  else Left sol_list
};

value rec puiseux_branch af br sol_list ns =
  let γ = ns.γ in
  let β = ns.β in
  let (j, αj) = ns.ini_pt in
  let (k, αk) = ns.fin_pt in
  let j = nofq j in
  let k = nofq k in
  let dpl = ns.oth_pts in
  let fld = af.ac_field in
  let ss = inf_string_of_string (string_of_int br.step) in
  let q = List.fold_left (fun q h → gcd q (nofq (fst h) - j)) (k - j) dpl in
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
  let cpol = characteristic_polynomial fld br.pol ns in
  let rl = ac_roots af cpol in
  if rl = [] then do {
    let sol = make_solution fld br.cγl in
    print_solution fld br (succ (List.length sol_list)) br.cγl False sol;
    [(sol, False) … sol_list]
  }
  else
    List.fold_left
      (fun sol_list (r, m) →
         if fld.is_zero r then sol_list
         else
           match puiseux_iteration fld br r m γ β sol_list with
           [ Right (pol, cγl) → next_step af br sol_list pol cγl
           | Left sol_list → sol_list ])
      sol_list rl

and next_step af br sol_list pol cγl =
  let gbl = newton_segments (ac_field af) pol in
  let gbl_f = List.filter (fun ns → not (Q.le (γ ns) Q.zero)) gbl in
  if gbl_f = [] then do {
    if verbose.val then do {
      printf "    pol %s\n%!"
        (string_of_ps_polyn af.ac_field True False "x" "y" pol);
      List.iter
        (fun ns →
           printf "γ %s β %s\n%!" (Q.to_string (γ ns)) (Q.to_string (β ns)))
        gbl
    }
    else ();
    failwith "no strictly positive γ value"
  }
  else
    List.fold_left
      (fun sol_list ns → do {
         if verbose.val then printf "\n%!" else ();
         let br =
           {initial_polynom = br.initial_polynom;
            cγl = cγl; step = br.step + 1;
            rem_steps = br.rem_steps - 1;
            vx = br.vx; vy = br.vy; pol = pol}
         in
         puiseux_branch af br sol_list ns
       })
      sol_list gbl_f
;

value print_line_equal () =
  if verbose.val then
    printf "\n============================================================\n"
  else ()
;

value puiseux af nb_steps vx vy pol =
(*
let vv = verbose.val in
let _ = verbose.val := False in
let niter = 6 in
let r = puiseux_root af niter pol in
let ps =
  {ps_terms = series_series_take niter (ps_terms r); ps_comden = ps_comden r;
   ps_valnum = ps_valnum r}
in
let _ = printf "PUISEUX : y₁ = %s\n\n%!" (airy_string_of_puiseux_series af.ac_field True vx ps) in
let _ = verbose.val := vv in
*)
  let gbl = newton_segments (ac_field af) pol in
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
           puiseux_branch af br sol_list gbdpl
         })
        [] gbl
    in
    List.rev rev_sol_list
;

value is_zero_tree k =
  fun
  [ Const c → k.is_zero c
  | _ → False ]
;

value polyn_of_tree fld t =
  let pol = tree_polyn_of_tree fld t in
  let rev_ml =
    List.rev_map
       (fun t →
          if is_zero_tree fld t then
            {ps_terms = End; ps_valnum = I.zero; ps_comden = I.one}
          else
            puiseux_series_of_tree fld t)
       (pol.al @ [pol.an])
  in
  match rev_ml with
  | [] → failwith "empty pol"
  | [m … ml] → {al = List.rev ml; an = m}
  end
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
    else if List.mem Sys.argv.(i) ["--test"; "-t"] then do {
      (* undocumented *)
      arg_test.val := True;
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
      eprintf "Eval polynomial on solutions; display <n> terms\n";
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

value af_c () =
  let ext =
    {minus_one = C.minus_one; equal = C.eq; compare = C.compare; gcd = C.gcd;
     normalise = C.normalise; nth_root = C.nth_root; neg_factor = C.neg_factor;
     of_i = C.of_i; of_q = C.of_q; of_a = C.of_a; of_complex = C.of_complex;
     of_float_string = C.of_float_string; to_q = C.to_q; to_a = C.to_a;
     to_complex = C.to_complex; to_string = C.to_string arg_lang.val;
     float_round_zero = C.float_round_zero;
     complex_round_zero = C.complex_round_zero; complex_mul = C.complex_mul;
     cpoly_roots = C.cpoly_roots; complex_to_string = C.complex_to_string}
  in
  let fc =
    {zero = C.zero; one = C.one; add = C.add; sub = C.sub; neg = C.neg;
     mul x y = C.normalise (C.mul x y); div = C.div;
     is_zero c = C.eq C.zero (C.float_round_zero c);
     ext = ext}
  in
  {ac_field = fc; ac_roots = roots fc}
;

value ps_of_int fld i =
  {ops_terms =
     Term {coeff = fld.ext.of_i (I.of_int i); power = Q.zero} End;
   ops_comden =
     I.one}
;

(*
value af_ps af =
  let fld = af.ac_field in
  let zero = ps_of_int fld 0 in
  let one = ps_of_int fld 1 in
  let add = ps_add (norm fld fld.add) in
  let sub = ps_add (norm fld fld.sub) in
  let mul = ps_mul fld.add (norm fld fld.mul) in
  let neg = sub zero in
  let fc =
    {zero = zero; one = one; add = add; sub = sub; neg = neg; mul = mul;
     div _ = failwith "k_ps.div not impl";
     eq _ = failwith "k_ps.eq not impl";
     ext = ()}
  in
  let roots pol =
    let rl = puiseux af 5 "x" "y" pol in
    List.map (fun (r, inf) → (r, 0)) rl
  in
  {ac_field = fc; ac_roots = roots}
;
*)

value af_mpfr () =
  let ext =
    {minus_one = M.minus_one; equal = M.eq; compare = M.compare; gcd = M.gcd;
     normalise = M.normalise; nth_root = M.nth_root; neg_factor = M.neg_factor;
     of_i = M.of_i; of_q = M.of_q; of_a = M.of_a; of_complex = M.of_complex;
     of_float_string = M.of_float_string; to_q = M.to_q; to_a = M.to_a;
     to_complex = M.to_complex; to_string = M.to_string arg_lang.val;
     float_round_zero = M.float_round_zero;
     complex_round_zero = M.complex_round_zero; complex_mul = M.complex_mul;
     cpoly_roots = M.cpoly_roots; complex_to_string = M.complex_to_string}
  in
  let fm =
    {zero = M.zero; one = M.one; add = M.add; sub = M.sub; neg = M.neg;
     mul = M.mul; div = M.div; is_zero = M.eq M.zero; ext = ext}
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
(*
      | [vx; v] → (vx, [v])
*)
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
            eprintf
              "Which one is 'y'? Either name it 'y' or use option -y.\n%!";
          };
          exit 2
        } ]
    in
    match more with
    [ [] →
        if arg_all_mpfr.val then do {
          Cpoly.Mfl.set_prec 200;
          let af = af_mpfr () in
          let fld = af.ac_field in
          let t = tree_of_ast fld vx vy p in
          let t = normalise fld t in
          let norm_txt = string_of_tree fld True vx vy t in
          if verbose.val then do {
            printf "normalised:\n";
            printf "%s\n%!" norm_txt;
          }
          else do {
            printf "equation: %s = 0\n\n%!" norm_txt;
          };
          failwith "--all-mpfr not implemented"
        }
        else do {
          let af = af_c () in
          let fld = af.ac_field in
          let t = tree_of_ast fld vx vy p in
          let t = normalise fld t in
          let norm_txt = string_of_tree fld (not arg_lang.val) vx vy t in
          if verbose.val then do {
            printf "normalised:\n";
            printf "%s\n%!" norm_txt;
          }
          else do {
            printf "equation: %s = 0\n\n%!" norm_txt;
          };
          let pol = polyn_of_tree fld t in
          let _ : list _ = puiseux af arg_nb_steps.val vx vy pol in
          ()
        }
    | [_] → do {
        failwith "k_ps not impl"
      }
    | [_; _ … _] →
        match () with [] ]
  }
  with e →
    match e with
    | Stream.Error s → do {
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
        }
    end
};

if Sys.interactive.val then () else main ();
