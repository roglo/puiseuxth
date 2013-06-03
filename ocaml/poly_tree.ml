(* $Id: poly_tree.ml,v 1.78 2013-06-03 02:08:38 deraugla Exp $ *)

#load "q_MLast.cmo";
#load "pa_macro.cmo";

IFDEF CAMLP5_6_09 THEN
#option "-dquot" "expr";
ELSE
#load "./q_def_expr.cmo";
END;

open Printf;
open Pnums;
open Field;
open Poly;
open Puiseux_series;

type tree α =
  [ Plus of tree α and tree α
  | Minus of tree α and tree α
  | Neg of tree α
  | Mult of tree α and tree α
  | Xpower of int and int
  | Ypower of int
  | Const of α ]
;

type term_descr α = { const : α; xpow : Q.t; ypow : int };

value rec comb n k =
  if n ≤ 0 || k < 0 || k > n then invalid_arg (sprintf "comb n=%d k=%d" n k)
  else if n = 1 || k = 0 || k = n then I.one
  else I.add (comb (n-1) (k-1)) (comb (n-1) k)
;

value power_int k a b =
  if b ≥ 0 then
    loop b k.one where rec loop b r =
      if b = 0 then r else loop (b - 1) (k.mul r a)
  else
    failwith "not impl power_int"
;

value mult k t₁ t₂ =
  match (t₁, t₂) with
  [ (Const c₁, Const c₂) → Const (k.mul c₁ c₂)
  | (Const c, t₂) → if k.equal c k.one then t₂ else Mult t₁ t₂
  | (t₁, t₂) → Mult t₁ t₂ ]
;

value multi k i t =
  match t with
  [ Const c → Const (k.mul (k.ext.of_i i) c)
  | t →
      if I.eq i I.zero then Const k.zero
      else if I.eq i I.one then t
      else Mult (Const (k.ext.of_i i)) t ]
;

value rec tree_power k t n d =
  match t with
  [ Plus t₁ t₂ →
      if d <> 1 then failwith "bad sum power"
      else if n = 0 then Const k.one
      else expr_plus_power k t₁ t₂ n
  | Minus t₁ t₂ →
      if d <> 1 then failwith "bad diff power"
      else if n = 0 then Const k.one
      else expr_plus_power k t₁ (Neg t₂) n
  | Neg t →
      let t = tree_power k t n d in
      if d = 1 then if n mod 2 = 0 then t else Neg t
      else failwith "not impl tree_power Neg"
  | Mult t₁ t₂ →
      Mult (tree_power k t₁ n d) (tree_power k t₂ n d)
  | Xpower n₁ d₁ →
      let n = n₁ * n in
      let d = d₁ * d in
      let g = gcd n d in
      Xpower (n / g) (d / g)
  | Ypower n₁ →
      let n = n₁ * n in
      let g = gcd n d in
      let n = n / g in
      let d = d / g in
      if n < 0 || d <> 1 then failwith "bad y power"
      else Ypower n
  | Const c →
      if d = 1 then Const (power_int k c n)
      else failwith "not impl tree_power Const" ]
and expr_plus_power k t₁ t₂ n =
  loop n where rec loop i =
    let c = comb n i in
    let t₁ = tree_power k t₁ (n - i) 1 in
    let t₂ = tree_power k t₂ i 1 in
    let t = mult k (multi k c t₁) t₂ in
    if i = 0 then t
    else Plus (loop (i - 1)) t
;

value tree_of_ast k vx vy =
  let rec expr =
    fun
    [ << $e₁$ + $e₂$ >> →
        match (expr e₁, expr e₂) with
        [ (Const c₁, Const c₂) → Const (k.add c₁ c₂)
        | (t₁, t₂) → Plus t₁ t₂ ]
    | << $e₁$ - $e₂$ >> →
        match (expr e₁, expr e₂) with
        [ (Const c₁, Const c₂) → Const (k.sub c₁ c₂)
        | (t₁, t₂) → Minus t₁ t₂ ]
    | << - $e$ >> →
        match expr e with
        [ Const c → Const (k.neg c)
        | t → Neg t ]
    | << $e₁$ * $e₂$ >> →
        match (expr e₁, expr e₂) with
        [ (Const c₁, Const c₂) → Const (k.mul c₁ c₂)
        | (t₁, t₂) → Mult t₁ t₂ ]
    | << $e$ / $int:n$ >> →
        match expr e with
        [ Const c → Const (k.div c (k.ext.of_i (I.os n)))
        | x → not_impl (sprintf "toa ?/%s" n) x ]
    | << $e₁$ ** $e₂$ >> →
        match e₂ with
        [ << $int:n$ >> → tree_power k (expr e₁) (ios n) 1
        | << $int:n$ / $int:d$ >> → tree_power k (expr e₁) (ios n) (ios d)
        | << - $int:n$ >> → tree_power k (expr e₁) (- ios n) 1
        | _ → failwith "toa ** not int" ]
    | << $lid:s$ >> →
        if s = vx then Xpower 1 1
        else if s = vy then Ypower 1
        else if s = "i" then
          Const (k.ext.of_a (A₂.make Q.zero Q.one I.minus_one))
        else
          failwith (sprintf "toa lid %s" s)
    | << $int:s$ >> →
        Const (k.ext.of_i (I.os s))
    | << $flo:s$ >> →
        Const (k.ext.of_float_string s)
    | << $lid:s$ $_$ $_$ >> →
        failwith (sprintf "toa op %s" s)
    | << $lid:s$ $_$ >> →
        failwith (sprintf "toa unop %s" s)
    | e →
        not_impl "tree_of_ast" e ]
  in
  expr
;

value gen_string_of_tree k airy opt vx vy =
  let rec expr ai =
    fun
    [ Plus t₁ t₂ → sprintf "%s%s+%s%s" (expr ai t₁) ai ai (expr₁ t₂)
    | Minus t₁ t₂ → sprintf "%s%s-%s%s" (expr ai t₁) ai ai (expr₁ t₂)
    | t → expr₁ t ]
  and expr₁ =
    fun
    [ Neg t → sprintf "-%s" (expr₁ t)
    | t → expr₂ t ]
  and expr₂ =
    fun
    [ Mult t₁ t₂ →
        let op = if opt then "" else "*" in
        sprintf "%s%s%s" (expr₂ t₁) op (expr₃ t₂)
    | t → expr₃ t ]
  and expr₃ =
    fun
    [ Xpower n d →
        if d = 1 then
          if n = 1 then vx
          else if opt then sprintf "%s%s" vx (sup_string_of_string (soi n))
          else sprintf "%s^%d" vx n
        else if n > 0 && Poly_print.with_sqrt_x.val && d ≤ 3 then
          if d = 2 then
            if n = 1 then sprintf "√%s" vx
            else
              match n mod 2 with
              [ 1 →
                  let n = n / 2 in
                  if n = 1 then sprintf "%s√%s" vx vx
                  else sprintf "%s%s√%s" vx (sup_string_of_string (soi n)) vx
              | _ →
                  let _ = printf "n %d d %d\n%!" n d in
                  match () with [] ]
          else
            if n = 1 then sprintf "∛%s" vx
            else if n = 2 then sprintf "∛%s²" vx
            else
              match n mod 3 with
              [ 1 →
                  let n = n / 3 in
                  if n = 1 then sprintf "%s∛%s" vx vx
                  else sprintf "%s%s∛%s" vx (sup_string_of_string (soi n)) vx
              | 2 →
                  let n = n / 3 in
                  if n = 1 then sprintf "%s∛%s²" vx vx
                  else sprintf "%s%s∛%s²" vx (sup_string_of_string (soi n)) vx
              | _ →
                  let _ = printf "n %d d %d\n%!" n d in
                  match () with [] ]
        else if opt then
          sprintf "%s%s" vx (sup_string_of_string (soi n ^ "/" ^ soi d))
        else
          sprintf "%s^(%d/%d)" vx n d
    | Ypower n →
        if n = 1 then vy
        else if opt then sprintf "%s%s" vy (sup_string_of_string (soi n))
        else sprintf "%s^%d" vy n
    | Const c →
        k.ext.to_string c
    | Plus _ _ | Minus _ _ | Neg _ | Mult _ _ as t →
        sprintf "(%s)" (expr "" t) ]
  in
  expr (if airy then " " else "")
;

value string_of_tree k = gen_string_of_tree k False;
value airy_string_of_tree k = gen_string_of_tree k True;

value rec is_factor =
  fun
  [ Plus _ _ → False
  | Minus _ _ → False
  | Neg t → is_factor t
  | Mult t₁ t₂ → is_factor t₁ && is_factor t₂
  | Xpower _ _ → True
  | Ypower _ → True
  | Const _ → True ]
;

value rec flatten t tl =
  if is_factor t then [t :: tl]
  else
    match t with
    [ Plus t₁ t₂ →
        flatten t₁ (flatten t₂ tl)
    | Minus t₁ t₂ →
        flatten t₁ (flatten (Neg t₂) tl)
    | Neg t →
        let tl₁ = List.map (fun t → Neg t) (flatten t []) in
        tl₁ @ tl
    | Mult t₁ t₂ →
        let tl₁ = flatten t₁ [] in
        let tl₂ = flatten t₂ [] in
        List.fold_right
          (fun t₂ → List.fold_right (fun t₁ → flatten (Mult t₁ t₂)) tl₁)
          tl₂ tl
    | Xpower _ _ | Ypower _ | Const _ →
        [t :: tl] ]
;

value term_descr_of_term k =
  let rec term td =
    fun
    [ Plus _ _ → match () with []
    | Minus _ _ → match () with []
    | Neg t →
        let td = term td t in
        {(td) with const = k.neg td.const}
    | Mult t₁ t₂ →
        let td = term td t₁ in
        term td t₂
    | Xpower p q →
        let xpow = Q.norm (Q.add td.xpow (Q.make (I.of_int p) (I.of_int q))) in
        {(td) with xpow = xpow}
    | Ypower i →
        {(td) with ypow = td.ypow + i}
    | Const c →
        {(td) with const = k.mul td.const c} ]
  in
  term {const = k.one; xpow = Q.zero; ypow = 0}
;

value compare_descr td₁ td₂ =
  if td₁.ypow < td₂.ypow then -1
  else if td₁.ypow > td₂.ypow then 1
  else if Q.eq td₁.xpow td₂.xpow then 0
  else if Q.le td₁.xpow td₂.xpow then -1
  else 1
;

value merge_const_px k m ml =
  match ml with
  [ [m₁ :: ml₁] →
      if Q.eq m.power m₁.power then
        let c = k.ext.normalise (k.add m.coeff m₁.coeff) in
        if k.is_zero c then ml₁
        else [{coeff = c; power = m.power} :: ml₁]
      else if k.is_zero m.coeff then ml
      else [m :: ml]
  | [] →
      if k.is_zero m.coeff then [] else [m] ]
;

value group_term_descr k tdl =
  let rev_ml =
    List.fold_left
      (fun rev_myl td →
         let mx = {coeff = td.const; power = td.xpow} in
         match rev_myl with
         [ [(ps, p) :: rev_myl₁] →
             if td.ypow = p then
               let mxl = merge_const_px k mx ps.old_ps_mon in
               if mxl = [] then rev_myl₁
               else [({old_ps_mon = mxl}, p) :: rev_myl₁]
             else [({old_ps_mon = [mx]}, td.ypow) :: rev_myl]
         | [] →
             [({old_ps_mon = [mx]}, td.ypow)] ])
      [] tdl
  in 
  loop [] 0 (List.rev rev_ml) where rec loop rev_cl deg ml =
    match ml with
    [ [(ps, p) :: ml₁] →
        if p > deg then
          loop [{old_ps_mon = []} :: rev_cl] (deg + 1) ml
        else if p < deg then
          match () with []
        else
          loop [{old_ps_mon = List.rev ps.old_ps_mon} :: rev_cl] (deg + 1) ml₁
    | [] →
        {ml = List.rev rev_cl} ]
;

value rec without_initial_neg k =
  fun
  [ Minus t₁ t₂ →
      match without_initial_neg k t₁ with
      [ Some t₁ → Some (Plus t₁ t₂)
      | None → None ]
  | Neg t →
      Some t
  | Mult t₁ t₂ →
      match without_initial_neg k t₁ with
      [ Some t₁ → Some (Mult t₁ t₂)
      | None → None ]
  | Const c →
      match k.ext.neg_factor c with
      [ Some c → Some (Const c)
      | None → None ]
  | _ →
      None ]
;

value is_zero_tree k =
  fun
  [ Const c → k.is_zero c
  | _ → False ]
;

value tree_of_tree_polyn k pol =
  let expr_of_term_ypow_list k (t₁, deg) m =
    let t =
      if is_zero_tree k m then t₁
      else
        let t₂ =
          if deg = 0 then m
          else
            let (is_neg, t₂) =
              match without_initial_neg k m with
              [ Some t₂ → (True, t₂)
              | None → (False, m) ]
            in
            let t₂_is_one =
              match t₂ with
              [ Const c → k.equal c k.one
              | _ →  False ]
            in
            let t₂ =
              if t₂_is_one then Ypower deg else Mult t₂ (Ypower deg)
            in
            if is_neg then Neg t₂ else t₂
        in
        let t_is_null =
          match t₁ with
          [ Const c → k.is_zero c
          | _ → False ]
        in
        if t_is_null then t₂
        else
          match without_initial_neg k t₂ with
          [ Some t₂ → Minus t₁ t₂
          | None → Plus t₁ t₂ ]
    in
    (t, deg + 1)
  in
  let (t, _) =
    List.fold_left (expr_of_term_ypow_list k) (Const k.zero, 0) pol.ml
  in
  t
;

value debug_n = False;

value ps_polyn_of_tree k t =
  let _ =
    if debug_n then
      printf "    tree: %s\n%!" (string_of_tree k True "x" "y" t)
    else ()
  in
  let tl = flatten t [] in
  let _ = if debug_n then printf "normalise flatten\n%!" else () in
  let _ =
    if debug_n then
      List.iter
        (fun t → printf "  %s\n%!" (string_of_tree k True "x" "y" t)) tl
    else ()
  in
  let tdl = List.map (term_descr_of_term k) tl in
  let _ = if debug_n then printf "normalise term_descr_of_term\n%!" else () in
  let _ =
    if debug_n then
      List.iter
        (fun td →
           printf "  const %s xpow %s ypow %d\n%!"
             (k.ext.to_string td.const) (Q.to_string td.xpow) td.ypow)
        tdl
    else ()
  in
  let tdl = List.sort compare_descr tdl in
(*
let _ = printf "normalise compare_descr\n%!" in
let _ = List.iter (fun td → printf "  const %s xpow %s ypow %d\n%!" (C.to_string td.const) (Q.to_string td.xpow) td.ypow) tdl in
*)
  group_term_descr k tdl
;

value xpower r = Xpower (I.to_int (Q.rnum r)) (I.to_int (Q.rden r));

value tree_of_old_puiseux_series k cancel_zeroes ps =
  let rebuild_add t mx =
    if cancel_zeroes && k.is_zero mx.coeff then t
    else
      let t₁ =
        if Q.eq mx.power Q.zero then Const mx.coeff
        else
          let xp = xpower mx.power in
          if k.equal mx.coeff k.one then xp
          else if k.equal mx.coeff k.ext.minus_one then Neg xp
          else Mult (Const mx.coeff) xp
      in
      let t₁ =
        match without_initial_neg k t₁ with
        [ Some t₁ → Neg t₁
        | None → t₁ ]
      in
      let t_is_null =
        match t with
        [ Const c → k.is_zero c
        | _ → False ]
      in
      if cancel_zeroes && t_is_null then t₁
      else
        match without_initial_neg k t₁ with
        [ Some t₁ → Minus t t₁
        | None → Plus t t₁ ]
  in
  List.fold_left rebuild_add (Const k.zero) ps.old_ps_mon
;

value rev_tree_of_polyn k pol =
  let rebuild_add (t, deg) m =
    let t =
      if k.is_zero m then t
      else
         let t₁ =
           if deg = 0 then Const m
           else if k.equal m k.one then Ypower deg
           else if k.equal m k.ext.minus_one then Neg (Ypower deg)
           else Mult (Const m) (Ypower deg)
         in
         let t_is_null =
           match t with
           [ Const c → k.is_zero c
           | _ → False ]
         in
         if t_is_null then t₁
         else
           match without_initial_neg k t₁ with
           [ Some t₁ → Minus t t₁
           | None → Plus t t₁ ]
       in
       (t, deg - 1)
  in
  let deg = List.length pol.ml - 1 in
  let (t, _) =
    List.fold_left rebuild_add (Const k.zero, deg) (List.rev pol.ml)
  in
  t
;

value tree_of_ps_polyn k cancel_zeroes pol =
  let cl = List.map (tree_of_old_puiseux_series k cancel_zeroes) pol.ml in
  tree_of_tree_polyn k {ml = cl}
;

value normalise k t =
  let pol = ps_polyn_of_tree k t in
  tree_of_ps_polyn k True pol
;

value sum_tree_of_tree t =
  expr [] t where rec expr list =
    fun
    [ Plus t₁ t₂ → expr [t₂ :: list] t₁
    | Minus t₁ t₂ → expr [Neg t₂ :: list] t₁
    | t → [t :: list] ]
;

type old_monomial α = { old_coeff : α; old_power : int };

value rec tree_with_pow_y k t =
  match t with
  [ Neg t →
      let my = tree_with_pow_y k t in
      {old_coeff = Neg my.old_coeff; old_power = my.old_power}
  | Mult t₁ (Ypower n) →
      {old_coeff = t₁; old_power = n}
  | Ypower n →
      {old_coeff = Const k.one; old_power = n}
  | Xpower _ _ | Mult _ _ | Const _ →
      {old_coeff = t; old_power = 0}
  | t →
      failwith
        (sprintf "not_impl \"tree_with_pow_y\" %s"
           (string_of_tree k False "x" "y" t)) ]
;

value _list_sort cmp =
  let rec insert x =
    fun
    [ [y :: l] → if cmp x y < 0 then [x; y :: l] else [y :: insert x l]
    | [] → [x] ]
  in
  let rec sort sorted =
    fun
    [ [x :: l] → sort (insert x sorted) l
    | [] → sorted ]
  in
  sort []
;

value compare_expr_pow cmp m₁ m₂ = cmp m₁.old_power m₂.old_power;
value compare_expr_pow₂ cmp m₁ m₂ = cmp m₁.power m₂.power;

value merge_expr_pow k power_eq merge_old_coeffs =
  loop [] where rec loop rev_list =
    fun
    [ [m₁ :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [m₂ :: rev_list₂] →
              if power_eq m₁.power m₂.power then
                merge_old_coeffs k m₁.coeff m₂.coeff m₁.power rev_list₂
              else
                [m₁ :: rev_list]
          | [] →
              [m₁] ]
        in
        loop rev_list₁ ml₁
    | [] →
        List.rev rev_list ]
;

value merge_old_coeffs k t₁ t₂ p ml =
  match (t₁, t₂) with
  [ (Const c₁, Const c₂) →
      let c = k.add c₁ c₂ in
      if k.is_zero c then ml
      else [{old_coeff = Const c; old_power = p} :: ml]
  | _ →
      [{old_coeff = Plus t₂ t₁; old_power = p} :: ml ] ]
;

value old_merge_expr_pow k =
  loop [] where rec loop rev_list =
    fun
    [ [m₁ :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [m₂ :: rev_list₂] →
              if m₁.old_power = m₂.old_power then
                merge_old_coeffs k m₁.old_coeff m₂.old_coeff m₁.old_power
                  rev_list₂
              else
                [m₁ :: rev_list]
          | [] →
              [m₁] ]
        in
        loop rev_list₁ ml₁
    | [] →
        List.rev rev_list ]
;

value tree_polyn_of_tree k t =
  let tl = sum_tree_of_tree t in
  let myl = List.map (tree_with_pow_y k) tl in
  let myl = List.sort (compare_expr_pow \-) myl in
  let myl = old_merge_expr_pow k myl in
  loop [] 0 myl where rec loop rev_np deg ml =
    match ml with
    [ [m :: ml₁] →
        if m.old_power > deg then loop [Const k.zero :: rev_np] (deg + 1) ml
        else if m.old_power < deg then match () with []
        else loop [m.old_coeff :: rev_np] (deg + 1) ml₁
    | [] →
        {ml = List.rev rev_np} ]
;

value rec expr_with_pow_x k t =
  match t with
  [ Neg t →
      let mx = expr_with_pow_x k t in
      {coeff = Neg mx.coeff; power = mx.power}
  | Mult t₁ (Xpower n d) →
      {coeff = t₁; power = Q.make (I.of_int n) (I.of_int d)}
  | Xpower n d →
      {coeff = Const k.one; power = Q.make (I.of_int n) (I.of_int d)}
  | Const _ →
      {coeff = t; power = Q.zero}
  | t →
      failwith
        (sprintf "not_impl \"expr_with_pow_x\" %s"
           (string_of_tree k False "x" "y" t)) ]
;

value rec const_of_tree k =
  fun
  [ Const c → c
  | Neg t → k.neg (const_of_tree k t)
  | _ → failwith "const_of_tree" ]
;

value merge_ps_coeffs k t₁ t₂ p ml =
  match (t₁, t₂) with
  [ (Const c₁, Const c₂) →
      let c = k.add c₁ c₂ in
      if k.is_zero c then ml
      else [{coeff = Const c; power = p} :: ml]
  | _ →
      [{coeff = Plus t₂ t₁; power = p} :: ml ] ]
;

value puiseux_series_of_tree k t =
  let (is_neg, t) =
    match t with
    [ Neg t → (True, t)
    | _ → (False, t) ]
  in
  let tl = sum_tree_of_tree t in
  let mxl = List.map (expr_with_pow_x k) tl in
  let mxl = List.sort (compare_expr_pow₂ Q.compare) mxl in
  let mxl = merge_expr_pow k Q.eq merge_ps_coeffs mxl in
  let mxl =
    List.map
      (fun mx → {coeff = const_of_tree k mx.coeff; power = mx.power})
      mxl
  in
  let mxl =
    if is_neg then
      List.map (fun mx → {coeff = k.neg mx.coeff; power = mx.power}) mxl
    else
      mxl
  in
  {old_ps_mon = mxl}
;
