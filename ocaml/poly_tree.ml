(* $Id: poly_tree.ml,v 1.51 2013-04-06 12:29:37 deraugla Exp $ *)

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

value rec tree_map f =
  fun
  [ Plus t₁ t₂ → Plus (tree_map f t₁) (tree_map f t₂)
  | Minus t₁ t₂ → Minus (tree_map f t₁) (tree_map f t₂)
  | Neg t → Neg (tree_map f t)
  | Mult t₁ t₂ → Mult (tree_map f t₁) (tree_map f t₂)
  | Xpower n d → Xpower n d
  | Ypower n → Ypower n
  | Const c → Const (f c) ]
;

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
  | (Const c, t₂) → if k.eq c k.one then t₂ else Mult t₁ t₂
  | (t₁, t₂) → Mult t₁ t₂ ]
;

value multi k i t =
  match t with
  [ Const c → Const (k.mul (k.of_i i) c)
  | t →
      if I.eq i I.zero then Const k.zero
      else if I.eq i I.one then t
      else Mult (Const (k.of_i i)) t ]
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
        [ Const c → Const (k.div c (k.of_i (I.os n)))
        | x → not_impl (sprintf "toa ?/%s" n) x ]
    | << $e₁$ ** $e₂$ >> →
        match e₂ with
        [ << $int:n$ >> → tree_power k (expr e₁) (ios n) 1
        | << $int:n$ / $int:d$ >> → tree_power k (expr e₁) (ios n) (ios d)
        | _ → failwith "toa ** not int" ]
    | << $lid:s$ >> →
        if s = vx then Xpower 1 1
        else if s = vy then Ypower 1
        else if s = "i" then Const (k.of_a (A₂.make Q.zero Q.one I.minus_one))
        else failwith (sprintf "toa lid %s" s)
    | << $int:s$ >> →
        Const (k.of_i (I.os s))
    | << $flo:s$ >> →
        Const (k.of_float_string s)
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
        k.to_string c
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
      if Q.eq m.power₂ m₁.power₂ then
        let c = k.normalise (k.add m.coeff₂ m₁.coeff₂) in
        if k.eq c k.zero then ml₁
        else [{coeff₂ = c; power₂ = m.power₂} :: ml₁]
      else if k.eq m.coeff₂ k.zero then ml
      else [m :: ml]
  | [] →
      if k.eq m.coeff₂ k.zero then [] else [m] ]
;

value group_term_descr k tdl =
  List.fold_right
    (fun td myl →
       let mx = {coeff₂ = td.const; power₂ = td.xpow} in
       match myl with
       [ [my :: myl₁] →
           if td.ypow = my.power then
             let mxl = merge_const_px k mx my.coeff.ps_monoms in
             if mxl = [] then myl₁
             else [{coeff = {ps_monoms = mxl}; power = my.power} :: myl₁]
           else [{coeff = {ps_monoms = [mx]}; power = td.ypow} :: myl]
       | [] → [{coeff = {ps_monoms = [mx]}; power = td.ypow}] ])
    tdl []
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
      match k.neg_factor c with
      [ Some c → Some (Const c)
      | None → None ]
  | _ →
      None ]
;

value tree_of_tree_polyn k pol =
  let expr_of_term_ypow_list k t₁ my =
    let t₂ =
      if my.power = 0 then my.coeff
      else
        let (is_neg, t₂) =
          match without_initial_neg k my.coeff with
          [ Some t₂ → (True, t₂)
          | None → (False, my.coeff) ]
        in
        let t₂_is_one =
          match t₂ with
          [ Const c → k.eq c k.one
          | _ →  False ]
        in
        let t₂ =
          if t₂_is_one then Ypower my.power else Mult t₂ (Ypower my.power)
        in
        if is_neg then Neg t₂ else t₂
    in
    let t_is_null =
      match t₁ with
      [ Const c → k.eq c k.zero
      | _ → False ]
    in
    if t_is_null then t₂
    else
      match without_initial_neg k t₂ with
      [ Some t₂ → Minus t₁ t₂
      | None → Plus t₁ t₂ ]
  in
  List.fold_left (expr_of_term_ypow_list k) (Const k.zero) pol.monoms
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
             (k.to_string td.const) (Q.to_string td.xpow) td.ypow)
        tdl
    else ()
  in
  let tdl = List.sort compare_descr tdl in
(*
let _ = printf "normalise compare_descr\n%!" in
let _ = List.iter (fun td → printf "  const %s xpow %s ypow %d\n%!" (C.to_string td.const) (Q.to_string td.xpow) td.ypow) tdl in
*)
  {monoms = group_term_descr k tdl}
;

value xpower r = Xpower (I.to_int (Q.rnum r)) (I.to_int (Q.rden r));

value tree_of_puiseux_series k ps =
  let rebuild_add t mx =
    if k.eq mx.coeff₂ k.zero then t
    else
       let t₁ =
         if Q.eq mx.power₂ Q.zero then Const mx.coeff₂
         else
           let xp = xpower mx.power₂ in
           if k.eq mx.coeff₂ k.one then xp
           else if k.eq mx.coeff₂ k.minus_one then Neg xp
           else Mult (Const mx.coeff₂) xp
       in
       let t₁ =
         match without_initial_neg k t₁ with
         [ Some t₁ → Neg t₁
         | None → t₁ ]
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
  List.fold_left rebuild_add (Const k.zero) ps.ps_monoms
;

value tree_of_polyn k pol =
  let rebuild_add t m =
    if k.eq m.coeff k.zero then t
    else
       let t₁ =
         if m.power = 0 then Const m.coeff
         else if k.eq m.coeff k.one then Ypower m.power
         else if k.eq m.coeff k.minus_one then Neg (Ypower m.power)
         else Mult (Const m.coeff) (Ypower m.power)
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
  List.fold_left rebuild_add (Const k.zero) pol.monoms
;

value tree_of_ps_polyn k pol =
  let ml =
    List.map
      (fun m → {coeff = tree_of_puiseux_series k m.coeff; power = m.power})
      pol.monoms
  in
  tree_of_tree_polyn k {monoms = ml}
;

value normalise k t =
  let pol = ps_polyn_of_tree k t in
  tree_of_ps_polyn k pol
;

value substitute_y k y t =
  let rec tree t =
    match t with
    [ Plus t₁ t₂ → Plus (tree t₁) (tree t₂)
    | Minus t₁ t₂ → Minus (tree t₁) (tree t₂)
    | Neg t → Neg (tree t)
    | Mult t₁ t₂ → Mult (tree t₁) (tree t₂)
    | Ypower py → tree_power k y py 1
    | Xpower _ _ | Const _ → t ]
  in
  tree t
;

value sum_tree_of_tree t =
  expr [] t where rec expr list =
    fun
    [ Plus t₁ t₂ → expr [t₂ :: list] t₁
    | Minus t₁ t₂ → expr [Neg t₂ :: list] t₁
    | t → [t :: list] ]
;

value rec tree_with_pow_y k t =
  match t with
  [ Neg t →
      let my = tree_with_pow_y k t in
      {coeff = Neg my.coeff; power = my.power}
  | Mult t₁ (Ypower n) →
      {coeff = t₁; power = n}
  | Ypower n →
      {coeff = Const k.one; power = n}
  | Xpower _ _ | Mult _ _ | Const _ →
      {coeff = t; power = 0}
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

value compare_expr_pow cmp m₁ m₂ = cmp m₁.power m₂.power;
value compare_expr_pow₂ cmp m₁ m₂ = cmp m₁.power₂ m₂.power₂;

value merge_expr_pow k power_eq merge_coeffs =
  loop [] where rec loop rev_list =
    fun
    [ [m₁ :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [m₂ :: rev_list₂] →
              if power_eq m₁.power m₂.power then
                merge_coeffs k m₁.coeff m₂.coeff m₁.power rev_list₂
              else
                [m₁ :: rev_list]
          | [] →
              [m₁] ]
        in
        loop rev_list₁ ml₁
    | [] →
        List.rev rev_list ]
;

value merge_expr_pow₂ k power_eq merge_coeffs =
  loop [] where rec loop rev_list =
    fun
    [ [m₁ :: ml₁] →
        let rev_list₁ =
          match rev_list with
          [ [m₂ :: rev_list₂] →
              if power_eq m₁.power₂ m₂.power₂ then
                merge_coeffs k m₁.coeff₂ m₂.coeff₂ m₁.power₂ rev_list₂
              else
                [m₁ :: rev_list]
          | [] →
              [m₁] ]
        in
        loop rev_list₁ ml₁
    | [] →
        List.rev rev_list ]
;

value merge_coeffs k t₁ t₂ p ml =
  match (t₁, t₂) with
  [ (Const c₁, Const c₂) →
      let c = k.add c₁ c₂ in
      if k.eq c k.zero then ml
      else [{coeff = Const c; power = p} :: ml]
  | _ →
      [{coeff = Plus t₂ t₁; power = p} :: ml ] ]
;

value merge_coeffs₂ k t₁ t₂ p ml =
  match (t₁, t₂) with
  [ (Const c₁, Const c₂) →
      let c = k.add c₁ c₂ in
      if k.eq c k.zero then ml
      else [{coeff₂ = Const c; power₂ = p} :: ml]
  | _ →
      [{coeff₂ = Plus t₂ t₁; power₂ = p} :: ml ] ]
;

value tree_polyn_of_tree k t =
  let tl = sum_tree_of_tree t in
  let myl = List.map (tree_with_pow_y k) tl in
  let myl = List.sort (compare_expr_pow \-) myl in
  let myl = merge_expr_pow k \= merge_coeffs myl in
  p_of_op (Const k.zero) {monoms = myl}
;

value rec expr_with_pow_x k t =
  match t with
  [ Neg t →
      let mx = expr_with_pow_x k t in
      {coeff₂ = Neg mx.coeff₂; power₂ = mx.power₂}
  | Mult t₁ (Xpower n d) →
      {coeff₂ = t₁; power₂ = Q.make (I.of_int n) (I.of_int d)}
  | Xpower n d →
      {coeff₂ = Const k.one; power₂ = Q.make (I.of_int n) (I.of_int d)}
  | Const _ →
      {coeff₂ = t; power₂ = Q.zero}
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

value puiseux_series_of_tree k t =
  let (is_neg, t) =
    match t with
    [ Neg t → (True, t)
    | _ → (False, t) ]
  in
  let tl = sum_tree_of_tree t in
  let mxl = List.map (expr_with_pow_x k) tl in
  let mxl = List.sort (compare_expr_pow₂ Q.compare) mxl in
  let mxl = merge_expr_pow₂ k Q.eq merge_coeffs₂ mxl in
  let mxl =
    List.map
      (fun mx → {coeff₂ = const_of_tree k mx.coeff₂; power₂ = mx.power₂})
      mxl
  in
  let mxl =
    if is_neg then
      List.map (fun mx → {coeff₂ = k.neg mx.coeff₂; power₂ = mx.power₂}) mxl
    else
      mxl
  in
  {ps_monoms = mxl}
;
