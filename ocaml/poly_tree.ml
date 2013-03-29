(* $Id: poly_tree.ml,v 1.14 2013-03-29 06:10:21 deraugla Exp $ *)

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

value tree_of_ast (k : field _) vx vy =
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

value gen_string_of_tree (k : field _) airy opt vx vy =
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

value merge_const_px k (c, px) cpl =
  match cpl with
  [ [(c₁, px₁) :: cpl₁] →
      if Q.eq px px₁ then
        let c = k.norm (k.add c c₁) in
        if k.eq c k.zero then cpl₁
        else [(c, px) :: cpl₁]
      else if k.eq c k.zero then cpl
      else [(c, px) :: cpl]
  | [] →
      if k.eq c k.zero then [] else [(c, px)] ]
;

value group_term_descr k tdl =
  List.fold_right
    (fun td cplpl →
       let cp = (td.const, td.xpow) in
       match cplpl with
       [ [(cpl, py) :: cplpl₁] →
           if td.ypow = py then
             let cpl = merge_const_px k cp cpl in
             if cpl = [] then cplpl₁ else [(cpl, py) :: cplpl₁]
           else [([cp], td.ypow) :: cplpl]
       | [] → [([cp], td.ypow)] ])
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

value term_of_const_xpow_list k t (c, px) =
  let (is_neg, c) =
    match k.neg_factor c with
    [ Some c → (True, c)
    | None → (False, c) ]
  in
  let t₂ =
    if Q.eq px Q.zero then Const c
    else
      let tx = Xpower (I.to_int (Q.rnum px)) (I.to_int (Q.rden px)) in
      if k.eq c k.one then tx
      else if k.eq c k.minus_one then Neg tx
      else Mult (Const c) tx
  in
  let t₂ = if is_neg then Neg t₂ else t₂ in
  let t_is_null =
    match t with
    [ Const c₀ → k.eq c₀ k.zero
    | _ → False ]
  in
  if t_is_null then t₂
  else
    match without_initial_neg k t₂ with
    [ Some t₂ → Minus t t₂
    | None → Plus t t₂ ]
;

value expr_of_term_ypow_list (k : field _) t₁ (t₂, py) =
  let t₂ =
    if py = 0 then t₂
    else
      let (is_neg, t₂) =
        match without_initial_neg k t₂ with
        [ Some t₂ → (True, t₂)
        | None → (False, t₂) ]
      in
      let t₂_is_one =
        match t₂ with
        [ Const c → k.eq c k.one
        | _ →  False ]
      in
      let t₂ = if t₂_is_one then Ypower py else Mult t₂ (Ypower py) in
      if is_neg then Neg t₂ else t₂
  in
  let t_is_null =
    match t₁ with
    [ Const c₀ → k.eq c₀ k.zero
    | _ → False ]
  in
  if t_is_null then t₂
  else
    match without_initial_neg k t₂ with
    [ Some t₂ → Minus t₁ t₂
    | None → Plus t₁ t₂ ]
;

value debug_n = False;

value group (k : field _) t =
  let _ =
    if debug_n then
      printf "    tree: %s\n%!" (string_of_tree k True "x" "y" t)
    else ()
  in
  let tl = flatten t [] in
  let _ = if debug_n then printf "normalize flatten\n%!" else () in
  let _ =
    if debug_n then
      List.iter
        (fun t → printf "  %s\n%!" (string_of_tree k True "x" "y" t)) tl
    else ()
  in
  let tdl = List.map (term_descr_of_term k) tl in
  let _ = if debug_n then printf "normalize term_descr_of_term\n%!" else () in
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
let _ = printf "normalize compare_descr\n%!" in
let _ = List.iter (fun td → printf "  const %s xpow %s ypow %d\n%!" (C.to_string td.const) (Q.to_string td.xpow) td.ypow) tdl in
*)
  group_term_descr k tdl
;

value normalize (k : field _) t =
  let cplpl = group k t in
  let _ = if debug_n then printf "normalize group_term_descr\n%!" else () in
  let _ =
    if debug_n then
      List.iter
        (fun (cpl, py) → do {
           printf "  py %d\n%!" py;
           List.iter
             (fun (cst, px) →
                printf "    cst %s px %s\n%!" (k.to_string cst)
                  (Q.to_string px))
             cpl
         })
        cplpl
    else ()
  in
  let tpl =
    List.map
      (fun (cpl, py) →
         let t =
           List.fold_left (term_of_const_xpow_list k) (Const k.zero) cpl
         in
         (t, py))
      cplpl
  in
  let _ =
    if debug_n then printf "normalize term_of_const_xpow_list\n%!" else ()
  in
  let _ =
    if debug_n then
      List.iter
        (fun (t, py) →
           printf "  t %s py %d\n%!" (string_of_tree k True "x" "y" t) py)
        tpl
    else ()
  in
  let t = List.fold_left (expr_of_term_ypow_list k) (Const k.zero) tpl in
  t
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

value rec tree_with_pow_y (k : field _) t =
  match t with
  [ Neg t →
      let (t, n) = tree_with_pow_y k t in
      (Neg t, n)
  | Mult t₁ (Ypower n) →
      (t₁, n)
  | Ypower n →
      (Const k.one, n)
  | Xpower _ _ | Mult _ _ | Const _ →
      (t, 0)
  | t →
      failwith
        (sprintf "not_impl \"tree_with_pow_y\" %s"
           (string_of_tree k False "x" "y" t)) ]
;

value list_sort cmp =
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

value compare_expr_pow cmp (_, n₁) (_, n₂) = cmp n₁ n₂;

(**)
value merge_expr_pow k eq =
  loop where rec loop =
    fun
    [ [(t₁, p₁); (t₂, p₂) :: tnl] →
        if eq p₁ p₂ then
          match (t₁, t₂) with
          [ (Const tn₁, Const tn₂) →
              let n = k.add tn₁ tn₂ in
              if k.eq n k.zero then loop tnl
              else loop [(Const n, p₁) :: tnl]
          | _ →
              loop [(Plus t₁ t₂, p₁) :: tnl] ]
        else
          [(t₁, p₁) :: loop [(t₂, p₂) :: tnl]]
    | [tn] → [tn]
    | [] → [] ]
;
(*
value merge_expr_pow k eq =
  loop [] where rec loop rev_list =
    fun
    [ [(t₁, p₁) :: tnl₁] →
        let rev_list₁ =
          match rev_list with
          [ [(t₂, p₂) :: rev_list₂] →
              if eq p₁ p₂ then
                match (t₁, t₂) with
                [ (Const c₁, Const c₂) →
                    let n = k.add c₁ c₂ in
                    if k.eq n k.zero then rev_list₂
                    else [(Const n, p₁) :: rev_list₂]
                | _ →
                    [(Plus t₁ t₂, p₁) :: rev_list₂] ]
              else
                [(t₁, p₁) :: rev_list]
          | [] →
              [(t₁, p₁)] ]
        in
        loop rev_list₁ tnl₁
    | [] →
        List.rev rev_list ]
;
*)

value tree_pow_list_y (k : field _) t =
  let (is_neg, t) =
    match t with
    [ Neg t → (True, t)
    | _ → (False, t) ]
  in
  let tl = sum_tree_of_tree t in
  let tnl = List.map (tree_with_pow_y k) tl in
  let tnl = List.sort (compare_expr_pow \-) tnl in
  let tnl = merge_expr_pow k \= tnl in
  if is_neg then List.map (fun (t, n) → (Neg t, n)) tnl
  else tnl
;

value rec expr_with_pow_x k t =
  match t with
  [ Neg t →
      let (t, n) = expr_with_pow_x k t in
      (Neg t, n)
  | Mult t₁ (Xpower n d) →
      (t₁, Q.make (I.of_int n) (I.of_int d))
  | Xpower n d →
      (Const k.one, Q.make (I.of_int n) (I.of_int d))
  | Const _ →
      (t, Q.zero)
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

value const_pow_list_x (k : field _) t =
  let (is_neg, t) =
    match t with
    [ Neg t → (True, t)
    | _ → (False, t) ]
  in
  let tl = sum_tree_of_tree t in
  let tpl = List.map (expr_with_pow_x k) tl in
  let tpl = List.sort (compare_expr_pow Q.compare) tpl in
  let tpl = merge_expr_pow k Q.eq tpl in
  let cpl = List.map (fun (t, p) → (const_of_tree k t, p)) tpl in
  if is_neg then List.map (fun (c, n) → (k.neg c, n)) cpl
  else cpl
;
