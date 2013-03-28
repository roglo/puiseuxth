(* $Id: poly_print.ml,v 1.2 2013-03-28 16:07:39 deraugla Exp $ *)

#load "q_MLast.cmo";
#load "./q_def_expr.cmo";

open Printf;
open Pnums;

value with_sqrt_x = ref False;
value cut_long_strings = ref False;

value loc = Ploc.dummy;

value rec without_initial_neg =
  fun
  [ << - $e$ >> → Some e
  | << - $e₁$ - $e₂$ >> →
      Some << $e₁$ + $e₂$ >>
  | << $e₁$ - $e₂$ >> →
      match without_initial_neg e₁ with
      [ Some e₁ → Some << $e₁$ + $e₂$ >>
      | None → None ]
  | << $e₁$ + $e₂$ >> →
      match without_initial_neg e₁ with
      [ Some e₁ →
          match without_initial_neg e₂ with
          [ Some e₂ → Some << $e₁$ + $e₂$ >>
          | None → None ]
      | None → None ]
  | << $e₁$ * $e₂$ >> →
      match without_initial_neg e₁ with
      [ Some e₁ → Some << $e₁$ * $e₂$ >>
      | None → None ]
  | << $e₁$ * $e₂$ / $e₃$ >> →
      match without_initial_neg e₁ with
      [ Some e₁ → Some << $e₁$ * $e₂$ / $e₃$ >>
      | None → None ]
  | << $int:s$ >> →
      if I.lt (I.os s) I.zero then
        Some << $int:I.ts (I.neg (I.os s))$ >>
      else None
  | << $int:n$ / $int:d$ >> →
      if I.lt (I.os n) I.zero then
        Some << $int:I.ts (I.neg (I.os n))$ / $int:d$ >>
      else
        None
  | _ → None ]
;

value a₂_type =
  fun
  [ << $int:n₁$ / $int:d₁$ + $int:r$ ** (1/2) / $int:d₂$ >> →
      if d₁ = d₂ then
        let q₁ = Q.make (I.os n₁) (I.os d₁) in
        let q₂ = Q.make I.one (I.os d₂) in
        Some (A₂.make q₁ q₂ (I.os r))
      else None
  | << $int:n₁$ / $int:d₁$ + $int:n₂$ * $int:r$ ** (1/2) / $int:d₂$ >> →
      if d₁ = d₂ then
        let q₁ = Q.make (I.os n₁) (I.os d₁) in
        let q₂ = Q.make (I.os n₂) (I.os d₂) in
        Some (A₂.make q₁ q₂ (I.os r))
      else None

  | << - $int:n₁$ / $int:d₁$ - $int:n₂$ * $int:r$ ** (1/2) / $int:d₂$ >> →
      failwith "fuck 1"
  | << - $int:n₁$ / $int:d₁$ + $int:n₂$ * $int:r$ ** (1/2) / $int:d₂$ >> →
      failwith "fuck 2"
  | << $int:n₁$ / $int:d₁$ - $int:n₂$ * $int:r$ ** (1/2) / $int:d₂$ >> →
      failwith "fuck 3"
  | _ → None ]
;

value gen_string_of_expr airy opt =
  let rec expr ai e =
    match e with
    [ << $e₁$ + $e₂$ >> →
        match a₂_type e with
        [ Some a → A₂.to_string (not opt) a
        | None →
            match without_initial_neg e₂ with
            [ Some e₂ → sprintf "%s%s-%s%s" (expr ai e₁) ai ai (expr₁ e₂)
            | None → sprintf "%s%s+%s%s" (expr ai e₁) ai ai (expr₁ e₂) ] ]
    | << $e₁$ - $e₂$ >> →
        match a₂_type e with
        [ Some a → A₂.to_string (not opt) a
        | None → sprintf "%s%s-%s%s" (expr ai e₁) ai ai (expr₁ e₂) ]
    | e →
        expr₁ e ]
  and expr₁ =
    fun
    [ << - $e$ >> → sprintf "-%s" (expr₂ e)
    | << $int:s$ >> as e → if I.lt (I.os s) I.zero then s else expr₂ e
    | e → expr₂ e ]
  and expr₂ =
    fun
    [ << $int:s$ * $e₂$ >> →
        match s with
        [ "1" → expr₃ e₂
        | "-1" → sprintf "-%s" (expr₃ e₂)
        | _ → sprintf "%s%s%s" s (if opt then "" else "*") (expr₃ e₂) ]
    | << $e₁$ * $e₂$ >> →
        if opt then sprintf "%s%s" (expr₂ e₁) (expr₃ e₂)
        else sprintf "%s*%s" (expr₂ e₁) (expr₃ e₂)
    | << $e₁$ / 1 >> → expr₂ e₁
    | << $e₁$ / $e₂$ >> →
        match without_initial_neg e₁ with
        [ Some e₁ → sprintf "-%s/%s" (expr₂ e₁) (expr₃ e₂)
        | None → sprintf "%s/%s" (expr₂ e₁) (expr₃ e₂) ]
    | e → expr₃ e ]
  and expr₃ =
    fun
    [ << $int:d$ ** (1/2) >> →
        let d = I.os d in
        if I.eq d I.minus_one then "i"
        else if I.lt d I.zero then sprintf "i√%s" (I.ts (I.neg d))
        else sprintf "√%s" (I.ts d)
    | << $e₁$ ** $e₂$ >> →
        if with_sqrt_x.val then
          match (e₁, e₂) with
          [ (<< $lid:s$ >>, << $int:p$ / 2 >>) →
              let p = ios p in
              if p < 0 then sprintf "%s%s" s (power_expr e₂)
              else if p mod 2 = 0 then failwith "soe 2"
              else if p = 1 then sprintf "√%s" s
              else if p = 3 then sprintf "%s√%s" s s
              else sprintf "%s%s√%s" s (sup_string_of_string (soi (p/2))) s
          | (<< $lid:s$ >>, << $int:p$ / 3 >>) →
              let p = ios p in
              if p mod 3 = 0 then failwith "soe 3"
              else if p < 0 then sprintf "%s%s" s (power_expr e₂)
              else
                match p with
                [ 1 → sprintf "∛%s" s
                | 2 → sprintf "∛%s²" s
                | 4 → sprintf "%s∛%s" s s
                | _ →
                    sprintf "%s%s∛%s" s (sup_string_of_string (soi (p/3))) s ]
          | _ →
              if opt then sprintf "%s%s" (expr₄ e₁) (power_expr e₂)
              else sprintf "%s^%s" (expr₄ e₁) (expr "" e₂) ]
        else
          if opt then sprintf "%s%s" (expr₄ e₁) (power_expr e₂)
          else sprintf "%s^%s" (expr₄ e₁) (expr "" e₂)
    | e → expr₄ e ]
  and expr₄ =
    fun
    [ << $int:n$ >> → if I.ge (I.os n) I.zero then n else sprintf "(%s)" n
    | << $flo:n$ >> → sprintf "(%s)" n
    | << $lid:s$ >> → s
    | << $_$ + $_$ >> | << $_$ - $_$ >> | << $_$ * $_$ >> |
      << $_$ / $_$ >> | << $_$ ** $_$ >> | << - $_$ >> as e →
        match a₂_type e with
        [ Some a → expr "" e
        | _ → sprintf "(%s)" (expr "" e) ]
    | << $lid:s$ $_$ >> → failwith (sprintf "expr₄ app(%s,_)" s)
    | << $lid:s$ $_$ $_$ >> → failwith (sprintf "expr₄ app(%s,_,_)" s)
    | x → not_impl "string_of_expr" x ]
  and power_expr =
    fun
    [ << $int:i$ >> | << $int:i$ / 1 >> → sup_string_of_string i
    | << $int:n$ / $int:d$ >> → sup_string_of_string (n ^ "/" ^ d)
    | e → sup_string_of_string (expr "" e) ]
  in
  expr (if airy then " " else "")
;

value nbc c =
  if Char.code c < 0b10000000 then 1
  else if Char.code c < 0b11000000 then -1
  else if Char.code c < 0b11100000 then 2
  else if Char.code c < 0b11110000 then 3
  else if Char.code c < 0b11111000 then 4
  else if Char.code c < 0b11111100 then 5
  else if Char.code c < 0b11111110 then 6
  else -1
;

value utf8_strlen s =
  loop 0 0 where rec loop len i =
    if i ≥ String.length s then len
    else loop (len + 1) (i + nbc s.[i])
;

value rec byte_pos_after_n_chars s ib n =
  if ib ≥ String.length s then String.length s
  else if n ≤ 0 then ib
  else byte_pos_after_n_chars s (ib + nbc s.[ib]) (n - 1)
;

value utf8_sub_string s begc lenc =
  let begb = byte_pos_after_n_chars s 0 begc in
  let endb = byte_pos_after_n_chars s begb lenc in
  String.sub s begb (endb - begb)
;

value cut_string_of_expr airy opt e =
  let s = gen_string_of_expr airy opt e in
  if cut_long_strings.val then
    let len = utf8_strlen s in
    if len > 73 then
      utf8_sub_string s 0 35 ^ " ... " ^
      utf8_sub_string s (len - 35) 35
    else s
  else s
;

value string_of_expr = cut_string_of_expr False;
