(* integer to rational making all rationals which are always reduced
   inspired from Farey sequences *)

(*
defined as returning rational
      | 0                if n = 0
f n = | 1 / (f k + 1)    if n = 2 k
      | f k + 1          if n = 2 k + 1

defined as returning pair of naturals
      | (0, 1)       if n = 0
f n = | (b, a + b)   f (n / 2) = (a, b) and n even
      | (a + b, b)   f (n / 2) = (a, b) and n odd

           | 0                    if b = 0
g (a, b) = | 2 g (b - a, a)       if a < b
           | 2 g (a - b, b) + 1   otherwise
*)

let rec f n =
  if n = 0 then (0, 1)
  else
    let (a, b) = f (n / 2) in
    if n mod 2 = 0 then (b, a + b)
    else (a + b, b)
;;

let rec g (a, b) =
  if b = 0 then 0
  else if a < b then 2 * g (b - a, a)
  else 2 * g (a - b, b) + 1
;;

(* *)

let rec left n =
  if n = 0 then 0
  else if n mod 2 = 0 then n / 2 + 1
  else left (n / 2)
;;

let rec right n =
  if n = 0 then 1
  else if n mod 2 = 0 then right (n / 2 - 1)
  else n / 2 + 2
;;

(*
let right n = max 1 (left (n + 1));;
*)

let rec ff n =
  if n = 0 then (0, 1)
  else if n = 1 then (1, 0)
  else
    let (a, b) = ff (left (n - 2)) in
    let (a', b') = ff (right (n - 2)) in
    (a + a', b + b')
;;

List.map (fun i -> i, ff i) (List.init 32 (fun i -> i ));;
