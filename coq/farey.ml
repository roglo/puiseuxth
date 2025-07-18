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

(* definitions of gcd and int power *)

let rec gcd a b = if b = 0 then a else gcd b (a mod b);;

let rec pow a =
  function
  | 0 -> 1
  | 1 -> a
  | n ->
      let b = pow a (n / 2) in
      b * b * (if n mod 2 = 0 then 1 else a)
;;

(* version ℕ → ℚ⁺ including ∞ = 1/0 *)
(* Stern-Brocot tree *)

(* right3 = https://oeis.org/A003602 *)
let right3 n = (n / gcd (pow 2 n) n + 1) / 2;;
let left3 n =
  match right3 (n - 1) with
  | 1 -> 0
  | k -> k
;;

let rec ff n =
  if n = 0 then (0, 1)
  else if n = 1 then (1, 0)
  else
    let (a, b) = ff (left3 n) in
    let (a', b') = ff (right3 n) in
    (a + a', b + b')
;;

List.map (fun i -> i, ff i) (List.init 32 (fun i -> i ));;

let rec gg (a, b) =
  if a = 0 then 0
  else if b = 0 then 1
  else 42
;;

List.map (fun i -> i, (gg (ff i))) (List.init 32 (fun i -> i ));;

(* *)

let rec fff n =
  if n = 0 then (1, 0)
  else if n = 1 then (0, 1)
  else
    let (a, b) = fff ((n - 1) / 2 + 1) in
    if n mod 2 = 0 then (a + b, b)
    else (b, a + b)
;;

let rec ggg (a, b) =
  if b = 0 then 0
  else if a = 0 then 1
  else if a < b then 2 * ggg (b - a, a) - 1
  else 2 * (ggg (a - b, b))
;;

List.map (fun i -> i, ggg (fff i)) (List.init 32 (fun i -> i ));;
List.map (fun ab -> ab, fff (ggg ab))
  (List.flatten (List.init 5 (fun a -> List.init 5 (fun b -> (a, b)))));;

... merde c'et pas ça...
