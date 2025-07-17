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

(*
0 (0, 1)
1 (1, 0)

2 0-1 (1, 1)

3 0-2 (1, 2)
4 2-1 (2, 1)

5 0-3 (1, 3)
6 3-2 (2, 3)
7 2-4 (3, 2)
8 4-1 (3, 1)

9 0-5 (1, 4)
10 5-3 (2, 5)
11 3-6 (3, 5)
12 6-2 (3, 4)
13 2-7 (4, 3)
14 7-4 (5, 3)
15 4-8 (5, 2)
16 8-1 (4, 1)
*)

let rec g (a, b) =
  if b = 0 then 0
  else if a < b then 2 * g (b - a, a)
  else 2 * g (a - b, b) + 1
;;
