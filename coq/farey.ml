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
0/1                             1/0
                1/1
        1/2             2/1
    1/3     2/3     3/2     3/1
*)
(*
0                               1
                 2
         3               4
     5        6      7       8
   9   10  11  12  13  14  15
*)
(*
0                                        1
                   10
         11                  100
    101       110       111       1000
 1001 1010 1011 1100 1101 1110 1111 10000
   9   10  11  12  13  14  15
*)
(*
-1                                      0
                   1
         10                   11
    100       101       110       111
 1000 1001 1010 1011 1100 1101 1110 1111
*)

(*
   2n   :    ?-n
   2n+1 :    n-?
left(2n)=left(n)
right(2n)=n
left(2n+1)=n
right(2n+1)=right(n)
*)

let rec left n =
  if n = -1 then 42
  else if n = 0 then 43
  else if n = 1 then -1
  else if n mod 2 = 0 then left (n / 2)
  else n / 2
;;

let rec right n =
  if n = -1 then 44
  else if n = 0 then 45
  else if n = 1 then 0
  else if n mod 2 = 0 then n / 2
  else right (n / 2)
;;

List.map (fun i -> (left i, i, right i)) (List.init 17 (fun i -> i - 1));;

let rec ff' n =
  if n = -1 then (0, 1)
  else if n = 0 then (1, 0)
  else
    let (a, b) = ff' (left n) in
    let (a', b') = ff' (right n) in
    (a + a', b + b')
;;


let ff n = ff' (n - 1);;

let rec ff1 n =
  if n = 0 then (0, 1)
  else if n = 1 then (1, 0)
  else
    let (a, b) = ff1 (left (n - 1) + 1) in
    let (a', b') = ff1 (right (n - 1) + 1) in
    (a + a', b + b')
;;

let rec left2 n =
  if n = 0 then 42
  else if n = 1 then 43
  else if n = 2 then -1
  else if n mod 2 = 0 then n / 2 - 1
  else left2 (n / 2 + 1)
;;

let rec right2 n =
  if n = 0 then 45
  else if n = 1 then 46
  else if n = 2 then 1
  else if n mod 2 = 0 then right2 (n / 2)
  else n / 2 + 1
;;

let rec ff2 n =
  if n = 0 then (0, 1)
  else if n = 1 then (1, 0)
  else
    let (a, b) = ff2 (left2 n + 1) in
    let (a', b') = ff2 (right2 n) in
    (a + a', b + b')
;;

List.map (fun i -> i, ff i) (List.init 32 (fun i -> i ));;
List.map (fun i -> i, ff1 i) (List.init 32 (fun i -> i ));;
List.map (fun i -> i, ff2 i) (List.init 32 (fun i -> i ));;

(*
0        0/1
1        1/0

2        1/1

3        1/2
4        2/1

5        1/3
6        2/3
7        3/2
8        3/1

9        1/4
10       2/5
11       3/5
12       3/4
13       4/3
14       5/3
15       5/2
16       4/1

0        0/1
1        1/0
2^i      i/1
2^i+1    1/i+1
*)

(*
(* including ∞ at 0 *)
let rec f n =
  if n = 0 then (1, 0)
  else if n = 1 then (0, 1)
  else
    let (a, b) = f ((n - 1) / 2 + 1) in
    if n mod 2 = 0 then (a + b, b)
    else (b, a + b)
;;
*)

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
