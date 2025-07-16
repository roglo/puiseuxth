(* integer to rational making all rationals which are always reduced
   inspired from Farey sequences *)

(*
      | (0, 1)       if n = 0
f n = | (b, a + b)   if n even and f (n / 2) = (a, b)
      | (a + b, b)   if n odd and f (n / 2) = (a, b)

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
