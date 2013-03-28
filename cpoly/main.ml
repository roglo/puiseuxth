(* $Id: main.ml,v 1.1 2013-03-28 13:24:19 deraugla Exp $ *)

open Printf;
open Cpoly;

(*

               DRIVER TO TEST CPOLY

*)

value prtc p = do {
  printf "\n\n COEFFICIENTS\n";
  for i = 0 to Array.length p - 1 do {
    printf "%s%s\n%!" (Mfl.to_string p.(i).re) (Mfl.to_string p.(i).im)
  }
};

value prtz z = do {
  printf "\n\n ZEROS\n";
  for i = 0 to Array.length z - 1 do {
    printf "%s%s\n%!" (Mfl.to_string z.(i).re) (Mfl.to_string z.(i).im)
  }
};

(*
  CHECKS THE ZEROS OF A COMPLEX POLYNOMIAL.
*)
(*
value pchk op zero = do {
  let degree = Array.length op - 1 in
  let s = Array.create degree complex_zero in
  let sum = ref complex_zero in
  for i = 0 to degree - 1 do {
    sum.val := complex_zero;
    for j = 0 to degree do {
      let sr =
        op.(j).re +. sum.val.re *. zero.(i).re -. sum.val.im *. zero.(i).im
      in
      let si =
        op.(j).im +. sum.val.re *. zero.(i).im +. sum.val.im *. zero.(i).re
      in
      sum.val := {re = sr; im = si};
    };
    s.(i) := sum.val;
  };
  let maxc = ref 0.0 in
  for i = 0 to degree - 1 do {
    let val = sqrt (op.(i).re *. op.(i).re +. op.(i).im *. op.(i).im) in
    maxc.val := max maxc.val val;
  };
  printf "\n\n CHECK\n%!";
  for i = 0 to degree - 1 do {
    let val = sqrt (s.(i).re*.s.(i).re +. s.(i).im*.s.(i).im) /. maxc.val in
    printf "%20.10E%20.10E  err=%20.10E\n%!" s.(i).re s.(i).im val;
  };
  printf "\n%!";
};
*)

value complex_combine pr pi =
  Array.of_list
    (List.map2 (fun r i → {re = Mfl.float r; im = Mfl.float i})
       (Array.to_list pr) (Array.to_list pi))
;

value main () = do {
  Mfl.set_prec 53;
  printf "1EXAMPLE 1.  POLYNOMIAL WITH ZEROS 1,2,...,10.\n";
  let pr =
    [| 1.; -55.; 1320.; -18150.; 157773.; -902055.; 3416930.; -8409500.;
       12753576.; -10628640.; 3628800. |]
  in
  let p = Array.map (fun r → {re = Mfl.float r; im = Mfl.zero}) pr in
  prtc p;
  match cpoly p with
  [ Some z → do { prtz z; (* pchk p z *) }
  | None → printf "\n\n CPOLY HAS FAILED ON THIS EXAMPLE\n%!" ];
  printf "\n%!";
  printf "1EXAMPLE 2. ZEROS ON IMAGINARY AXIS DEGREE 3.\n%!";
  let pr = [| 1.; 0.; -10001.0001; 0. |] in
  let pi = [| 0.; -10001.0001; 0.; 1. |] in
  let p = complex_combine pr pi in
  prtc p;
  match cpoly p with
  [ Some z → do { prtz z; (* pchk p z *) }
  | None → printf "\n\n CPOLY HAS FAILED ON THIS EXAMPLE\n%!" ];
  printf "\n%!";
  printf "1EXAMPLE 3. ZEROS AT 1+I,1/2*(1+I)....1/(2**-9)*(1+I)\n%!";
  let pr =
    [| 1.0; -1.998046875; 0.0; 0.7567065954208374;
       -0.2002119533717632; 1.271507365163416e-2; 0.; -1.154642632172909e-5;
       1.584803612786345e-7; -4.652065399568528e-10; 0. |]
  in
  let pi =
    [| 0.; pr.(1); 2.658859252929688; -7.567065954208374e-1;
       0.; pr.(5); -7.820779428584501e-4; Pervasives.\~-. pr.(7);
       0.; pr.(9); 9.094947017729282e-13 |]
  in
  let p = complex_combine pr pi in
  prtc p;
  match cpoly p with
  [ Some z → do { prtz z; (* pchk p z *) }
  | None → printf "\n\n CPOLY HAS FAILED ON THIS EXAMPLE\n%!" ];
  printf "\n%!";
  printf "1EXAMPLE 4. MULTIPLE ZEROS\n%!";
  let pr =
    [| 1.; -10.; 3.; 284.; -1293.; 2374.; -1587.; -920.; 2204.;
       -1344.; 288. |]
  in
  let pi =
    [| 0.; -10.; 100.; -334.; 200.; 1394.; -3836.; 4334.; -2352.;
       504.; 0. |]
  in
  let p = complex_combine pr pi in
  prtc p;
  match cpoly p with
  [ Some z → do { prtz z; (* pchk p z *) }
  | None → printf "\n\n CPOLY HAS FAILED ON THIS EXAMPLE\n%!" ];
  printf "\n%!";
  printf "1EXAMPLE 5. 12 ZEROS EVENLY DISTRIBUTE ";
  printf "ON A CIRCLE OF RADIUS 1. CENTERED AT 0+2I.\n%!";
  let pr =
    [| 1.; 0.; -264.; 0.; 7920.; 0.; -59136.; 0.; 126720.; 0.; -67584.;
       0.; 4095. |]
  in
  let pi =
    [| 0.; -24.; 0.; 1760.; 0.; -25344.; 0.; 101376.; 0.; -112640.; 0.;
       24576.; 0. |]
  in
  let p = complex_combine pr pi in
  prtc p;
  match cpoly p with
  [ Some z → do { prtz z; (* pchk p z *) }
  | None → printf "\n\n CPOLY HAS FAILED ON THIS EXAMPLE\n%!" ];
};

main ();
