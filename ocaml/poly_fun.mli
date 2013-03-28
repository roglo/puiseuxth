(* $Id: poly_fun.mli,v 1.1 2013-03-28 13:24:20 deraugla Exp $ *)

open Pnums;

value poly_eucl_div : list I.t → list I.t → (list I.t * list I.t);
value poly_gcd : list I.t → list I.t → list I.t;
