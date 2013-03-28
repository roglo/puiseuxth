(* $Id: roots.mli,v 1.1 2013-03-28 13:24:20 deraugla Exp $ *)

open Pnums;
open Pnums_sig;

value quiet : ref bool;
value roots : field C.t → list (C.t * int) → list (C.t * int);
