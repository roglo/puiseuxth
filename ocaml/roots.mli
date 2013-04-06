(* $Id: roots.mli,v 1.14 2013-04-06 11:07:28 deraugla Exp $ *)

open Pnums;
open Field;
open Poly;

value verbose : ref bool;
value roots : field α β → old_polynomial α → list (α * int);
