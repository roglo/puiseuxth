(* $Id: roots.mli,v 1.13 2013-04-06 08:33:57 deraugla Exp $ *)

open Pnums;
open Field;
open Poly;

value verbose : ref bool;
value roots : field α β → polynomial α → list (α * int);
