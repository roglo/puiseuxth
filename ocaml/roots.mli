(* $Id: roots.mli,v 1.15 2013-04-06 12:49:39 deraugla Exp $ *)

open Pnums;
open Field;
open Poly;

value verbose : ref bool;
value roots : field α β → polynomial α → list (α * int);
