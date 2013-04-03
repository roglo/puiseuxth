(* $Id: roots.mli,v 1.12 2013-04-03 08:51:42 deraugla Exp $ *)

open Pnums;
open Field;
open Poly;

value verbose : ref bool;
value roots : field α β → polynomial α int → list (α * int);
