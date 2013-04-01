(* $Id: roots.mli,v 1.11 2013-04-01 23:33:05 deraugla Exp $ *)

open Pnums;
open Field;
open Poly_tree;

value verbose : ref bool;
value roots : field α β → polynomial α int → list (α * int);
