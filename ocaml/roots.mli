(* $Id: roots.mli,v 1.5 2013-03-30 01:26:44 deraugla Exp $ *)

open Pnums;
open Field;
open Poly_tree;

value quiet : ref bool;
value roots : field α → polynomial α int → list (α * int);
