(* $Id: roots.mli,v 1.6 2013-03-31 22:09:23 deraugla Exp $ *)

open Pnums;
open Field;
open Poly_tree;

value quiet : ref bool;
value roots : field α float → polynomial α int → list (α * int);
