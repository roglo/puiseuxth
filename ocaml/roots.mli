(* $Id: roots.mli,v 1.10 2013-04-01 10:51:45 deraugla Exp $ *)

open Pnums;
open Field;
open Poly_tree;

value quiet : ref bool;
value roots : field α β → polynomial α int → list (α * int);
