(* $Id: roots.mli,v 1.4 2013-03-30 00:52:29 deraugla Exp $ *)

open Pnums;
open Field;
open Poly_tree;

value quiet : ref bool;
value roots : field α → list (monomial α int) → list (α * int);
