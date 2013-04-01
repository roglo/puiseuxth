(* $Id: roots.mli,v 1.9 2013-04-01 10:21:52 deraugla Exp $ *)

open Pnums;
open Field;
open Poly_tree;

value quiet : ref bool;
(**)
value roots : field α float → polynomial α int → list (α * int);
(*
value roots : field α Cpoly.Mfl.t → polynomial α int → list (α * int);
*)
