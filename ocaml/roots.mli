(* $Id: roots.mli,v 1.7 2013-04-01 06:40:29 deraugla Exp $ *)

open Pnums;
open Field;
open Poly_tree;

value quiet : ref bool;
(**)
value roots : field α float → polynomial α int → list (α * int);
(*
value roots : field M.t Cpoly.Mfl.t → polynomial M.t int → list (M.t * int);
*)
