(* $Id: roots.mli,v 1.8 2013-04-01 08:53:23 deraugla Exp $ *)

open Pnums;
open Field;
open Poly_tree;

value quiet : ref bool;
(**)
value roots : field C.t float → polynomial C.t int → list (C.t * int);
(*
value roots : field M.t Cpoly.Mfl.t → polynomial M.t int → list (M.t * int);
*)
