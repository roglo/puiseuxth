(* $Id: roots.mli,v 1.17 2013-05-30 19:29:45 deraugla Exp $ *)

open Pnums;
open Field;
open Poly;

value verbose : ref bool;
value roots : field α (ext α _) → polynomial α → list (α * int);
