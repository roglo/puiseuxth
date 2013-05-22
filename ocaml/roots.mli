(* $Id: roots.mli,v 1.16 2013-05-22 14:38:51 deraugla Exp $ *)

open Pnums;
open Field;
open Poly;

value verbose : ref bool;
value roots : field α (ext α _) → old_poly α → list (α * int);
