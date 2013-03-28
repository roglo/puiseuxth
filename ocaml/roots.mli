(* $Id: roots.mli,v 1.3 2013-03-28 21:37:59 deraugla Exp $ *)

open Pnums;
open Field;

value quiet : ref bool;
value roots : field α → list (α * int) → list (α * int);
