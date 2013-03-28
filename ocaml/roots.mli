(* $Id: roots.mli,v 1.2 2013-03-28 20:01:35 deraugla Exp $ *)

open Pnums;
open Field;

value quiet : ref bool;
value roots : field C.t → list (C.t * int) → list (C.t * int);
