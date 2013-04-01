(* $Id: cpoly.mli,v 1.4 2013-04-01 11:18:59 deraugla Exp $ *)

(* Jenkins-Traub's algorithm for computing roots *)

module Mfl :
  sig
    type t = α;
    value abs : t → t;
    value neg : t → t;
    value add : t → t → t;
    value sub : t → t → t;
    value mul : t → t → t;
    value div : t → t → t;
    value pow : t → t → t;
    value sqrt : t → t;
    value exp : t → t;
    value log : t → t;
    value cmp : t → t → int;
    value eq : t → t → bool;
    value int : int → t;
    value float : float → t;
    value zero : t;
    value one : t;
    value set_prec : int → unit;
    value epsilon_float : int → t;
    value max_float : unit → t;
    value min_float : unit → t;
    value to_raw_string : t → string;
    value to_nice_string : int → int → t → (string * int);
    value to_float : t → float;
    value of_string : string → t;
  end;

type complex α = { re : α; im : α };
value map_complex : (α → β) → complex α → complex β;

value cpoly : array (complex Mfl.t) → option (array (complex Mfl.t));

value mroots : list (complex Mfl.t) → list (complex Mfl.t);
value roots : list (complex float) → list (complex float);
value froots : list float → list (complex float);
value iroots : list int → list (complex float);

value mcon : int → (Mfl.t * Mfl.t * Mfl.t * Mfl.t);
value cmod : complex Mfl.t → Mfl.t;
