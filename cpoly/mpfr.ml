(* $Id: mpfr.mli,v 1.3 2013-04-02 16:15:30 deraugla Exp $ *)

type t = 'abstract;

external abs : t → t = "ml_mpfr_abs";
external neg : t → t = "ml_mpfr_neg";
external add : t → t → t = "ml_mpfr_add";
external sub : t → t → t = "ml_mpfr_sub";
external mul : t → t → t = "ml_mpfr_mul";
external mul_si : t → int → t = "ml_mpfr_mul_si";
external div : t → t → t = "ml_mpfr_div";
external div_si : t → int → t = "ml_mpfr_div_si";
external pow : t → t → t = "ml_mpfr_pow";
external sqr : t → t = "ml_mpfr_sqr";
external sqrt : t → t = "ml_mpfr_sqrt";
external exp : t → t = "ml_mpfr_exp";
external log : t → t = "ml_mpfr_log";
external cos : t → t = "ml_mpfr_cos";
external sin : t → t = "ml_mpfr_sin";
external atan2 : t → t → t = "ml_mpfr_atan2";
external cmp : t → t → int = "ml_mpfr_cmp";
external to_float : t → float = "ml_mpfr_to_float";
external of_float : float → t = "ml_mpfr_of_float";
external set_default_prec : int → unit = "ml_mpfr_set_default_prec";
external get_prec : t → int = "ml_mpfr_get_prec";
external with_prec : int → t → t = "ml_mpfr_with_prec";

external of_string : int → string → t = "ml_mpfr_of_string";
(** [of_string p s] returns the mpfr float of [s] with precision [p] *)
external to_string : int → int → t → (string * int) = "ml_mpfr_to_string";
(** [to_string base size x]. When [size] is zero, the significand is
    chosen large enough so that re-reading the printed value with the
    same precision. *)
