(* implementation of rationals with the normal rationals of
   coq (library QArith) together with a field saying that the
   numerator and the denominator are coprimes. This allows to
   use normal equality instead of ==. Therefore rewrite is
   possible. *)

From Stdlib Require Import Utf8.

Require Import QGArith.

Require Import RingLike.Core.

Definition QG_ring_like_op : ring_like_op QG :=
  {| rngl_zero := 0%QG;
     rngl_add := QG_add;
     rngl_mul := QG_mul;
     rngl_opt_one := Some 1%QG;
     rngl_opt_opp_or_subt := Some (inl QG_opp);
     rngl_opt_inv_or_quot := Some (inl QG_inv);
     rngl_opt_is_zero_divisor := Some (λ _, True);
     rngl_opt_eq_dec := Some QG_eq_dec;
     rngl_opt_leb := Some QG_leb |}.

Definition QG_ring_like_ord :=
  let _ := QG_ring_like_op in
  {| rngl_ord_le_dec := QG_le_dec;
     rngl_ord_le_refl := QG_le_refl;
     rngl_ord_le_antisymm := QG_le_antisymm;
     rngl_ord_le_trans := QG_le_trans;
     rngl_ord_add_le_compat := QG_add_le_compat;
     rngl_ord_mul_le_compat_nonneg := QG_mul_le_compat_nonneg;
     rngl_ord_mul_le_compat_nonpos := QG_mul_le_compat_nonpos;
     rngl_ord_not_le := QG_not_le |}.

Theorem QG_integral :
  let roq := QG_ring_like_op in
  ∀ a b : QG,
  (a * b)%QG = 0%QG
  → a = 0%QG ∨ b = 0%QG ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
now right; right; left.
Qed.

Definition QG_ring_like_prop (ro := QG_ring_like_op) : ring_like_prop QG :=
  {| rngl_mul_is_comm := true;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := QG_add_comm;
     rngl_add_assoc := QG_add_assoc;
     rngl_add_0_l := QG_add_0_l;
     rngl_mul_assoc := QG_mul_assoc;
     rngl_opt_mul_1_l := QG_mul_1_l;
     rngl_mul_add_distr_l := QG_mul_add_distr_l;
     rngl_opt_mul_comm := QG_mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_diag_l := QG_add_opp_diag_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_sub_0_l := NA;
     rngl_opt_mul_inv_diag_l := QG_mul_inv_diag_l;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_integral := QG_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := QG_characteristic_prop;
     rngl_opt_ord := QG_ring_like_ord;
     rngl_opt_archimedean := QG_archimedean |}.
