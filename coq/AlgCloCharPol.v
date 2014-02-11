(* AlgCloCharPol.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.
Require Import ArithRing.

Require Import Misc.
Require Import Field.
Require Import Newton.
Require Import Fsummation.
Require Import Fpolynomial.
Require Import Puiseux_base.
Require Import Puiseux_series.
Require Import CharactPolyn.

Set Implicit Arguments.

Definition apply_list α (f : field α) la x :=
  (List.fold_right (λ c accu, accu .* f x .+ f c) (.0 f) la)%K.

Definition apply_poly α (f : field α) pol :=
  apply_list f (al pol).

(* euclidean division of a polynomial by (x - c) *)

Fixpoint list_mod_div_mono α (f : field α) c al :=
  match al with
  | [] => []
  | [a₁ … al₁] => [apply_poly f (POL al)%pol c … list_mod_div_mono f c al₁]
  end.

Definition poly_div_mono α (f : field α) pol c :=
  match list_mod_div_mono f c (al pol) with
  | [] => POL []%pol
  | [m … ml] => POL ml%pol
  end.

Definition poly_mod_mono α (f : field α) pol c :=
  match list_mod_div_mono f c (al pol) with
  | [] => .0 f%K
  | [m … ml] => m
  end.

(* test
Load Q_field.
Definition Qtest_div cl c := poly_div_mono Q_field (POL cl)%pol c.
Definition Qtest_mod cl c := poly_mod_mono Q_field (POL cl)%pol c.
Eval vm_compute in Qtest_div [2#1; -3#1; 1#1 … []] (4#1).
Eval vm_compute in Qtest_mod [2#1; -3#1; 1#1 … []] (4#1).
Eval vm_compute in Qtest_div [-Qnat 5; -Qnat 13; Qnat 0; Qnat 4 … []] (- 1 # 2).
Eval vm_compute in Qtest_mod [-Qnat 5; -Qnat 13; Qnat 0; Qnat 4 … []] (- 1 # 2).
*)

(* n-th derivative divided by factorial n *)

Fixpoint comb n k :=
  match k with
  | 0%nat => 1%nat
  | S k₁ =>
      match n with
      | 0%nat => 0%nat
      | S n₁ => (comb n₁ k₁ + comb n₁ k)%nat
      end
  end.

Fixpoint mul_int α (f : field α) x n :=
  match n with
  | O => .0 f%K
  | S n₁ => (mul_int f x n₁ .+ f x)%K
  end.

Fixpoint coeff_list_deriv α (f : field α) la n i :=
  match la with
  | [] => []
  | [a₁ … la₁] =>
      [mul_int f a₁ (comb i n) … coeff_list_deriv f la₁ n (S i)]
  end.

Definition list_derivial α (f : field α) n la :=
  coeff_list_deriv f (List.skipn n la) n n.

Definition poly_derivial α (f : field α) n pol :=
  (POL (list_derivial f n (al pol)))%pol.

Fixpoint coeff_taylor_list α (f : field α) n la c k :=
  match n with
  | 0%nat => []
  | S n₁ =>
      [apply_list f (list_derivial f k la) c …
       coeff_taylor_list f n₁ la c (S k)]
  end.

Definition taylor_list α (f : field α) la c :=
  coeff_taylor_list f (length la) la c 0.

(* P(x+c) = P(c) + P'(c)/1!.x + P''(c)/2!.x² + ... *)
Definition taylor_poly α (f : field α) P c :=
  (POL (taylor_list f (al P) c))%pol.

Lemma apply_list_0 : ∀ α (f : field α) la,
  (apply_list f la .0 f .= f List.nth 0 la .0 f)%K.
Proof.
intros α f la.
destruct la as [| a]; [ reflexivity | simpl ].
rewrite fld_mul_0_r, fld_add_0_l; reflexivity.
Qed.

Lemma comb_lt : ∀ n k, (n < k)%nat → comb n k = 0%nat.
Proof.
intros n k Hnk.
revert k Hnk.
induction n; intros; simpl.
 destruct k; [ exfalso; omega | reflexivity ].

 destruct k; [ exfalso; omega | idtac ].
 apply Nat.succ_lt_mono in Hnk.
 rewrite IHn; [ idtac | assumption ].
 rewrite IHn; [ reflexivity | idtac ].
 apply Nat.lt_lt_succ_r; assumption.
Qed.

Lemma comb_id : ∀ n, comb n n = 1%nat.
Proof.
intros n.
induction n; [ reflexivity | simpl ].
rewrite IHn, comb_lt; [ idtac | apply Nat.lt_succ_r; reflexivity ].
rewrite Nat.add_0_r; reflexivity.
Qed.

Lemma mul_int_1_r : ∀ α (f : field α) a, (mul_int f a 1 .= f a)%K.
Proof. intros α f a; simpl; rewrite fld_add_0_l; reflexivity. Qed.

Theorem taylor_coeff_0 : ∀ α (f : field α) la k,
  (apply_list f (list_derivial f k la) .0 f .= f
   List.nth k la .0 f)%K.
Proof.
intros α f la k.
rewrite apply_list_0.
destruct k.
 destruct la; [ reflexivity | simpl ].
 rewrite fld_add_0_l; reflexivity.

 unfold list_derivial; simpl.
 destruct la as [| a]; [ reflexivity | simpl ].
 remember (List.skipn k la) as lb eqn:Hlb .
 symmetry in Hlb.
 destruct lb as [| b]; simpl.
  rewrite List.nth_overflow; [ reflexivity | idtac ].
  apply list_skipn_overflow_if; assumption.

  rewrite comb_id, comb_lt; [ idtac | apply Nat.lt_succ_r; reflexivity ].
  rewrite Nat.add_0_r, mul_int_1_r.
  erewrite list_skipn_cons_nth; [ reflexivity | eassumption ].
Qed.

Lemma taylor_formula_0_loop : ∀ α (f : field α) la x cnt n,
  length la = (cnt + n)%nat
  → (apply_list f (List.skipn n la) x .= f
     apply_list f (coeff_taylor_list f cnt la .0 f n) x)%K.
Proof.
intros α f la x cnt n Hlen.
revert la x n Hlen.
induction cnt; intros.
 simpl in Hlen; subst n; simpl.
 rewrite list_skipn_overflow; reflexivity.

 simpl.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hlen.
 rewrite <- IHcnt; [ idtac | assumption ].
 rewrite taylor_coeff_0; clear.
 revert x n.
 induction la as [| a]; intros.
  rewrite list_skipn_nil; simpl.
  rewrite fld_mul_0_l, fld_add_0_l.
  destruct n; reflexivity.

  destruct n; [ reflexivity | simpl ].
  rewrite IHla; reflexivity.
Qed.

Theorem list_skipn_0 : ∀ A (l : list A), List.skipn 0 l = l.
Proof. intros A l; destruct l; reflexivity. Qed.

Theorem taylor_formula_0 : ∀ α (f : field α) x P,
  (apply_poly f P x .= f
   apply_poly f (taylor_poly f P .0 f) x)%K.
Proof.
intros α f x P.
unfold apply_poly; simpl.
remember (al P) as la; clear Heqla.
unfold taylor_list.
rewrite <- taylor_formula_0_loop.
 rewrite list_skipn_0; reflexivity.

 rewrite Nat.add_0_r; reflexivity.
Qed.

Lemma mul_int_add_distr_r : ∀ α (f : field α) a b n,
  (mul_int f (a .+ f b) n .= f mul_int f a n .+ f mul_int f b n)%K.
Proof.
intros α f a b n.
revert a b.
induction n; intros; simpl; [ rewrite fld_add_0_l; reflexivity | idtac ].
rewrite IHn.
do 2 rewrite <- fld_add_assoc.
apply fld_add_compat_l.
rewrite fld_add_comm, <- fld_add_assoc.
apply fld_add_compat_l.
apply fld_add_comm.
Qed.

Lemma mul_int_add_distr_l : ∀ α (f : field α) a m n,
  (mul_int f a (m + n) .= f mul_int f a m .+ f mul_int f a n)%K.
Proof.
intros α f a m n.
revert a n.
induction m; intros; simpl.
 rewrite fld_add_0_l; reflexivity.

 rewrite IHm.
 apply fld_add_shuffle0.
Qed.

Lemma coeff_list_deriv_add : ∀ α (f : field α) la lb n i,
  list_eq f
    (coeff_list_deriv f (list_add f la lb) n i)
    (list_add f (coeff_list_deriv f la n i) (coeff_list_deriv f lb n i)).
Proof.
intros α f la lb n i.
revert lb n i.
induction la as [| a]; intros; [ reflexivity | simpl ].
destruct lb as [| b]; [ reflexivity | simpl ].
constructor; [ apply mul_int_add_distr_r | apply IHla ].
Qed.

Lemma list_derivial_nil : ∀ α (f : field α) k,
  list_eq f (list_derivial f k []) [].
Proof.
intros α f k.
unfold list_derivial.
rewrite list_skipn_nil; reflexivity.
Qed.

Lemma comb_0_r : ∀ i, comb i 0 = 1%nat.
Proof. intros i; destruct i; reflexivity. Qed.

Lemma mul_int_0_l : ∀ α (f : field α) n, (mul_int f .0 f n .= f .0 f)%K.
Proof.
intros α f n.
induction n; [ reflexivity | simpl ].
rewrite fld_add_0_r; assumption.
Qed.

Add Parametric Morphism α (f : field α) : (mul_int f)
  with signature fld_eq f ==> eq ==> fld_eq f
  as mul_int_morph.
Proof.
intros a b Hab n.
induction n; [ reflexivity | simpl ].
rewrite IHn, Hab; reflexivity.
Qed.

Add Parametric Morphism α (f : field α) : (coeff_list_deriv f)
  with signature list_eq f ==> eq ==> eq ==> list_eq f
  as coeff_list_deriv_morph.
Proof.
intros la lb Hlab n i.
revert lb Hlab n i.
induction la as [| a]; intros; simpl.
 revert i.
 induction lb as [| b]; intros; [ reflexivity | simpl ].
 apply list_eq_nil_cons_inv in Hlab.
 destruct Hlab as (Hb, Hlb).
 constructor; [ rewrite Hb; apply mul_int_0_l | idtac ].
 apply IHlb; assumption.

 destruct lb as [| b].
  simpl.
  apply list_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Ha, Hla).
  constructor; [ rewrite Ha; apply mul_int_0_l | idtac ].
  rewrite IHla with (lb := []); [ reflexivity | eassumption ].

  apply list_eq_cons_inv in Hlab.
  destruct Hlab as (Hab, Hlab).
  rewrite Hab; simpl.
  rewrite IHla; [ reflexivity | eassumption ].
Qed.

Lemma list_skipn_add : ∀ α (f : field α) k la lb,
  list_eq f (List.skipn k (list_add f la lb))
    (list_add f (List.skipn k la) (List.skipn k lb)).
Proof.
intros α f k la lb.
revert la lb.
induction k; intros; [ rewrite list_skipn_0; reflexivity | simpl ].
destruct la as [| a]; [ reflexivity | simpl ].
destruct lb as [| b]; [ simpl | apply IHk ].
rewrite list_add_nil_r; reflexivity.
Qed.

Lemma list_derivial_add : ∀ α (f : field α) la lb k,
  list_eq f
    (list_derivial f k (list_add f la lb))
    (list_add f (list_derivial f k la) (list_derivial f k lb)).
Proof.
intros α f la lb k.
unfold list_derivial.
rewrite list_skipn_add.
rewrite coeff_list_deriv_add.
reflexivity.
Qed.

Lemma length_deriv_list : ∀ α (f : field α) la n i,
  length (coeff_list_deriv f la n i) = length la.
Proof.
intros α f la n i.
revert i.
induction la as [| a]; intros; [ reflexivity | simpl ].
apply eq_S, IHla.
Qed.

Lemma coeff_list_deriv_0_l : ∀ α (f : field α) la i,
  list_eq f (coeff_list_deriv f la 0 i) la.
Proof.
intros α f la i; revert i.
induction la as [| a]; intros; [ reflexivity | simpl ].
rewrite comb_0_r, mul_int_1_r.
constructor; [ reflexivity | apply IHla ].
Qed.

Lemma list_derivial_0 : ∀ α (f : field α) la,
  list_eq f (list_derivial f 0 la) la.
Proof.
intros α f la.
unfold list_derivial.
rewrite list_skipn_0; simpl.
rewrite coeff_list_deriv_0_l; reflexivity.
Qed.

Lemma comb_neq_0 : ∀ n k, k ≤ n → comb n k ≠ O.
Proof.
intros n k Hkn.
revert k Hkn.
induction n; intros.
 apply Nat.le_0_r in Hkn; subst k.
 intros H; discriminate H.

 simpl.
 destruct k; [ intros H; discriminate H | idtac ].
 apply le_S_n in Hkn.
 intros H.
 apply Nat.eq_add_0 in H.
 destruct H as (H, _).
 revert H; apply IHn; assumption.
Qed.

Lemma comb_succ_l : ∀ n, comb (S n) n = S n.
Proof.
intros n.
induction n; [ reflexivity | idtac ].
remember (S n) as x; simpl; subst x.
rewrite IHn, comb_id, Nat.add_1_r; reflexivity.
Qed.

Lemma list_derivial_le : ∀ α (f : field α) k la,
  (length la ≤ k)%nat
  → list_eq f (list_derivial f k la) [].
Proof.
intros α f k la Hle.
unfold list_derivial.
rewrite list_skipn_overflow; [ reflexivity | assumption ].
Qed.

Lemma list_skipn_is_nil : ∀ α (f : field α) la n,
  list_eq f la []
  → list_eq f (List.skipn n la) [].
Proof.
intros α f la n Heq.
revert n.
induction la as [| a]; intros.
 rewrite list_skipn_nil; reflexivity.

 destruct n; [ assumption | simpl ].
 apply list_eq_cons_nil_inv in Heq.
 destruct Heq as (Ha, Hla).
 apply IHla; assumption.
Qed.

Add Parametric Morphism α (f : field α) : (@List.skipn α)
  with signature eq ==> list_eq f ==> list_eq f
  as list_skipn_morph.
Proof.
intros n la lb Hlab.
revert la lb Hlab.
induction n; intros.
 do 2 rewrite list_skipn_0; assumption.

 destruct la as [| a]; simpl.
  destruct lb as [| b]; [ reflexivity | simpl ].
  symmetry; apply list_skipn_is_nil; symmetry.
  apply list_eq_nil_cons_inv in Hlab.
  destruct Hlab; assumption.

  destruct lb as [| b].
   apply list_skipn_is_nil.
   apply list_eq_cons_nil_inv in Hlab.
   destruct Hlab; assumption.

   apply IHn.
   apply list_eq_cons_inv in Hlab.
   destruct Hlab; assumption.
Qed.

Add Parametric Morphism α (f : field α) : (list_derivial f)
  with signature eq ==> list_eq f ==> list_eq f
  as list_derivial_morph.
Proof.
intros k la lb Hlab.
unfold list_derivial.
destruct k.
 do 2 rewrite list_skipn_0; simpl.
 do 2 rewrite coeff_list_deriv_0_l; assumption.

 simpl.
 destruct la as [| a]; simpl.
  destruct lb as [| b]; [ reflexivity | simpl ].
  apply list_eq_nil_cons_inv in Hlab.
  destruct Hlab as (Hb, Hlb).
  rewrite <- Hlb, list_skipn_nil.
  reflexivity.

  destruct lb as [| b]; simpl.
   apply list_eq_cons_nil_inv in Hlab.
   destruct Hlab as (Ha, Hla).
   rewrite Hla, list_skipn_nil.
   reflexivity.

   apply list_eq_cons_inv in Hlab.
   destruct Hlab as (Hab, Hlab).
   rewrite Hlab.
   reflexivity.
Qed.

Lemma fold_apply_list : ∀ α (f : field α) al x,
  (List.fold_right (λ c accu : α, accu .* f x .+ f c) .0 f al)%K =
  apply_list f al x.
Proof. reflexivity. Qed.

Add Parametric Morphism α (f : field α) : (apply_list f)
  with signature list_eq f ==> fld_eq f ==> fld_eq f
  as apply_list_morph.
Proof.
intros la lb Hab x y Hxy.
revert lb Hab x y Hxy.
induction la as [| a]; intros; simpl.
 revert x y Hxy.
 induction lb as [| b]; intros; [ reflexivity | simpl ].
 apply list_eq_nil_cons_inv in Hab.
 destruct Hab as (Hb, Hlb).
 rewrite Hb, fld_add_0_r.
 rewrite <- IHlb; try eassumption.
 rewrite fld_mul_0_l; reflexivity.

 destruct lb as [| b].
  apply list_eq_cons_nil_inv in Hab.
  destruct Hab as (Ha, Hla).
  rewrite Ha, fld_add_0_r; simpl.
  rewrite IHla; try eassumption; simpl.
  rewrite fld_mul_0_l; reflexivity.

  simpl.
  apply list_eq_cons_inv in Hab.
  destruct Hab as (Hab, Hlab).
  unfold apply_list.
  rewrite Hab, Hxy.
  do 2 rewrite fold_apply_list.
  rewrite IHla; try eassumption.
  reflexivity.
Qed.

Add Parametric Morphism α (f : field α) : (apply_poly f)
  with signature eq_poly f ==> fld_eq f ==> fld_eq f
  as apply_poly_morph.
Proof.
intros p₁ p₂ Hpp v₁ v₂ Hvv.
unfold eq_poly in Hpp.
unfold apply_poly.
rewrite Hpp, Hvv; reflexivity.
Qed.

Lemma list_eq_map_ext : ∀ α (f : field α) A g h,
   (∀ a : A, fld_eq f (g a) (h a))
   → ∀ la, list_eq f (List.map g la) (List.map h la).
Proof.
intros α f A g h Hgh la.
induction la as [| a]; [ reflexivity | simpl ].
constructor; [ apply Hgh | assumption ].
Qed.

Lemma list_skipn_succ_cons : ∀ A (a : A) la k,
  List.skipn (S k) [a … la] = List.skipn k la.
Proof. reflexivity. Qed.

Lemma comb_1_r : ∀ n, comb n 1 = n.
Proof.
intros n.
induction n; [ reflexivity | simpl ].
rewrite comb_0_r, IHn; reflexivity.
Qed.

Lemma mul_int_assoc : ∀ α (f : field α) a m n,
  (mul_int f (mul_int f a m) n .= f mul_int f a (m * n))%K.
Proof.
intros α f a m n.
revert a m.
induction n; intros; [ rewrite Nat.mul_0_r; reflexivity | simpl ].
rewrite IHn.
symmetry.
rewrite Nat.mul_comm; simpl.
rewrite mul_int_add_distr_l.
rewrite fld_add_comm, Nat.mul_comm; reflexivity.
Qed.

Lemma mul_int_compat : ∀ α (f : field α) a b m n,
  (a .= f b)%K
  → (m = n)%nat
    → (mul_int f a m .= f mul_int f b n)%K.
Proof.
intros α f a b m n Hab Hmn.
rewrite Hab, Hmn; reflexivity.
Qed.

Lemma comb_succ_succ : ∀ n k,
  comb (S n) (S k) = (comb n k + comb n (S k))%nat.
Proof. intros; reflexivity. Qed.

Lemma comb_fact : ∀ m n,
  (comb (m + n) m * (fact m * fact n) = fact (m + n))%nat.
Proof.
intros m n.
revert m.
induction n; intros.
 rewrite Nat.add_0_r, comb_id; simpl.
 rewrite Nat.add_0_r, Nat.mul_1_r; reflexivity.

 induction m.
  simpl.
  do 2 rewrite Nat.add_0_r; reflexivity.

  rewrite Nat.add_succ_l.
  rewrite comb_succ_succ.
  rewrite Nat.mul_add_distr_r.
  replace (fact (S m)) with (S m * fact m)%nat by reflexivity.
  rewrite Nat.mul_comm.
  do 2 rewrite <- Nat.mul_assoc.
  rewrite Nat.mul_comm.
  do 3 rewrite Nat.mul_assoc.
  rewrite Nat.mul_comm in IHm; rewrite IHm.
  rewrite Nat.add_comm.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l.
  replace (fact (S n)) with (fact n * S n)%nat .
   rewrite Nat.mul_comm.
   do 2 rewrite <- Nat.mul_assoc.
   replace (S m * fact m)%nat with (fact (S m)) by reflexivity.
   rewrite Nat.mul_comm.
   do 2 rewrite <- Nat.mul_assoc.
   rewrite IHn.
   rewrite Nat.mul_comm, <- Nat.mul_add_distr_l.
   replace (S n + S m)%nat with (S (S m + n)) .
    rewrite Nat.mul_comm; reflexivity.

    simpl.
    apply eq_S.
    rewrite Nat.add_succ_r.
    apply eq_S, Nat.add_comm.

   rewrite Nat.mul_comm; reflexivity.
Qed.

Lemma comb_add : ∀ n k, comb (n + k) k = comb (n + k) n.
Proof.
intros n k.
pose proof (comb_fact n k) as Hnk.
pose proof (comb_fact k n) as Hkn.
rewrite Nat.add_comm in Hkn.
rewrite <- Hkn in Hnk.
rewrite Nat.mul_assoc, Nat.mul_shuffle0 in Hnk.
rewrite <- Nat.mul_assoc in Hnk.
apply Nat.mul_cancel_r in Hnk; [ symmetry; assumption | idtac ].
apply Nat.neq_mul_0; split; apply fact_neq_0.
Qed.

Lemma comb_add_succ_mul : ∀ n k,
  (comb (n + k) (S k) * S k = comb (n + k) k * n)%nat.
Proof.
intros n k.
revert k.
induction n; intros.
 simpl; rewrite comb_lt; [ ring | omega ].

 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 rewrite Nat.add_comm.
 pose proof (comb_fact (S k) n) as Hnk.
 replace (fact (S k)) with (S k * fact k)%nat in Hnk by reflexivity.
 do 2 rewrite Nat.mul_assoc in Hnk.
 apply Nat.mul_cancel_r with (p := (fact k * fact n)%nat).
  apply Nat.neq_mul_0; split; apply fact_neq_0.

  rewrite Nat.mul_assoc, Hnk.
  rewrite Nat.add_succ_l, <- Nat.add_succ_r.
  rewrite <- comb_fact; simpl; ring.
Qed.

Lemma comb_succ_succ_mul : ∀ n k,
  k ≤ n
  → (comb (S n) (S k) * S k = comb n k * (S n))%nat.
Proof.
intros n k Hkn.
destruct (eq_nat_dec k n) as [H₁| H₁].
 subst k.
 do 2 rewrite comb_id; reflexivity.

 apply le_neq_lt in Hkn; [ idtac | assumption ].
 rewrite comb_succ_succ.
 replace n with (n - k + k)%nat by omega.
 rewrite Nat.mul_add_distr_r.
 rewrite comb_add_succ_mul.
 replace (n - k + k)%nat with n by omega.
 rewrite <- Nat.mul_add_distr_l.
 replace (S k + (n - k))%nat with (S n) by omega.
 reflexivity.
Qed.

Lemma map_coeff_list_deriv_gen : ∀ α (f : field α) la n i,
  list_eq f
    (List.map (λ x, mul_int f x (S n)) (coeff_list_deriv f la (S n) (S n + i)))
    (coeff_list_deriv f (coeff_list_deriv f la 1 (S n + i)) n (n + i)).
Proof.
intros α f la n i.
revert n i.
induction la as [| a]; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
constructor; [ clear | do 2 rewrite <- Nat.add_succ_r; apply IHla ].
rewrite Nat.add_succ_l, comb_1_r.
do 2 rewrite mul_int_assoc.
apply mul_int_compat; [ reflexivity | idtac ].
rewrite comb_succ_succ_mul; [ apply Nat.mul_comm | apply Nat.le_add_r ].
Qed.

Lemma map_coeff_list_deriv : ∀ α (f : field α) la n,
  list_eq f
    (List.map (λ x, mul_int f x (S n)) (coeff_list_deriv f la (S n) (S n)))
    (coeff_list_deriv f (coeff_list_deriv f la 1 (S n)) n n).
Proof.
intros α f la n.
pose proof (map_coeff_list_deriv_gen f la n 0) as H.
do 2 rewrite Nat.add_0_r in H.
assumption.
Qed.

Lemma coeff_list_deriv_skipn : ∀ α (f : field α) la k i,
  list_eq f (coeff_list_deriv f (List.skipn k la) 1 (i + k))
    (List.skipn k (coeff_list_deriv f la 1 i)).
Proof.
intros α f la k i.
revert la i.
induction k; intros.
 rewrite Nat.add_0_r; reflexivity.

 destruct la as [| a]; [ reflexivity | simpl ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 apply IHk.
Qed.

Lemma list_derivial_succ : ∀ α (f : field α) la k,
  list_eq f (List.map (λ a, mul_int f a (S k)) (list_derivial f (S k) la))
    (list_derivial f k (list_derivial f 1 la)).
Proof.
intros α f la k.
unfold list_derivial; simpl.
destruct la as [| a].
 rewrite list_skipn_nil; reflexivity.

 pose proof (map_coeff_list_deriv f (List.skipn k la) k) as H.
 rewrite H.
 rewrite <- coeff_list_deriv_skipn; reflexivity.
Qed.

Lemma apply_list_compose_nil_r : ∀ α (f : field α) la x,
  (apply_list f (list_compose f la []) x .= f apply_list f la .0 f)%K.
Proof.
intros α f la x.
destruct la as [| a]; [ reflexivity | simpl ].
rewrite fld_mul_0_r, fld_add_0_l.
rewrite list_mul_nil_r, list_add_nil_l; simpl.
rewrite fld_mul_0_l, fld_add_0_l; reflexivity.
Qed.

Lemma apply_list_add : ∀ α (f : field α) la lb x,
  (apply_list f (list_add f la lb) x .= f
   apply_list f la x .+ f apply_list f lb x)%K.
Proof.
intros α f la lb x.
revert lb x.
induction la as [| a]; intros; simpl.
 rewrite fld_add_0_l; reflexivity.

 destruct lb as [| b]; simpl.
  rewrite fld_add_0_r; reflexivity.

  rewrite IHla.
  do 2 rewrite fld_add_assoc.
  apply fld_add_compat_r.
  rewrite fld_add_shuffle0.
  rewrite fld_mul_add_distr_r; reflexivity.
Qed.

Lemma list_eq_0 : ∀ α (f : field α), list_eq f [.0 f%K] [].
Proof. intros α f; constructor; reflexivity. Qed.

Lemma list_mul_cons_l : ∀ α (f : field α) a la lb,
  list_eq f (list_mul f [a … la] lb)
    (list_add f (list_mul f [a] lb) [.0 f%K … list_mul f la lb]).
Proof.
intros α f a la lb.
unfold list_mul.
apply list_nth_list_eq; intros k.
rewrite list_nth_list_convol_mul; [ idtac | reflexivity ].
rewrite list_nth_add.
rewrite list_nth_list_convol_mul; [ idtac | reflexivity ].
destruct k.
 rewrite summation_only_one.
 rewrite summation_only_one.
 rewrite fld_add_0_r; reflexivity.

 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite Nat.sub_0_r.
 symmetry.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite all_0_summation_0.
  rewrite Nat.sub_0_r.
  simpl.
  rewrite fld_add_0_r.
  apply fld_add_compat_l.
  rewrite list_nth_list_convol_mul; [ idtac | reflexivity ].
  rewrite summation_succ_succ; reflexivity.

  intros i (Hi, Hik); simpl.
  destruct i; [ exfalso; omega | simpl ].
  destruct i; rewrite fld_mul_0_l; reflexivity.
Qed.

Lemma list_mul_cons_r : ∀ α (f : field α) la b lb,
  list_eq f (list_mul f la [b … lb])
    (list_add f (list_mul f la [b]) [.0 f%K … list_mul f la lb]).
Proof.
intros α f la b lb.
rewrite list_mul_comm.
rewrite list_mul_cons_l.
rewrite list_mul_comm.
apply list_add_compat; [ reflexivity | idtac ].
rewrite list_mul_comm; reflexivity.
Qed.

Lemma list_convol_mul_cons_succ : ∀ α (f : field α) a b lb i len,
  list_eq f (list_convol_mul f [a] [b … lb] (S i) len)
    (list_convol_mul f [a] lb i len).
Proof.
intros α f a b lb i len.
revert a b lb i.
induction len; intros; [ reflexivity | idtac ].
constructor; [ idtac | apply IHlen ].
rewrite summation_succ; [ idtac | apply Nat.le_0_l ].
rewrite List.nth_overflow; [ idtac | simpl; fast_omega  ].
rewrite fld_mul_0_l, fld_add_0_r.
apply summation_compat; intros j (_, Hj).
apply fld_mul_compat_l.
rewrite Nat.sub_succ_l; [ reflexivity | assumption ].
Qed.

Lemma list_mul_cons : ∀ α (f : field α) a b la lb,
  list_eq f (list_mul f [a … la] [b … lb])
    [(a .* f b)%K
    … list_add f (list_add f (list_mul f la [b]) (list_mul f [a] lb))
        [.0 f%K … list_mul f la lb]].
Proof.
intros α f a b la lb.
rewrite list_mul_cons_l; simpl.
rewrite summation_only_one.
rewrite fld_add_0_r.
constructor; [ reflexivity | idtac ].
rewrite list_mul_cons_r.
unfold list_mul; simpl.
rewrite <- list_add_assoc.
apply list_add_compat; [ idtac | reflexivity ].
rewrite list_add_comm.
apply list_add_compat; [ reflexivity | idtac ].
apply list_convol_mul_cons_succ.
Qed.

Lemma apply_list_single : ∀ α (f : field α) a lb x,
  (apply_list f (list_mul f [a] lb) x .= f a .* f apply_list f lb x)%K.
Proof.
intros α f a lb x.
induction lb as [| b].
 simpl; rewrite fld_mul_0_r; reflexivity.

 rewrite list_mul_cons_r; simpl.
 rewrite summation_only_one, fld_add_0_r, IHlb.
 rewrite fld_mul_add_distr_l, fld_mul_assoc; reflexivity.
Qed.

Lemma apply_list_mul : ∀ α (f : field α) la lb x,
  (apply_list f (list_mul f la lb) x .= f
   apply_list f la x .* f apply_list f lb x)%K.
Proof.
intros α f la lb x.
revert lb x.
induction la as [| a]; intros; simpl.
 rewrite list_mul_nil_l, fld_mul_0_l; reflexivity.

 destruct lb as [| b]; simpl.
  rewrite list_mul_nil_r, fld_mul_0_r; reflexivity.

  rewrite list_mul_cons; simpl.
  rewrite apply_list_add; simpl.
  rewrite fld_add_0_r.
  rewrite apply_list_add.
  rewrite IHla.
  rewrite IHla.
  simpl.
  rewrite fld_mul_0_l, fld_add_0_l.
  do 3 rewrite fld_mul_add_distr_r.
  do 2 rewrite fld_mul_add_distr_l.
  do 2 rewrite fld_mul_assoc.
  rewrite fld_add_assoc.
  apply fld_add_compat_r.
  rewrite fld_add_comm, fld_add_assoc.
  do 2 rewrite <- fld_add_assoc.
  apply fld_add_compat.
   apply fld_mul_compat_r.
   apply fld_mul_shuffle0.

   apply fld_add_compat.
    apply fld_mul_shuffle0.

    apply fld_mul_compat_r.
    apply apply_list_single.
Qed.

Lemma apply_list_compose : ∀ α (f : field α) la lb x,
  (apply_list f (list_compose f la lb) x .= f
   apply_list f la (apply_list f lb x))%K.
Proof.
intros α f la lb x.
unfold list_compose.
revert lb x.
induction la as [| a]; intros; [ reflexivity | simpl ].
rewrite <- IHla; clear.
rewrite apply_list_add; simpl.
rewrite fld_mul_0_l, fld_add_0_l.
apply fld_add_compat_r.
apply apply_list_mul.
Qed.

Lemma apply_list_compose_add_sub : ∀ α (f : field α) la a x,
  (apply_list f (list_compose f la [a; .1 f … []]) (x .- f a) .= f
   apply_list f la x)%K.
Proof.
intros α f la a x.
rewrite apply_list_compose; simpl.
rewrite fld_mul_0_l, fld_add_0_l.
rewrite fld_mul_1_l.
rewrite fld_add_comm, fld_add_assoc.
rewrite fld_add_comm, fld_add_assoc.
rewrite fld_add_opp_l, fld_add_0_l; reflexivity.
Qed.

Lemma list_nth_taylor : ∀ α (f : field α) la n c k i,
  (n + k = length la)%nat
  → (List.nth i (coeff_taylor_list f n la c k) .0 f .= f
     apply_list f (list_derivial f (i + k) la) c)%K.
Proof.
intros α f la n c k i Hlen.
revert la c k i Hlen.
induction n; intros; simpl.
 rewrite list_derivial_le; [ destruct i; reflexivity | idtac ].
 rewrite <- Hlen.
 apply Nat.add_le_mono_r, Nat.le_0_l.

 destruct i; [ reflexivity | simpl ].
 rewrite <- Nat.add_succ_r.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hlen.
 apply IHn; assumption.
Qed.

(* ah bin non, faut la dérivée k-ième...
Lemma list_derivial_mul : ∀ α (f : field α) k la lb,
  list_eq f (list_derivial f 1 (list_mul f la lb))
    (list_add f
       (list_mul f la (list_derivial f 1 lb))
       (list_mul f (list_derivial f 1 la) lb)).
Proof.
intros α f k la lb.
bbb.
*)

Lemma list_derivial_compose_deg_1 : ∀ α (f : field α) k la b,
  list_eq f (list_derivial f k (list_compose f la [b; .1 f%K … []]))
    (list_compose f (list_derivial f k la) [b; .1 f%K … []]).
Proof.
intros α f k la b.
revert la b.
induction k; intros; simpl.
 destruct la as [| a]; simpl.
  rewrite list_derivial_nil; reflexivity.

  rewrite list_derivial_add.
bbb.

Lemma zzz : ∀ α (f : field α) a la,
  list_eq f
    (taylor_list f (list_compose f la [a; .1 f … []]) .0 f)%K
    (taylor_list f la a).
Proof.
intros α f a la.
apply list_nth_list_eq; intros k.
unfold taylor_list.
rewrite list_nth_taylor; [ idtac | rewrite Nat.add_0_r; reflexivity ].
rewrite list_nth_taylor; [ idtac | rewrite Nat.add_0_r; reflexivity ].
rewrite Nat.add_0_r.
rewrite list_derivial_compose_deg_1.
rewrite apply_list_compose; simpl.
rewrite fld_mul_0_r, fld_add_0_l; reflexivity.
bbb.

Theorem taylor_formula_sub : ∀ α (f : field α) x P a,
  (apply_poly f P x .= f
   apply_poly f (taylor_poly f P a) (x .- f a))%K.
Proof.
intros α f x P a.
remember (poly_compose f P POL [a; .1 f%K … []]%pol) as Q eqn:HQ .
pose proof (taylor_formula_0 f (x .- f a)%K Q) as H.
subst Q.
unfold poly_compose in H; simpl in H.
unfold apply_poly in H; simpl in H.
unfold apply_poly in H; simpl in H.
unfold apply_poly; simpl.
rewrite apply_list_compose_add_sub in H.
bbb.
rewrite fld_mul_0_l in H.

intros α f x P a.
remember (poly_compose f P POL [a; .1 f%K … []]%pol) as Q eqn:HQ .
assert
 (∀ k,
  poly_derivial f k Q .= f
  poly_compose f (poly_derivial f k P) POL [a; .1 f%K … []])%pol 
 as H.
 intros k.
 subst Q.
 unfold poly_derivial; simpl.
 unfold poly_compose; simpl.
 unfold eq_poly; simpl.
 remember (al P) as la.
 clear.
 revert a k.
 induction la as [| a₁]; intros.
  simpl.
bbb.

Lemma taylor_formula_loop : ∀ α (f : field α) la x cnt n c,
  length la = (cnt + n)%nat
  → (apply_list f (List.skipn n la) (x .+ f c) .= f
     apply_list f (coeff_taylor_list f cnt la c n) x)%K.
Proof.
intros α f la x cnt n c Hlen.
revert la x n c Hlen.
induction cnt; intros.
 simpl in Hlen; subst n; simpl.
 rewrite list_skipn_overflow; reflexivity.

 simpl.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hlen.
 rewrite <- IHcnt; [ idtac | assumption ].
Abort. (*
bbb.
 clear; revert x c n.
 induction la as [| a]; intros.
  rewrite list_skipn_nil; simpl.
  rewrite fld_mul_0_l, fld_add_0_l.
  destruct n; reflexivity.

  destruct n; simpl.
   rewrite fld_add_0_l.
   rewrite fld_add_assoc.
   apply fld_add_compat_r.
   Focus 2.
   rewrite IHla.
   simpl.
   apply fld_add_compat_l.
   unfold list_derivial.
   simpl.
bbb.
*)

Theorem taylor_formula : ∀ α (f : field α) x c P,
  (apply_poly f P (x .+ f c) .= f
   apply_poly f (taylor_poly f P c) x)%K.
Proof.
intros α f x c P.
unfold apply_poly; simpl.
remember (al P) as la; clear Heqla.
unfold taylor_list.
clear.
revert x c.
induction la as [| a]; intros; [ reflexivity | simpl ].
rewrite IHla.
rewrite fld_add_0_l.
rewrite fld_add_assoc.
apply fld_add_compat_r.
rewrite fld_mul_add_distr_l.
apply fld_add_compat.
 clear.
 revert a x c.
 induction la as [| a₂]; intros; [ reflexivity | simpl ].
 rewrite fld_add_assoc.
 rewrite fld_add_assoc.
 rewrite fld_add_assoc.
 rewrite fld_add_assoc.
 apply fld_mul_compat_r.
 apply fld_add_compat_r.
 apply fld_add_compat_r.
bbb.
*)

(* test
Load Q_field.
Definition Qtest_taylor la c := taylor_list Q_field la c.
Eval vm_compute in Qtest_taylor [2#1; -3#1; 1#1 … []] 0.
Eval vm_compute in Qtest_taylor [2#1; -3#1; 1#1 … []] (2#1).
Eval vm_compute in Qtest_taylor [1; 1; 1; 1; 1; 1; 1 … []] 0.
Eval vm_compute in Qtest_taylor [1; 1; 1; 1; 1; 1; 1 … []] (2#1).
Definition Qtest_deriv n la := list_derivial Q_field n la.
Eval vm_compute in Qtest_deriv 0 [1; 1; 1; 1; 1; 1; 1 … []].
Eval vm_compute in Qtest_deriv 1 [1; 1; 1; 1; 1; 1; 1 … []].
Eval vm_compute in Qtest_deriv 2 [1; 1; 1; 1; 1; 1; 1 … []].
*)

(* *)

Fixpoint degree_plus_1_of_list α (is_zero : α → bool) (l : list α) :=
  match l with
  | [] => O
  | [x … l₁] =>
      match degree_plus_1_of_list is_zero l₁ with
      | O => if is_zero x then O else 1%nat
      | S n => S (S n)
      end
  end.

Definition degree α is_zero (pol : polynomial α) :=
  pred (degree_plus_1_of_list is_zero (al pol)).

Record algeb_closed_field α :=
  { ac_field : field α;
    ac_is_zero : α → bool;
    ac_root : polynomial α → α;
    ac_prop : ∀ pol, degree ac_is_zero pol ≥ 1
      → (apply_poly ac_field pol (ac_root pol) .= ac_field
         .0 ac_field)%K }.

Fixpoint poly_power α (f : field α) pol n :=
  match n with
  | O => .1 f%pol
  | S m => (pol .* f poly_power f pol m)%pol
  end.

Notation "a .^ f b" := (poly_power f a b) : poly_scope.

Fixpoint list_multiplicity α (acf : algeb_closed_field α) c₁ al d :=
  let f := ac_field acf in
  match d with
  | O => O
  | S d₁ =>
      match list_mod_div_mono f c₁ al with
      | [] => O
      | [m … ml] =>
          if ac_is_zero acf m then S (list_multiplicity acf c₁ ml d₁)
          else O
      end
  end.

Definition multiplicity α (acf : algeb_closed_field α) c₁ pol :=
  list_multiplicity acf c₁ (al pol) (List.length (al pol)).

Fixpoint quotient_phi_x_sub_c_pow_r α (f : field α) pol c₁ r :=
  match r with
  | O => pol
  | S r₁ => quotient_phi_x_sub_c_pow_r f (poly_div_mono f pol c₁) c₁ r₁
  end.

Section theorems.

Variable α : Type.
Variable acf : algeb_closed_field α.
Let f := ac_field acf.

(* P(x) = P(0) + x Q(x) *)
Lemma poly_eq_add_const_mul_x_poly : ∀ c cl,
  (POL [c … cl] .= f POL [c] .+ f POL [.0 f; .1 f … []]%K .* f POL cl)%pol.
Proof.
intros c cl.
unfold eq_poly; simpl.
rewrite summation_only_one.
rewrite fld_mul_0_l, fld_add_0_r.
constructor; [ reflexivity | idtac ].
destruct cl as [| c₁]; [ reflexivity | simpl ].
constructor.
 rewrite summation_only_one_non_0 with (v := 1%nat).
  rewrite fld_mul_1_l; reflexivity.

  split; [ apply Nat.le_0_l | reflexivity ].

  intros i (_, Hi) Hin1.
  destruct i; [ rewrite fld_mul_0_l; reflexivity | simpl ].
  destruct i; [ exfalso; apply Hin1; reflexivity | idtac ].
  destruct i; rewrite fld_mul_0_l; reflexivity.

 symmetry.
 apply poly_convol_mul_x_l; reflexivity.
Qed.

Lemma apply_poly_add : ∀ p₁ p₂ x,
  (apply_poly f (p₁ .+ f p₂)%pol x .= f
   apply_poly f p₁ x .+ f apply_poly f p₂ x)%K.
Proof.
intros p₁ p₂ x.
unfold apply_poly, horner; simpl.
remember (al p₁) as la eqn:Hla .
remember (al p₂) as lb eqn:Hlb .
clear.
revert x lb.
induction la as [| a]; intros; simpl.
 rewrite fld_add_0_l; reflexivity.

 destruct lb as [| b]; simpl; [ rewrite fld_add_0_r; reflexivity | idtac ].
 rewrite IHla.
 do 2 rewrite fld_add_assoc.
 apply fld_add_compat_r.
 rewrite fld_mul_add_distr_r.
 do 2 rewrite <- fld_add_assoc.
 apply fld_add_compat_l, fld_add_comm.
Qed.

Lemma list_fold_right_apply_compat : ∀ la lb x,
  list_eq f la lb
  → (List.fold_right (λ c accu, accu .* f x .+ f c) .0 f la .= f
     List.fold_right (λ c accu, accu .* f x .+ f c) .0 f lb)%K.
Proof.
intros la lb x Heq.
revert lb x Heq.
induction la as [| a]; intros; simpl.
 revert x.
 induction lb as [| b]; intros; [ reflexivity | simpl ].
 apply list_eq_nil_cons_inv in Heq.
 destruct Heq as (Hb, Hlb).
 rewrite Hb, fld_add_0_r.
 rewrite <- IHlb; [ idtac | assumption ].
 rewrite fld_mul_0_l; reflexivity.

 destruct lb as [| b].
  simpl.
  apply list_eq_cons_nil_inv in Heq.
  destruct Heq as (Ha, Hla).
  rewrite IHla; [ idtac | eassumption ].
  simpl.
  rewrite Ha, fld_mul_0_l, fld_add_0_r; reflexivity.

  apply list_eq_cons_inv in Heq.
  destruct Heq as (Hab, Hlab).
  simpl.
  rewrite Hab, IHla; [ reflexivity | eassumption ].
Qed.

(*
  Hlen : pred (length la + length lb) = len
  ============================
   (apply_list la x .* f apply_list lb x .= f
    apply_list (poly_convol_mul f la lb 0 len) x)%K

  Hlen : pred (length la + length lb) = S len
  ============================
   (apply_list la x .* f apply_list lb x .= f
    apply_list (poly_convol_mul f la lb 1 len) x .* f x .+ f
    List.nth 0 la .0 f .* f List.nth 0 lb .0 f)%K

  Hlen : pred (length la + length lb) = S (S len)
  ============================
   (apply_list la x .* f apply_list lb x .= f
    (apply_list (poly_convol_mul f la lb 2 len) x .* f x .+ f
     Σf (j = 0, 1)_ List.nth j la .0 f .* f List.nth (1 - j) lb .0 f) .* f x
    .+ f List.nth 0 la .0 f .* f List.nth 0 lb .0 f)%K

  Hlen : (length la + length lb)%nat = S len
  ============================
   ((apply_list f la x .* f x .+ f a) .* f (apply_list f lb x .* f x .+ f b)
    .= f
    (apply_list f (poly_convol_mul f [a … la] [b … lb] 2 len) x .* f x .+ f
     Σf (j = 0, 1)
     _ List.nth j [a … la] .0 f .* f List.nth (1 - j) [b … lb] .0 f) .* f x
    .+ f a .* f b)%K
*)

Lemma xxx : ∀ a b la lb x len,
  S (length la + length lb) = len
  → (apply_list f [a … la] x .* f apply_list f [b … lb] x .= f
     apply_list f (poly_convol_mul f [a … la] [b … lb] 0 len) x)%K.
Proof.
intros a b la lb x len Hlen; simpl.
destruct len; [ discriminate Hlen | simpl ].
rewrite summation_only_one.
apply Nat.succ_inj in Hlen.
rewrite fld_mul_add_distr_r.
do 2 rewrite fld_mul_add_distr_l.
rewrite fld_add_assoc.
apply fld_add_compat_r.
rewrite fld_mul_assoc.
rewrite fld_mul_assoc.
assert
 (apply_list f la x .* f x .* f b .= f apply_list f la x .* f b .* f x)%K
 as H.
 apply fld_mul_shuffle0.

 rewrite H; clear H.
 do 2 rewrite <- fld_mul_add_distr_r.
 apply fld_mul_compat_r.
 destruct len; simpl.
  Focus 2.
  unfold summation; simpl.
  rewrite fld_add_0_r.
  rename a into a₀.
  rename b into b₀.
  destruct la as [| a₁].
   simpl.
   Focus 2.
   destruct lb as [| b₁].
    simpl.
    Focus 2.
    simpl.
    rewrite fld_add_assoc.
    do 3 rewrite fld_mul_add_distr_r.
    rewrite fld_add_assoc, fld_add_comm, fld_add_assoc.
    apply fld_add_compat_r.
    rewrite fld_mul_add_distr_l.
    rewrite <- fld_add_assoc, fld_add_comm.
    do 2 rewrite <- fld_add_assoc.
    rewrite fld_add_comm.
    apply fld_add_compat_r.
    rewrite fld_mul_assoc.
    rewrite fld_add_assoc.
    rewrite fld_mul_add_distr_l.
    rewrite fld_mul_add_distr_l.
    rewrite fld_mul_assoc.
    rewrite fld_mul_assoc.
    rewrite fld_add_assoc.
    assert
     (apply_list f la x .* f x .* f b₀ .= f apply_list f la x .* f b₀ .* f x)%K
     as H by apply fld_mul_shuffle0.
    rewrite H; clear H.
    assert (a₁ .* f x .* f b₁ .= f a₁ .* f b₁ .* f x)%K
     as H by apply fld_mul_shuffle0.
    rewrite H; clear H.
    assert
     (apply_list f la x .* f x .* f x .* f b₁ .= f
      apply_list f la x .* f x .* f b₁ .* f x)%K as H
     by apply fld_mul_shuffle0.
    rewrite H; clear H.
    do 5 rewrite <- fld_mul_add_distr_r.
    apply fld_mul_compat_r.
    simpl in Hlen.
    rewrite Nat.add_succ_r in Hlen.
    apply Nat.succ_inj in Hlen.
bbb.

Lemma yyy : ∀ la lb x len,
  pred (length la + length lb) = len
  → (apply_list f la x .* f apply_list f lb x .= f
     apply_list f (poly_convol_mul f la lb 0 len) x)%K.
Proof.
intros la lb x len Hlen.
destruct la as [| a].
 rewrite fld_mul_0_l.
 rewrite poly_convol_mul_nil_l; reflexivity.

 destruct lb as [| b].
  rewrite fld_mul_0_r.
  rewrite poly_convol_mul_nil_r; reflexivity.

  simpl in Hlen.
  rewrite Nat.add_succ_r in Hlen.
bbb.

intros la lb x len Hlen.
destruct len.
 simpl.
 destruct la as [| a]; simpl.
  rewrite fld_mul_0_l; reflexivity.

  destruct lb as [| b]; simpl.
   rewrite fld_mul_0_r; reflexivity.

   simpl in Hlen.
   rewrite Nat.add_succ_r in Hlen; discriminate Hlen.

 simpl.
 destruct len.
  rewrite summation_only_one.
  simpl.
  rewrite fld_mul_0_l, fld_add_0_l.
  destruct la as [| a]; simpl.
   do 2 rewrite fld_mul_0_l; reflexivity.

   simpl in Hlen.
   rewrite Nat.add_comm in Hlen.
   destruct lb as [| b]; simpl.
    do 2 rewrite fld_mul_0_r; reflexivity.

    simpl in Hlen.
    apply Nat.succ_inj in Hlen.
    destruct lb; [ idtac | discriminate Hlen ].
    simpl in Hlen.
    destruct la; [ idtac | discriminate Hlen ].
    simpl.
    rewrite fld_mul_0_l, fld_add_0_l, fld_add_0_l; reflexivity.

  rewrite summation_only_one.
  remember 1%nat as z; simpl; subst z.
  destruct la as [| a].
   remember 1%nat as z; simpl; subst z.
   do 2 rewrite fld_mul_0_l.
   rewrite all_0_summation_0.
    do 2 rewrite fld_add_0_r.
    rewrite poly_convol_mul_nil_l; simpl.
    do 2 rewrite fld_mul_0_l; reflexivity.

    intros i (_, Hi).
    destruct i; rewrite fld_mul_0_l; reflexivity.

   remember 1%nat as z; remember [a … la] as ala.
   rewrite Heqala in |- * at 3.
   simpl; subst z ala.
   simpl in Hlen.
   destruct lb as [| b].
    simpl.
    do 2 rewrite fld_mul_0_r.
    rewrite poly_convol_mul_nil_r, fld_mul_0_l, fld_add_0_l.
    rewrite all_0_summation_0.
     rewrite fld_mul_0_l, fld_add_0_l; reflexivity.

     intros i (_, Hi).
     destruct i; rewrite fld_mul_0_r; reflexivity.

    rewrite Nat.add_comm in Hlen; simpl in Hlen.
    apply Nat.succ_inj in Hlen.
    rewrite Nat.add_comm in Hlen.
    remember [a … la] as ala.
    remember [b … lb] as alb.
    remember 1%nat as z.
    rewrite Heqala in |- * at 1.
    rewrite Heqala in |- * at 1.
    rewrite Heqalb in |- * at 1.
    rewrite Heqalb in |- * at 2.
    simpl; subst z ala alb.
Abort. (*
bbb.
*)

Lemma apply_poly_mul : ∀ p₁ p₂ x,
  (apply_poly f (p₁ .* f p₂)%pol x .= f
   apply_poly f p₁ x .* f apply_poly f p₂ x)%K.
Proof.
intros p₁ p₂ x.
symmetry.
unfold apply_poly, apply_list; simpl.
remember (al p₁) as la eqn:Hla .
remember (al p₂) as lb eqn:Hlb .
clear.
do 3 rewrite fold_apply_list.
remember (pred (length la + length lb)) as n eqn:Hn .
symmetry in Hn.
bbb.

intros p₁ p₂ x.
unfold apply_poly, apply_list; simpl.
remember (al p₁) as la eqn:Hla .
remember (al p₂) as lb eqn:Hlb .
clear.
do 3 rewrite fold_apply_list.
remember (pred (length la + length lb)) as n eqn:Hn .
symmetry in Hn.
destruct n; simpl.
 destruct la as [| a]; simpl.
  rewrite fld_mul_0_l; reflexivity.

  destruct lb as [| b]; simpl.
   rewrite fld_mul_0_r; reflexivity.

   simpl in Hn.
   rewrite Nat.add_succ_r in Hn; discriminate Hn.

 rewrite summation_only_one; simpl.
bbb.

remember (List.fold_right (λ c accu : α, accu .* f x .+ f c) .0 f)%K as g.
revert lb.
induction la as [| a]; intros; simpl.
 subst g.
 rewrite fld_mul_0_l.
 rewrite list_fold_right_apply_compat with (lb := []).
  reflexivity.

  apply poly_convol_mul_nil_l.

 induction lb as [| b].
  simpl.
  subst g.
  rewrite list_fold_right_apply_compat with (lb := []).
   simpl.
   rewrite fld_mul_0_r; reflexivity.

   apply poly_convol_mul_nil_r.

  simpl.
bbb.

(* p(c) = 0 ⇒ p = (x-c) * (p / (x-c)) *)
Lemma zzz : ∀ c p,
  (apply_poly f p c .= f .0 f)%K
  → (p .= f POL [(.-f c)%K; .1 f%K … []] .* f poly_div_mono f p c)%pol.
Proof.
intros c p Hz.
unfold poly_div_mono.
destruct p as (cl); simpl.
unfold eq_poly; simpl.
rewrite summation_only_one.
destruct cl as [| c₁]; simpl.
 rewrite fld_mul_0_r.
 constructor; reflexivity.

 constructor.
  rename c into x.
  rename c₁ into c.
  rename x into c₁.
  pose proof (poly_eq_add_const_mul_x_poly c cl) as Hc.
  rewrite Hc in Hz; simpl in Hz.
  rewrite apply_poly_add in Hz.
bbb.

(* [Walker, p. 100] « If c₁ ≠ 0 is an r-fold root, r ≥ 1, of Φ(z^q) = 0,
   we have:
      Φ(z^q) = (z - c₁)^r Ψ(z), [...] » *)
Theorem phi_zq_eq_z_sub_c₁_psy : ∀ pol ns c₁ r Ψ,
  ns ∈ newton_segments f pol
  → c₁ = ac_root acf (Φq f pol ns)
    → r = multiplicity acf c₁ (Φq f pol ns)
      → Ψ = quotient_phi_x_sub_c_pow_r f (Φq f pol ns) c₁ r
        → (Φq f pol ns .= f POL [(.- f c₁)%K; .1 f%K … []] .^ f r .* f Ψ)%pol.
Proof.
intros pol ns c₁ r Ψ Hns Hc₁ Hr HΨ.
symmetry in Hc₁, Hr.
destruct r.
 simpl.
 rewrite poly_mul_1_l.
 subst Ψ; reflexivity.

 simpl.
 destruct r; simpl.
  rewrite poly_mul_1_r.
  subst Ψ; simpl.
  unfold Φq; simpl.
  unfold poly_left_shift; simpl.
  unfold poly_div_mono; simpl.
  rewrite skipn_pad.
  rewrite Nat.sub_diag; simpl.
  remember (ini_pt ns) as jj eqn:Hj .
  destruct jj as (jq, αj); simpl.
  remember Hns as H; clear HeqH.
  apply exists_ini_pt_nat in H.
  destruct H as (j, (x, Hx)).
  rewrite <- Hj in Hx; injection Hx; clear Hx; intros; subst jq x.
  unfold nofq, Qnat; simpl; rewrite Nat2Z.id.
  symmetry in Hj.
  apply zzz.
bbb.

End theorems.
