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

Fixpoint list_mod_div_deg_1 α (f : field α) la c :=
  match la with
  | [] => []
  | [a₁ … la₁] => [apply_list f la c … list_mod_div_deg_1 f la₁ c]
  end.

Definition list_div_deg_1 α (f : field α) la c :=
  match list_mod_div_deg_1 f la c with
  | [] => []
  | [m … ml] => ml
  end.

Definition list_mod_deg_1 α (f : field α) la c :=
  match list_mod_div_deg_1 f la c with
  | [] => .0 f%K
  | [m … ml] => m
  end.

Definition poly_div_deg_1 α (f : field α) pol c :=
  (POL (list_div_deg_1 f (al pol) c))%pol.

(* test
Load Q_field.
Definition Qtest_div cl c := poly_div_deg_1 Q_field (POL cl)%pol c.
Definition Qtest_mod cl c := poly_mod_deg_1 Q_field (POL cl)%pol c.
Eval vm_compute in Qtest_div [2#1; -3#1; 1#1 … []] (4#1).
Eval vm_compute in Qtest_mod [2#1; -3#1; 1#1 … []] (4#1).
Eval vm_compute in Qtest_div [-Qnat 5; -Qnat 13; Qnat 0; Qnat 4 … []] (- 1 # 2).
Eval vm_compute in Qtest_mod [-Qnat 5; -Qnat 13; Qnat 0; Qnat 4 … []] (- 1 # 2).
*)

Fixpoint comb n k :=
  match k with
  | 0%nat => 1%nat
  | S k₁ =>
      match n with
      | 0%nat => 0%nat
      | S n₁ => (comb n₁ k₁ + comb n₁ k)%nat
      end
  end.

Fixpoint fld_mul_nat α (f : field α) n x :=
  match n with
  | O => .0 f%K
  | S n₁ => (fld_mul_nat f n₁ x .+ f x)%K
  end.

Fixpoint fld_pow_nat α (f : field α) a n :=
  match n with
  | 0%nat => .1 f%K
  | S n₁ => (a .* f fld_pow_nat f a n₁)%K
  end.

Fixpoint coeff_list_deriv α (f : field α) la n i :=
  match la with
  | [] => []
  | [a₁ … la₁] =>
      [fld_mul_nat f (comb i n) a₁ … coeff_list_deriv f la₁ n (S i)]
  end.

(* n-th derivial = n-th derivative divided by factorial n *)

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

Lemma fld_mul_nat_1_l : ∀ α (f : field α) a, (fld_mul_nat f 1 a .= f a)%K.
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
  rewrite Nat.add_0_r, fld_mul_nat_1_l.
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

Lemma taylor_list_formula_0 : ∀ α (f : field α) x la,
  (apply_list f la x .= f
   apply_list f (taylor_list f la .0 f) x)%K.
Proof.
intros α f x la.
unfold taylor_list.
rewrite <- taylor_formula_0_loop.
 rewrite list_skipn_0; reflexivity.

 rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem taylor_formula_0 : ∀ α (f : field α) x P,
  (apply_poly f P x .= f
   apply_poly f (taylor_poly f P .0 f) x)%K.
Proof.
intros α f x P.
apply taylor_list_formula_0.
Qed.

Lemma fld_mul_nat_add_distr_l : ∀ α (f : field α) a b n,
  (fld_mul_nat f n (a .+ f b) .= f fld_mul_nat f n a .+ f fld_mul_nat f n b)%K.
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

Lemma fld_mul_nat_add_distr_r : ∀ α (f : field α) a m n,
  (fld_mul_nat f (m + n) a .= f fld_mul_nat f m a .+ f fld_mul_nat f n a)%K.
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
constructor; [ apply fld_mul_nat_add_distr_l | apply IHla ].
Qed.

Lemma length_deriv_list : ∀ α (f : field α) la n i,
  length (coeff_list_deriv f la n i) = length la.
Proof.
intros α f la n i.
revert i.
induction la as [| a]; intros; [ reflexivity | simpl ].
apply eq_S, IHla.
Qed.

Lemma list_length_skipn : ∀ α k (la : list α),
  length (List.skipn k la) = (length la - k)%nat.
Proof.
intros α k la.
revert la.
induction k; intros; [ rewrite Nat.sub_0_r; reflexivity | simpl ].
destruct la as [| a]; [ reflexivity | apply IHk ].
Qed.

Lemma list_length_derivial : ∀ α (f : field α) la k,
  length (list_derivial f k la) = (length la - k)%nat.
Proof.
intros α f la k.
unfold list_derivial.
rewrite length_deriv_list.
apply list_length_skipn.
Qed.

Lemma comb_0_r : ∀ i, comb i 0 = 1%nat.
Proof. intros i; destruct i; reflexivity. Qed.

Lemma fld_mul_nat_0_r : ∀ α (f : field α) n, (fld_mul_nat f n .0 f .= f .0 f)%K.
Proof.
intros α f n.
induction n; [ reflexivity | simpl ].
rewrite fld_add_0_r; assumption.
Qed.

Add Parametric Morphism α (f : field α) : (fld_mul_nat f)
  with signature eq ==> fld_eq f ==> fld_eq f
  as fld_mul_nat_morph.
Proof.
intros n a b Hab.
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
 constructor; [ rewrite Hb; apply fld_mul_nat_0_r | idtac ].
 apply IHlb; assumption.

 destruct lb as [| b].
  simpl.
  apply list_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Ha, Hla).
  constructor; [ rewrite Ha; apply fld_mul_nat_0_r | idtac ].
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

Lemma coeff_list_deriv_0_l : ∀ α (f : field α) la i,
  list_eq f (coeff_list_deriv f la 0 i) la.
Proof.
intros α f la i; revert i.
induction la as [| a]; intros; [ reflexivity | simpl ].
rewrite comb_0_r, fld_mul_nat_1_l.
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

Definition list_nth_def_0 α (f : field α) n l := List.nth n l .0 f%K.

Lemma fold_list_nth_def_0 : ∀ α (f : field α) n l,
  List.nth n l .0 f%K = list_nth_def_0 f n l.
Proof. reflexivity. Qed.

Add Parametric Morphism α (f : field α) : (list_nth_def_0 f)
  with signature eq ==> list_eq f ==> fld_eq f
  as list_nth_fld_morph.
Proof.
intros n la lb Hab.
unfold list_nth_def_0.
revert n lb Hab.
induction la as [| a]; intros; simpl.
 rewrite match_id.
 symmetry.
 revert n.
 induction lb as [| b]; intros; [ destruct n; reflexivity | idtac ].
 apply list_eq_nil_cons_inv in Hab.
 destruct Hab as (Hb, Hlb).
 destruct n; [ assumption | simpl ].
 apply IHlb; assumption.

 destruct n; simpl.
  destruct lb as [| b]; simpl.
   apply list_eq_cons_nil_inv in Hab.
   destruct Hab; assumption.

   apply list_eq_cons_inv in Hab.
   destruct Hab; assumption.

  destruct lb as [| b]; simpl.
   apply list_eq_cons_nil_inv in Hab.
   destruct Hab as (_, Hla).
   clear a IHla.
   revert n.
   induction la as [| a]; intros.
    destruct n; reflexivity.

    destruct n; simpl.
     apply list_eq_cons_nil_inv in Hla.
     destruct Hla; assumption.

     apply list_eq_cons_nil_inv in Hla.
     apply IHla; destruct Hla; assumption.

   apply list_eq_cons_inv in Hab.
   destruct Hab as (_, Hab).
   apply IHla; assumption.
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

Add Parametric Morphism α (f : field α) : (list_mod_div_deg_1 f)
  with signature list_eq f ==> fld_eq f ==> list_eq f
  as list_mod_div_deg_1_morph.
Proof.
intros la lb Hlab ca cb Hcab.
revert lb ca cb Hlab Hcab.
induction la as [| a]; intros; simpl.
 induction lb as [| b]; [ reflexivity | simpl ].
 apply list_eq_nil_cons_inv in Hlab.
 destruct Hlab as (Hb, Hlb).
 constructor; [ idtac | apply IHlb; assumption ].
 rewrite Hb, fld_add_0_r.
 rewrite <- Hlb; simpl.
 rewrite fld_mul_0_l; reflexivity.

 destruct lb as [| b]; simpl.
  apply list_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Ha, Hla).
  constructor.
   rewrite Ha, Hla; simpl.
   rewrite fld_mul_0_l, fld_add_0_l; reflexivity.

   rewrite IHla; try eassumption; reflexivity.

  apply list_eq_cons_inv in Hlab.
  destruct Hlab as (Hab, Hlab).
  constructor; [ idtac | apply IHla; assumption ].
  rewrite Hab, Hlab, Hcab; reflexivity.
Qed.

Add Parametric Morphism α (f : field α) : (list_div_deg_1 f)
  with signature list_eq f ==> fld_eq f ==> list_eq f
  as list_div_deg_1_morph.
Proof.
intros la lb Hlab ca cb Hcab.
revert lb ca cb Hlab Hcab.
induction la as [| a]; intros; simpl.
 induction lb as [| b]; [ reflexivity | simpl ].
 apply list_eq_nil_cons_inv in Hlab.
 destruct Hlab as (Hb, Hlb).
 unfold list_div_deg_1; simpl.
 unfold list_div_deg_1 in IHlb; simpl in IHlb.
 rewrite <- Hlb; reflexivity.

 destruct lb as [| b]; simpl.
  apply list_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Ha, Hla).
  unfold list_div_deg_1; simpl.
  rewrite Hla; reflexivity.

  apply list_eq_cons_inv in Hlab.
  destruct Hlab as (Hab, Hlab).
  unfold list_div_deg_1; simpl.
  rewrite Hlab, Hcab; reflexivity.
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

Lemma fld_mul_nat_assoc : ∀ α (f : field α) a m n,
  (fld_mul_nat f m (fld_mul_nat f n a) .= f fld_mul_nat f (m * n) a)%K.
Proof.
intros α f a m n.
revert a n.
induction m; intros; [ reflexivity | simpl ].
rewrite IHm; symmetry.
rewrite Nat.mul_comm; simpl.
rewrite fld_mul_nat_add_distr_r.
rewrite fld_add_comm, Nat.mul_comm; reflexivity.
Qed.

Lemma fld_mul_nat_compat : ∀ α (f : field α) a b m n,
  (a .= f b)%K
  → (m = n)%nat
    → (fld_mul_nat f m a .= f fld_mul_nat f n a)%K.
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
    (List.map (λ x, fld_mul_nat f (S n) x)
       (coeff_list_deriv f la (S n) (S n + i)))
    (coeff_list_deriv f (coeff_list_deriv f la 1 (S n + i)) n (n + i)).
Proof.
intros α f la n i.
revert n i.
induction la as [| a]; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
constructor; [ clear | do 2 rewrite <- Nat.add_succ_r; apply IHla ].
rewrite Nat.add_succ_l, comb_1_r.
do 2 rewrite fld_mul_nat_assoc.
eapply fld_mul_nat_compat; [ reflexivity | idtac ].
rewrite Nat.mul_comm.
rewrite comb_succ_succ_mul; [ reflexivity | apply Nat.le_add_r ].
Qed.

Lemma map_coeff_list_deriv : ∀ α (f : field α) la n,
  list_eq f
    (List.map (λ x, fld_mul_nat f (S n) x) (coeff_list_deriv f la (S n) (S n)))
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
  list_eq f (List.map (λ a, fld_mul_nat f (S k) a) (list_derivial f (S k) la))
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

Lemma list_derivial_const : ∀ α (f : field α) k a,
  list_eq f (list_derivial f (S k) [a]) [].
Proof.
intros α f k a.
unfold list_derivial; simpl.
rewrite list_skipn_nil; reflexivity.
Qed.

Lemma list_mul_const_l : ∀ α (f : field α) a lb,
  list_eq f (list_mul f [a] lb) (List.map (fld_mul f a) lb).
Proof.
intros α f a lb.
unfold list_mul; simpl.
induction lb as [| b]; [ reflexivity | simpl ].
rewrite summation_only_one.
constructor; [ reflexivity | idtac ].
rewrite list_convol_mul_cons_succ; assumption.
Qed.

Lemma list_nth_coeff_list_deriv : ∀ α (f : field α) P i k n,
  (List.nth i (coeff_list_deriv f P n k) .0 f .= f
   fld_mul_nat f (comb (k + i) n) (List.nth i P .0 f))%K.
Proof.
intros α f P i k n.
revert i k n.
induction P as [| a]; intros; simpl.
 destruct i; rewrite fld_mul_nat_0_r; reflexivity.

 destruct i; simpl; [ rewrite Nat.add_0_r; reflexivity | idtac ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l; apply IHP.
Qed.

Lemma list_nth_derivial : ∀ α (f : field α) P i k,
  (List.nth i (list_derivial f k P) .0 f .= f
   fld_mul_nat f (comb (k + i) k) (List.nth (k + i) P .0 f))%K.
Proof.
intros α f P i k.
unfold list_derivial.
rewrite list_nth_coeff_list_deriv.
rewrite list_nth_skipn, Nat.add_comm; reflexivity.
Qed.

Fixpoint list_pow α (f : field α) P n :=
  match n with
  | 0%nat => [.1 f%K]
  | S n₁ => list_mul f P (list_pow f P n₁)
  end.

Definition list_compose2 α (f : field α) la lb :=
  List.fold_right
    (λ i accu,
     list_add f accu (list_mul f [List.nth i la .0 f] (list_pow f lb i)))%K
    [] (List.seq 0 (length la)).

Lemma list_compose_cons_l : ∀ α (f : field α) a la lb,
  list_eq f (list_compose f [a … la] lb)
    (list_add f [a] (list_mul f lb (list_compose f la lb))).
Proof.
intros α f a la lb.
rewrite list_add_comm, list_mul_comm; reflexivity.
Qed.

Lemma list_seq_bef_start_not_in : ∀ i s len,
  (i < s)%nat
  → i ∉ List.seq s len.
Proof.
intros i s len His H.
revert s His H.
induction len; intros; [ assumption | simpl ].
simpl in H.
destruct H as [H| H].
 subst s; revert His; apply Nat.lt_irrefl.

 eapply IHlen; [ idtac | eassumption ].
 apply Nat.lt_lt_succ_r; assumption.
Qed.

Lemma list_fold_right_some_compat : ∀ α (f : field α) β g l,
  (∀ x y z, list_eq f y z → list_eq f (g x y) (g x z))
  → (∀ (i : β), i ∈ l → list_eq f (g i []) [])
    → list_eq f (List.fold_right g [] l) [].
Proof.
intros α f β g l Hg Hil.
induction l as [| x]; [ reflexivity | simpl ].
rewrite <- Hil in |- * at 2; [ idtac | left; reflexivity ].
apply Hg, IHl.
intros i Hi.
apply Hil; right; assumption.
Qed.

Lemma list_compose2_cons_nil : ∀ α (f : field α) a la,
  list_eq f (list_compose2 f [a … la] []) [a].
Proof.
intros α f a la.
unfold list_compose2; simpl.
unfold list_mul at 2; simpl.
rewrite summation_only_one, fld_mul_1_r.
rewrite list_fold_right_some_compat.
 rewrite list_add_nil_l; reflexivity.

 intros x y z Hyz.
 rewrite Hyz; reflexivity.

 intros i Hi.
 destruct i.
  exfalso; revert Hi.
  apply list_seq_bef_start_not_in; apply Nat.lt_0_1.

  simpl.
  rewrite list_mul_nil_l, list_mul_nil_r; reflexivity.
Qed.

Lemma list_mul_fold_add_distr : ∀ α (f : field α) la li (g : nat → list α) x,
  list_eq f
    (list_mul f x (List.fold_right (λ i accu, list_add f accu (g i)) la li))
    (List.fold_right (λ i accu, list_add f accu (list_mul f x (g i)))
       (list_mul f x la) li).
Proof.
intros α f la li g x.
revert la x.
induction li as [| j]; intros; [ reflexivity | simpl ].
rewrite list_mul_add_distr_l.
rewrite IHli; reflexivity.
Qed.

Lemma list_add_fold_assoc : ∀ α (f : field α) la li (g : nat → list α) x,
  list_eq f
    (list_add f x (List.fold_right (λ i accu, list_add f accu (g i)) la li))
    (List.fold_right (λ i accu, list_add f accu (g i))
       (list_add f x la) li).
Proof.
intros α f la li g x.
revert la x.
induction li as [| j]; intros; [ reflexivity | simpl ].
rewrite <- list_add_assoc.
rewrite IHli; reflexivity.
Qed.

Lemma list_fold_right_seq : ∀ α (f : field α) g h la lb s t len,
  list_eq f la lb
  → (∀ x y z, list_eq f y z → list_eq f (g x y) (g x z))
    → (∀ i accu, list_eq f (g (s + i)%nat accu) (h (t + i)%nat accu))
      → list_eq f
          (List.fold_right g la (List.seq s len))
          (List.fold_right h lb (List.seq t len)).
Proof.
intros α f g h la lb s t len Hab Hg Hgh.
revert g h la lb s t Hab Hg Hgh.
induction len; intros; [ assumption | simpl ].
pose proof (Hgh O (List.fold_right h lb (List.seq (S t) len))) as H.
do 2 rewrite Nat.add_0_r in H.
rewrite <- H.
apply Hg.
apply IHlen; [ assumption | assumption | idtac ].
intros i accu.
do 2 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
apply Hgh.
Qed.

Lemma list_compose_compose2 : ∀ α (f : field α) la lb,
  list_eq f (list_compose f la lb) (list_compose2 f la lb).
Proof.
intros α f la lb.
revert lb.
induction la as [| a]; intros; [ reflexivity | simpl ].
rewrite IHla.
symmetry; clear.
unfold list_compose2.
rewrite list_mul_comm.
rewrite list_mul_fold_add_distr.
rewrite list_add_comm.
remember [a] as aa; simpl; subst aa.
rewrite list_add_comm.
apply list_add_compat; [ apply list_mul_1_r | idtac ].
apply list_fold_right_seq.
 rewrite list_mul_nil_r; reflexivity.

 intros x y z Hyz.
 rewrite Hyz; reflexivity.

 intros i accu; simpl.
 apply list_add_compat; [ reflexivity | simpl ].
 rewrite list_mul_comm, <- list_mul_assoc.
 apply list_mul_compat; [ reflexivity | idtac ].
 apply list_mul_comm.
Qed.

Lemma length_derivial_nil : ∀ α (f : field α) k,
  length (list_derivial f k []) = O.
Proof.
intros α f k.
destruct k; reflexivity.
Qed.

Lemma fold_nth_succ : ∀ α n a l (d : α),
  match n with
  | 0%nat => a
  | S n₁ => List.nth n₁ l d
  end = List.nth n [a … l] d.
Proof. intros; destruct n; reflexivity. Qed.

Lemma fold_seq_succ : ∀ α (f : field α) g s len,
  (∀ t a b, list_eq f a b → list_eq f (g t a) (g t b))
  → list_eq f
      (List.fold_right g [] (List.seq s (S len)))
      (g s (List.fold_right (λ i accu, g (S i) accu) [] (List.seq s len)))%K.
Proof.
intros α f g s len Hg.
revert s Hg.
induction len; intros; [ reflexivity | idtac ].
remember (S len) as x; simpl; subst x.
apply Hg.
rewrite IHlen; [ reflexivity | apply Hg ].
Qed.

Lemma fold_add_pow : ∀ α (f : field α) a la lb lc da,
  list_eq f
    (List.fold_right
      (λ i accu,
       list_add f accu
         (list_mul f [List.nth (S i) [a … la] da]
            (list_pow f lb (S i))))
      [] lc)
    (list_mul f lb
       (List.fold_right
          (λ i accu,
           list_add f accu
             (list_mul f [List.nth i la da] (list_pow f lb i)))
          [] lc)).
Proof.
intros α f a la lb lc da; simpl; clear.
revert la lb da.
induction lc as [| c]; intros; simpl.
 rewrite list_mul_nil_r; reflexivity.

 rewrite IHlc.
 rewrite list_mul_add_distr_l.
 apply list_add_compat; [ reflexivity | idtac ].
 rewrite list_mul_assoc.
 rewrite list_mul_assoc.
 apply list_mul_compat; [ idtac | reflexivity ].
 apply list_mul_comm.
Qed.

Lemma nth_mul_deg_1 : ∀ α (f : field α) a lb k,
  (List.nth (S k) (list_mul f [a; .1 f … []] lb) .0 f .= f
   a .* f List.nth (S k) lb .0 f .+ f List.nth k lb .0 f)%K.
Proof.
intros α f a lb k.
unfold list_mul.
rewrite list_nth_list_convol_mul; [ idtac | reflexivity ].
rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
rewrite summation_split_first; [ idtac | omega ].
simpl.
rewrite all_0_summation_0.
 rewrite fld_mul_1_l, Nat.sub_0_r, fld_add_0_r.
 reflexivity.

 intros i (Hi, Hik).
 destruct i; [ exfalso; omega | idtac ].
 destruct i; [ exfalso; omega | idtac ].
 rewrite match_id, fld_mul_0_l; reflexivity.
Qed.

Lemma fld_mul_nat_mul_swap : ∀ α (f : field α) n a b,
  (fld_mul_nat f n (a .* f b) .= f a .* f fld_mul_nat f n b)%K.
Proof.
intros α f n a b.
induction n; simpl.
 rewrite fld_mul_0_r; reflexivity.

 rewrite IHn, fld_mul_add_distr_l; reflexivity.
Qed.

Lemma list_nth_compose_deg_1 : ∀ α (f : field α) la b k n,
  n = length la
  → (List.nth k (list_compose2 f la [b; .1 f … []]) .0 f .= f
     Σ f (i = 0, n - k) _
     fld_mul_nat f (comb (k + i) k)
      (List.nth (k + i) la .0 f .* f fld_pow_nat f b i))%K.
Proof.
intros α f la b k n Hlen.
unfold list_compose2; subst n.
revert b k.
induction la as [| a]; intros.
 simpl.
 rewrite summation_only_one.
 do 2 rewrite match_id.
 rewrite fld_mul_0_l, fld_mul_nat_0_r; reflexivity.

 remember (length [a … la]) as x; simpl in Heqx; subst x.
 rewrite fold_list_nth_def_0.
 rewrite fold_seq_succ.
  unfold list_nth_def_0.
  rewrite list_nth_add.
  rewrite fold_list_nth_def_0.
  rewrite fold_add_pow.
  unfold list_nth_def_0.
  destruct k.
   simpl.
   do 2 rewrite summation_only_one.
   rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
   rewrite fld_mul_1_r, comb_id.
   rewrite fld_mul_nat_1_l.
   simpl.
   rewrite fld_mul_1_r.
   rewrite fld_add_comm.
   apply fld_add_compat_l.
   rewrite IHla.
   rewrite Nat.sub_0_r; simpl.
   rewrite summation_succ_succ.
   rewrite <- summation_mul_swap.
   apply summation_compat; intros i (_, Hi).
   do 2 rewrite comb_0_r, fld_mul_nat_1_l; simpl.
   do 2 rewrite fld_mul_assoc.
   apply fld_mul_compat_r, fld_mul_comm.

   rewrite nth_mul_deg_1.
   do 2 rewrite IHla; simpl.
   rewrite match_id, fld_add_0_r.
   rewrite <- summation_mul_swap.
   rewrite fld_add_comm.
   rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
   rewrite Nat.add_0_r, comb_id; simpl.
   rewrite fld_add_0_l, fld_mul_1_r; symmetry.
   rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
   rewrite Nat.add_0_r, comb_id, comb_lt; [ idtac | omega ].
   rewrite Nat.add_0_r; simpl.
   rewrite fld_add_0_l, fld_mul_1_r.
   rewrite <- fld_add_assoc.
   apply fld_add_compat_l.
   destruct (le_dec (length la) k) as [H₁| H₁].
    rewrite summation_lt; [ idtac | omega ].
    rewrite summation_lt; [ idtac | omega ].
    replace (length la - S k)%nat with O by omega.
    rewrite summation_only_one; simpl.
    rewrite Nat.add_0_r.
    rewrite comb_id, comb_lt; [ idtac | omega ].
    rewrite Nat.add_0_r; simpl.
    rewrite List.nth_overflow; [ idtac | omega ].
    do 2 rewrite fld_add_0_l; rewrite fld_mul_0_l, fld_mul_0_r.
    reflexivity.

    replace (length la - k)%nat with (S (length la - S k)) by omega.
    do 2 rewrite summation_succ_succ.
    rewrite <- summation_add_distr.
    apply summation_compat; intros i (_, Hi); simpl.
    rewrite <- Nat.add_succ_r.
    do 2 rewrite <- comb_succ_succ.
    remember (List.nth (k + S i) la .0 f)%K as n eqn:Hn .
    remember (fld_pow_nat f b i) as p eqn:Hp; simpl.
    rewrite fld_mul_nat_add_distr_r.
    apply fld_add_compat_l.
    rewrite Nat.add_succ_r; simpl.
    rewrite fld_mul_assoc, fld_mul_shuffle0, fld_mul_comm.
    rewrite fld_mul_nat_mul_swap; reflexivity.

  intros t lc ld Hcd.
  rewrite Hcd; reflexivity.
Qed.

Lemma summation_mul_nat_swap: ∀ α (f : field α) a g k,
  (Σ f (i = 0, k)_ fld_mul_nat f a (g i) .= f
   fld_mul_nat f a (Σ f (i = 0, k)_ g i))%K.
Proof.
intros α f a g k.
induction k.
 do 2 rewrite summation_only_one; reflexivity.

 rewrite summation_succ; [ idtac | apply Nat.le_0_l ].
 rewrite summation_succ; [ idtac | apply Nat.le_0_l ].
 rewrite IHk.
 rewrite fld_mul_nat_add_distr_l.
 reflexivity.
Qed.

Lemma comb_mul_add_add : ∀ i j k,
  (comb (k + i) k * comb (k + i + j) (k + i) =
   comb (i + j) i * comb (k + i + j) k)%nat.
Proof.
intros i j k.
pose proof (comb_fact k i) as H₁.
pose proof (comb_fact i j) as H₂.
pose proof (comb_fact (k + i) j) as H₃.
pose proof (comb_fact k (i + j)) as H₄.
rewrite Nat.add_assoc in H₄.
rewrite <- H₄ in H₃.
rewrite <- H₁, <- H₂ in H₃.
revert H₃; clear; intros H.
do 6 rewrite Nat.mul_assoc in H.
apply Nat.mul_cancel_r in H; [ idtac | apply fact_neq_0 ].
apply Nat.mul_cancel_r in H; [ idtac | apply fact_neq_0 ].
symmetry in H.
rewrite Nat.mul_shuffle0 in H.
apply Nat.mul_cancel_r in H; [ idtac | apply fact_neq_0 ].
rewrite Nat.mul_comm in H; rewrite H.
apply Nat.mul_comm.
Qed.

Lemma list_derivial_compose_deg_1 : ∀ α (f : field α) k la b,
  list_eq f (list_derivial f k (list_compose f la [b; .1 f%K … []]))
    (list_compose f (list_derivial f k la) [b; .1 f%K … []]).
Proof.
intros α f k la b.
do 2 rewrite list_compose_compose2.
apply list_nth_list_eq; intros j.
rewrite list_nth_derivial.
rewrite list_nth_compose_deg_1; [ idtac | reflexivity ].
rewrite list_nth_compose_deg_1; [ idtac | reflexivity ].
rewrite list_length_derivial.
rewrite <- Nat.sub_add_distr.
rewrite <- summation_mul_nat_swap.
apply summation_compat; intros i (_, Hi).
rewrite list_nth_derivial.
rewrite Nat.add_assoc.
rewrite fld_mul_comm.
rewrite fld_mul_nat_mul_swap.
symmetry; rewrite fld_mul_comm.
rewrite fld_mul_nat_mul_swap.
rewrite fld_mul_nat_mul_swap.
apply fld_mul_compat_l.
do 2 rewrite fld_mul_nat_assoc.
rewrite comb_mul_add_add.
reflexivity.
Qed.

Lemma taylor_list_compose_deg_1 : ∀ α (f : field α) a la,
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
Qed.

Lemma taylor_list_formula_sub : ∀ α (f : field α) x la a,
  (apply_list f la x .= f
   apply_list f (taylor_list f la a) (x .- f a))%K.
Proof.
intros α f x la a.
remember (list_compose f la [a; .1 f%K … []]) as lb eqn:Hlb .
pose proof (taylor_list_formula_0 f (x .- f a)%K lb) as H.
subst lb.
rewrite apply_list_compose_add_sub in H.
rewrite H.
rewrite taylor_list_compose_deg_1; reflexivity.
Qed.

Theorem taylor_formula_sub : ∀ α (f : field α) x P a,
  (apply_poly f P x .= f
   apply_poly f (taylor_poly f P a) (x .- f a))%K.
Proof.
intros α f x P a.
apply taylor_list_formula_sub.
Qed.

Theorem taylor_formula : ∀ α (f : field α) x c P,
  (apply_poly f P (x .+ f c) .= f
   apply_poly f (taylor_poly f P c) x)%K.
Proof.
intros α f x c P.
rewrite taylor_formula_sub.
rewrite fld_add_sub; reflexivity.
Qed.

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
    ac_prop_is_zero : ∀ a,
      ac_is_zero a = true ↔ (a .= ac_field .0 ac_field)%K;
    ac_prop_root : ∀ pol, degree ac_is_zero pol ≥ 1
      → (apply_poly ac_field pol (ac_root pol) .= ac_field
         .0 ac_field)%K }.

Fixpoint list_power α (f : field α) la n :=
  match n with
  | O => [.1 f%K]
  | S m => list_mul f la (list_power f la m)
  end.

Definition poly_power α (f : field α) pol n :=
  (POL (list_power f (al pol) n))%pol.

Notation "a .^ f b" := (poly_power f a b) : poly_scope.

Fixpoint list_root_multiplicity α (acf : algeb_closed_field α) c la d :=
  let f := ac_field acf in
  match d with
  | O => O
  | S d₁ =>
      if ac_is_zero acf (list_mod_deg_1 f la c) then
        S (list_root_multiplicity acf c (list_div_deg_1 f la c) d₁)
      else O
  end.

Definition root_multiplicity α (acf : algeb_closed_field α) c pol :=
  list_root_multiplicity acf c (al pol) (List.length (al pol)).

Fixpoint list_quotient_phi_x_sub_c_pow_r α (f : field α) la c₁ r :=
  match r with
  | O => la
  | S r₁ => list_quotient_phi_x_sub_c_pow_r f (list_div_deg_1 f la c₁) c₁ r₁
  end.

Definition quotient_phi_x_sub_c_pow_r α (f : field α) pol c₁ r :=
  (POL (list_quotient_phi_x_sub_c_pow_r f (al pol) c₁ r))%pol.

Definition list_root α (acf : algeb_closed_field α) la :=
  ac_root acf (POL la)%pol.

Section theorems.

Variable α : Type.
Variable acf : algeb_closed_field α.
Let f := ac_field acf.

Lemma list_prop_root : ∀ la,
  degree_plus_1_of_list (ac_is_zero acf) la ≥ 2
  → (apply_list f la (list_root acf la) .= f .0 f)%K.
Proof.
intros la Hdeg.
remember POL la%pol as pol eqn:Hpol .
assert (degree (ac_is_zero acf) pol ≥ 1) as H.
 subst pol; unfold degree; simpl.
 unfold ge in Hdeg; unfold ge.
 apply Nat.le_succ_le_pred; assumption.

 apply ac_prop_root in H.
 subst pol; assumption.
Qed.

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
 apply list_convol_mul_x_l; reflexivity.
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

Lemma apply_poly_mul : ∀ p₁ p₂ x,
  (apply_poly f (p₁ .* f p₂)%pol x .= f
   apply_poly f p₁ x .* f apply_poly f p₂ x)%K.
Proof.
intros p₁ p₂ x.
apply apply_list_mul.
Qed.

Lemma list_nth_mod_div_deg_1 : ∀ la c i,
  (List.nth i (list_mod_div_deg_1 f la c) .0 f .= f
   apply_list f (List.skipn i la) c)%K.
Proof.
intros la c i; revert i.
induction la as [| a]; intros; simpl.
 rewrite match_id, list_skipn_nil; reflexivity.

 destruct i; [ reflexivity | apply IHla ].
Qed.

Lemma root_formula : ∀ la c,
  (apply_list f la c .= f .0 f)%K
  → list_eq f la
       (list_mul f [(.-f c)%K; .1 f%K … []] (list_div_deg_1 f la c)).
Proof.
intros la c Hc.
unfold list_div_deg_1.
remember (list_mod_div_deg_1 f la c) as md eqn:Hmd .
symmetry in Hmd.
destruct md as [| r d].
 rewrite list_mul_nil_r.
 destruct la as [| a]; [ reflexivity | discriminate Hmd ].

 destruct la as [| a]; [ discriminate Hmd | simpl ].
 simpl in Hmd.
 simpl in Hc.
 injection Hmd; clear Hmd; intros Hd Hr.
 subst d; clear r Hr.
 rename a into a₀.
 apply list_nth_list_eq; intros i.
 destruct i.
  simpl.
  rewrite summation_only_one.
  destruct la as [| a₁].
   simpl.
   rewrite fld_mul_0_r.
   simpl in Hc.
   rewrite fld_mul_0_l, fld_add_0_l in Hc; assumption.

   simpl in Hc; simpl.
   remember (apply_list f la c .* f c .+ f a₁)%K as v eqn:Hv .
   rewrite fld_mul_comm in Hc.
   apply fld_add_compat_r with (c := (.-f c .* f v)%K) in Hc.
   rewrite fld_add_0_l in Hc.
   rewrite fld_add_comm, fld_add_assoc in Hc.
   rewrite fld_mul_opp_l in Hc.
   rewrite fld_add_opp_l in Hc.
   rewrite fld_add_0_l in Hc.
   rewrite fld_mul_opp_l.
   assumption.

  rewrite nth_mul_deg_1; simpl.
  clear a₀ Hc.
  do 2 rewrite list_nth_mod_div_deg_1.
  revert i.
  induction la as [| a]; intros; simpl.
   rewrite match_id, list_skipn_nil; simpl.
   rewrite fld_mul_0_r, fld_add_0_l; reflexivity.

   destruct i; [ simpl | apply IHla ].
   rewrite fld_add_assoc.
   rewrite fld_mul_opp_l, fld_mul_comm.
   rewrite fld_add_opp_l, fld_add_0_l; reflexivity.
Qed.

(* p(c) = 0 ⇒ p = (x-c) * (p / (x-c)) *)
Lemma poly_root_formula : ∀ c p,
  (apply_poly f p c .= f .0 f)%K
  → (p .= f POL [(.-f c)%K; .1 f%K … []] .* f poly_div_deg_1 f p c)%pol.
Proof.
intros c p Hz.
apply root_formula; assumption.
Qed.

Lemma list_root_mult_succ_if : ∀ la d c md n,
  list_root_multiplicity acf c la d = S n
  → list_mod_div_deg_1 f la c = md
    → d ≠ O ∧ ac_is_zero acf (list_mod_deg_1 f la c) = true ∧
      list_root_multiplicity acf c (list_div_deg_1 f la c) (pred d) = n.
Proof.
intros la d c md n Hn Hmd.
destruct d; [ discriminate Hn | simpl in Hn ].
split; [ intros H; discriminate H | idtac ].
fold f in Hn.
remember (ac_is_zero acf (list_mod_deg_1 f la c)) as z eqn:Hz .
symmetry in Hz.
destruct z; [ idtac | discriminate Hn ].
split; [ reflexivity | idtac ].
apply eq_add_S; assumption.
Qed.

Lemma list_fold_pol_list : ∀ A g P (l : list A) (c : α),
  (∀ lb lc, list_eq f lb lc → list_eq f (g f lb c) (g f lc c))
  → (List.fold_right (λ _ accu, POL (g f (al accu) c))%pol P l .= f
     POL (List.fold_right (λ _ accu, g f accu c) (al P) l))%pol.
Proof.
intros A g P l c Heq.
destruct P as (la); simpl.
revert la.
induction l as [| n]; intros; [ reflexivity | simpl ].
unfold eq_poly; simpl.
apply Heq.
rewrite IHl; reflexivity.
Qed.

Lemma list_length_shrink_le : ∀ k (l : list α),
  length (list_shrink k l) ≤ length l.
Proof.
intros k l.
unfold list_shrink.
assert (∀ cnt k₁, length (list_shrink_aux cnt k₁ l) ≤ length l) as H.
 intros cnt k₁.
 revert cnt.
 induction l as [| x]; intros; [ reflexivity | simpl ].
 destruct cnt; simpl.
  apply le_n_S, IHl.

  etransitivity; [ apply IHl | idtac ].
  apply Nat.le_succ_r; left; reflexivity.

 apply H.
Qed.

Lemma degree_plus_1_is_0 : ∀ la,
  degree_plus_1_of_list (ac_is_zero acf) la = 0%nat
  → list_eq f la [].
Proof.
intros la H.
induction la as [| a]; [ reflexivity | idtac ].
simpl in H.
remember (degree_plus_1_of_list (ac_is_zero acf) la) as d eqn:Hd .
symmetry in Hd.
destruct d; [ idtac | discriminate H ].
constructor; [ idtac | apply IHla; reflexivity ].
remember (ac_is_zero acf a) as iz eqn:Hiz .
symmetry in Hiz.
destruct iz; [ idtac | discriminate H].
apply ac_prop_is_zero in Hiz.
assumption.
Qed.

Lemma list_eq_nil_nth : ∀ la,
  list_eq f la []
  → ∀ n, (List.nth n la .0 f .= f .0 f)%K.
Proof.
intros la H n.
revert n.
induction la as [| a]; intros; simpl.
 rewrite match_id; reflexivity.

 apply list_eq_cons_nil_inv in H.
 destruct H as (Ha, Hla).
 destruct n; [ assumption | idtac ].
 apply IHla; assumption.
Qed.

Lemma all_0_shrink_0 : ∀ la cnt k,
  (∀ n, List.nth n la .0 f .= f .0 f)%K
  → (∀ n, List.nth n (list_shrink_aux cnt k la) .0 f .= f .0 f)%K.
Proof.
intros la cnt k H n.
revert cnt k n.
induction la as [| a]; intros; [ destruct n; reflexivity | simpl ].
destruct cnt; simpl.
 destruct n; simpl.
  pose proof (H O); assumption.

  apply IHla; clear n; intros n.
  pose proof (H (S n)); assumption.

 apply IHla; clear n; intros n.
 pose proof (H (S n)); assumption.
Qed.

Lemma cpol_degree_ge_1 : ∀ pol ns,
  ns ∈ newton_segments f pol
  → degree (ac_is_zero acf) (Φq f pol ns) ≥ 1.
Proof.
intros pol ns Hns.
remember (Pos.to_nat (q_of_ns f pol ns)) as q eqn:Hq .
remember (ini_pt ns) as jj eqn:Hj .
destruct jj as (jq, αj); simpl.
remember Hns as H; clear HeqH.
apply exists_ini_pt_nat in H.
destruct H as (j, (x, Hx)).
rewrite <- Hj in Hx; injection Hx; clear Hx; intros; subst jq x.
remember Hns as Hk; clear HeqHk.
apply exists_fin_pt_nat in Hk.
destruct Hk as (k, (αk, Hk)).
symmetry in Hk.
remember Hns as Hdeg; clear HeqHdeg.
eapply phi_degree_is_k_sub_j_div_q in Hdeg; try eassumption.
unfold has_degree in Hdeg.
destruct Hdeg as (Hdeg, Hcnz).
remember Hns as Hqkj; clear HeqHqkj.
eapply q_is_factor_of_h_minus_j with (h := k) in Hqkj; try eassumption.
 destruct Hqkj as (n, Hqkj).
 destruct n.
  simpl in Hqkj.
  exfalso.
  remember Hns as H; clear HeqH.
  apply j_lt_k with (j := j) (k := k) in H.
   fast_omega Hqkj H.

   rewrite <- Hj; simpl.
   unfold nofq, Qnat; simpl.
   rewrite Nat2Z.id; reflexivity.

   rewrite <- Hk; simpl.
   unfold nofq, Qnat; simpl.
   rewrite Nat2Z.id; reflexivity.

  rewrite Hqkj in Hdeg, Hcnz.
  rewrite Nat.div_mul in Hdeg; [ idtac | subst q; apply Pos2Nat_ne_0 ].
  rewrite Nat.div_mul in Hcnz; [ idtac | subst q; apply Pos2Nat_ne_0 ].
  unfold pseudo_degree in Hdeg.
  unfold degree.
  remember (al (Φ f pol ns)) as la eqn:Hla .
  simpl in Hla.
  rewrite Nat.sub_diag in Hla; simpl in Hla.
  rewrite skipn_pad in Hla.
  rewrite <- Hj in Hla; simpl in Hla.
  unfold nofq, Qnat in Hla; simpl in Hla.
  rewrite Nat2Z.id in Hla; simpl.
  rewrite Nat.sub_diag; simpl.
  rewrite skipn_pad.
  rewrite <- Hj; unfold fst.
  unfold nofq, Qnat.
  unfold Qnum.
  rewrite Nat2Z.id.
  remember (valuation_coeff f (List.nth j (al pol) .0 f%ps)) as v eqn:Hv .
  remember (oth_pts ns ++ [fin_pt ns]) as pts eqn:Hpts .
  remember (List.map (term_of_point f pol) pts) as tl eqn:Htl .
  subst la; simpl.
  remember (make_char_pol f (S j) tl) as cpol eqn:Hcpol .
  remember (degree_plus_1_of_list (ac_is_zero acf) cpol) as d eqn:Hd .
  symmetry in Hd.
  destruct d; [ exfalso | omega ].
  subst cpol.
  remember (Pos.to_nat (q_of_ns f pol ns)) as nq.
  remember (make_char_pol f (S j) tl) as cpol.
  pose proof (list_length_shrink_le nq [v … cpol]) as Hlen.
  remember [v … cpol] as vcpol.
  rewrite Heqvcpol in Hlen at 2.
  simpl in Hlen.
  subst vcpol.
  apply degree_plus_1_is_0 in Hd.
  simpl in Hcnz.
  simpl in Hdeg.
  simpl in Hlen.
  apply le_S_n in Hlen.
  apply Hcnz.
  apply all_0_shrink_0; intros m.
  apply list_eq_nil_nth; assumption.

 apply List.in_or_app; right; left; symmetry; eassumption.
Qed.

Lemma poly_power_1_r : ∀ P, (poly_power f P 1 .= f P)%pol.
Proof.
intros P.
unfold eq_poly; simpl.
rewrite list_mul_1_r; reflexivity.
Qed.

Lemma list_mod_deg_1_apply : ∀ la c,
  (list_mod_deg_1 f la c .= f .0 f)%K
  → (apply_list f la c .= f .0 f)%K.
Proof.
intros la c Hmod.
destruct la as [| a]; [ reflexivity | assumption ].
Qed.

Lemma list_root_mul_power_quotient : ∀ la c r len,
  list_root_multiplicity acf c la len = r
  → list_eq f la
       (list_mul f (list_power f [(.-f c)%K; .1 f%K … []] r)
       (list_quotient_phi_x_sub_c_pow_r f la c r)).
Proof.
intros la c r len Hmult.
revert la len Hmult.
induction r; intros; simpl.
 rewrite list_mul_1_l; reflexivity.

 rewrite <- list_mul_assoc.
 eapply list_root_mult_succ_if in Hmult; [ idtac | reflexivity ].
 destruct Hmult as (_, (Hz, Hmult)).
 rewrite <- IHr; [ idtac | eassumption ].
 apply root_formula.
 apply list_mod_deg_1_apply, ac_prop_is_zero.
 assumption.
Qed.

Lemma list_div_x_sub_c_ne_0 : ∀ la c r len,
  not (list_eq f la [])
  → list_root_multiplicity acf c la len = r
    → length la ≤ len
      → (apply_list f (list_quotient_phi_x_sub_c_pow_r f la c r) c .≠ f
         .0 f)%K.
Proof.
intros la c r len Hla Hmult Hlen.
revert la len Hla Hmult Hlen.
induction r; intros; simpl.
 intros Happ; apply Hla; clear Hla.
 revert la Hmult Hlen Happ.
 induction len; intros.
  destruct la; [ reflexivity | simpl in Hlen; exfalso; omega ].

  destruct la as [| a]; [ reflexivity | idtac ].
  simpl in Hmult.
  fold f in Hmult.
  unfold list_mod_deg_1 in Hmult; simpl in Hmult.
  simpl in Hlen.
  apply le_S_n in Hlen.
  simpl in Happ.
  remember (ac_is_zero acf (apply_list f la c .* f c .+ f a)%K) as z eqn:Hz .
  symmetry in Hz.
  destruct z; [ discriminate Hmult | idtac ].
  exfalso; revert Hz.
  apply not_false_iff_true.
  apply ac_prop_is_zero; assumption.

 destruct len.
  destruct la; [ idtac | exfalso; simpl in Hlen; fast_omega Hlen ].
  exfalso; apply Hla; reflexivity.

  simpl in Hmult.
  fold f in Hmult.
  remember (ac_is_zero acf (list_mod_deg_1 f la c)) as z eqn:Hz .
  symmetry in Hz.
  destruct z; [ idtac | discriminate Hmult ].
  apply ac_prop_is_zero in Hz.
  fold f in Hz.
  apply eq_add_S in Hmult.
  destruct la as [| a]; [ exfalso; apply Hla; reflexivity | idtac ].
  simpl in Hlen.
  apply le_S_n in Hlen.
  eapply IHr.
   intros H; apply Hla; clear Hla.
   unfold list_div_deg_1 in H; simpl in H.
   unfold list_mod_deg_1 in Hz; simpl in Hz.
   remember (list_mod_div_deg_1 f la c) as md eqn:Hmd .
   symmetry in Hmd.
   assert (apply_list f la c .= f .0 f)%K as Happ.
    apply list_mod_deg_1_apply.
    unfold list_mod_deg_1; simpl.
    rewrite Hmd.
    destruct md as [| d]; [ reflexivity | idtac ].
    apply list_eq_cons_nil_inv in H.
    destruct H; assumption.

    rewrite Happ in Hz.
    rewrite fld_mul_0_l, fld_add_0_l in Hz.
    constructor; [ assumption | idtac ].
    destruct len.
     destruct la; [ reflexivity | exfalso; simpl in Hlen; omega ].

     simpl in Hmult.
     fold f in Hmult.
     unfold list_div_deg_1 in Hmult; simpl in Hmult.
     revert Hmd H; clear; intros.
     revert md Hmd H.
     induction la as [| a]; intros; [ reflexivity | simpl ].
     constructor.
      simpl in Hmd.
      subst md.
      apply list_eq_cons_nil_inv in H.
      destruct H as (Happ, H).
      assert (apply_list f la c .= f .0 f)%K as Haz.
       apply list_mod_deg_1_apply.
       unfold list_mod_deg_1.
       remember (list_mod_div_deg_1 f la c) as md eqn:Hmd .
       symmetry in Hmd.
       destruct md as [| m]; [ reflexivity | idtac ].
       apply list_eq_cons_nil_inv in H.
       destruct H; assumption.

       rewrite Haz, fld_mul_0_l, fld_add_0_l in Happ.
       assumption.

      simpl in Hmd.
      subst md.
      apply list_eq_cons_nil_inv in H.
      destruct H as (Happ, H).
      eapply IHla; [ reflexivity | eassumption ].

   eassumption.

   unfold list_div_deg_1; simpl.
   revert Hlen; clear; intros.
   revert len Hlen.
   induction la as [| a]; intros; [ apply Nat.le_0_l | simpl ].
   destruct len; [ exfalso; simpl in Hlen; omega | simpl ].
   simpl in Hlen.
   apply le_S_n in Hlen.
   apply le_n_S, IHla; assumption.
Qed.

(* [Walker, p. 100] « If c₁ ≠ 0 is an r-fold root, r ≥ 1, of Φ(z^q) = 0,
   we have:
      Φ(z^q) = (z - c₁)^r Ψ(z), [...] » *)
Theorem phi_zq_eq_z_sub_c₁_psy : ∀ pol ns c₁ r Ψ,
  r = root_multiplicity acf c₁ (Φq f pol ns)
  → Ψ = quotient_phi_x_sub_c_pow_r f (Φq f pol ns) c₁ r
    → (Φq f pol ns .= f POL [(.- f c₁)%K; .1 f%K … []] .^ f r .* f Ψ)%pol.
Proof.
intros pol ns c r Ψ Hr HΨ.
subst Ψ; simpl.
eapply list_root_mul_power_quotient.
symmetry; eassumption.
Qed.

(* [Walker, p. 100] « If c₁ ≠ 0 is an r-fold root, r ≥ 1, of Φ(z^q) = 0,
   we have:
      Φ(z^q) = (z - c₁)^r Ψ(z), Ψ(c₁) ≠ 0 » *)
Theorem psy_c₁_ne_0 : ∀ pol ns c₁ r Ψ,
  ns ∈ newton_segments f pol
  → r = root_multiplicity acf c₁ (Φq f pol ns)
    → Ψ = quotient_phi_x_sub_c_pow_r f (Φq f pol ns) c₁ r
      → (apply_poly f Ψ c₁ .≠ f .0 f)%K.
Proof.
intros pol ns c r Ψ Hns Hr HΨ.
remember (Φq f pol ns) as phi eqn:Hphi .
unfold Φq in Hphi; simpl in Hphi.
unfold poly_left_shift in Hphi; simpl in Hphi.
rewrite Nat.sub_diag, skipn_pad in Hphi; simpl in Hphi.
subst Ψ; simpl.
unfold apply_poly; simpl.
unfold root_multiplicity in Hr.
remember (al phi) as la eqn:Hla .
subst phi; simpl in Hla.
symmetry in Hr.
eapply list_div_x_sub_c_ne_0; [ idtac | eassumption | reflexivity ].
rewrite Hla; intros H.
apply list_eq_cons_nil_inv in H.
destruct H as (H, _).
remember (ini_pt ns) as jj eqn:Hj .
destruct jj as (jq, αj); simpl.
remember Hns as HH; clear HeqHH.
apply exists_ini_pt_nat in HH.
destruct HH as (j, (x, Hx)).
rewrite <- Hj in Hx; injection Hx; clear Hx; intros; subst jq x.
simpl in H.
revert H.
eapply val_coeff_non_zero_in_newt_segm; [ eassumption | idtac | idtac ].
 symmetry in Hj.
 left; eassumption.

 unfold nofq, Qnat; simpl.
 rewrite Nat2Z.id; reflexivity.
Qed.

End theorems.
