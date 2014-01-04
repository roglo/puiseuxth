(* Fsummation.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Field.

Set Implicit Arguments.

Open Scope nat_scope.

Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) (at level 70, y at next level).
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) (at level 70, y at next level).

Fixpoint summation_aux α (f : field α) b len g :=
  match len with
  | O => .0 f%F
  | S len₁ => (g b .+ f summation_aux f (S b) len₁ g)%F
  end.

Definition summation α (f : field α) b e g := summation_aux f b (S e - b) g.

Notation "'Σ' f ( i = b , e ) '_' g" := (summation f b e (λ i, (g)%F))
  (at level 0, f at level 0, i at level 0, b at level 60, e at level 60,
   g at level 40).

Section theorems_summation.

Variable α : Type.
Variable f : field α.

Lemma summation_aux_compat : ∀ g h b₁ b₂ len,
  (∀ i, 0 ≤ i < len → (g (b₁ + i) .= f h (b₂ + i))%F)
  → (summation_aux f b₁ len g .= f summation_aux f b₂ len h)%F.
Proof.
intros g h b₁ b₂ len Hgh.
revert b₁ b₂ Hgh.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen.
 apply fld_add_compat_r.
 assert (0 ≤ 0 < S len) as H.
  split; [ reflexivity | apply Nat.lt_0_succ ].

  apply Hgh in H.
  do 2 rewrite Nat.add_0_r in H; assumption.

 intros i Hi.
 do 2 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hgh.
 split; [ apply Nat.le_0_l | idtac ].
 apply lt_n_S.
 destruct Hi; assumption.
Qed.

Lemma summation_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i .= f h i)%F)
  → (Σ f (i = b, k)_ g i .= f Σ f (i = b, k) _ h i)%F.
Proof.
intros g h b k Hgh.
apply summation_aux_compat.
intros i (_, Hi).
apply Hgh.
split; [ apply Nat.le_add_r | omega ].
Qed.

Lemma summation_mul_comm : ∀ g h b k,
  (Σ f (i = b, k) _ g i .* f h i
   .= f Σ f (i = b, k) _ h i .* f g i)%F.
Proof.
intros g h b len.
apply summation_compat; intros i Hi.
apply fld_mul_comm.
Qed.

Lemma all_0_summation_aux_0 : ∀ g b len,
  (∀ i, (b ≤ i < b + len) → (g i .= f .0 f)%F)
  → (summation_aux f b len (λ i, g i) .= f .0 f)%F.
Proof.
intros g b len H.
revert b H.
induction len; intros; [ reflexivity | simpl ].
rewrite H; [ idtac | omega ].
rewrite fld_add_0_l, IHlen; [ reflexivity | idtac ].
intros i Hi; apply H; omega.
Qed.

Lemma all_0_summation_0 : ∀ g i₁ i₂,
  (∀ i, i₁ ≤ i ≤ i₂ → (g i .= f .0 f)%F)
  → (Σ f (i = i₁, i₂) _ g i .= f .0 f)%F.
Proof.
intros g i₁ i₂ H.
apply all_0_summation_aux_0.
intros i (H₁, H₂).
apply H.
split; [ assumption | omega ].
Qed.

Lemma summation_aux_succ_last : ∀ g b len,
  (summation_aux f b (S len) g .= f
   summation_aux f b len g .+ f g (b + len))%F.
Proof.
intros g b len.
revert b.
induction len; intros.
 simpl.
 rewrite fld_add_0_l, fld_add_0_r, Nat.add_0_r.
 reflexivity.

 remember (S len) as x; simpl; subst x.
 rewrite IHlen.
 simpl.
 rewrite fld_add_assoc, Nat.add_succ_r.
 reflexivity.
Qed.

Lemma summation_aux_rtl : ∀ g b len,
  (summation_aux f b len g .= f
   summation_aux f b len (λ i, g (b + len - 1 + b - i)))%F.
Proof.
(* supprimer ce putain de omega trop lent *)
intros g b len.
revert g b.
induction len; intros; [ reflexivity | idtac ].
remember (S len) as x.
rewrite Heqx in |- * at 1.
simpl; subst x.
rewrite IHlen.
rewrite summation_aux_succ_last.
replace (b + S len - 1 + b - (b + len)) with b by omega.
rewrite fld_add_comm.
apply fld_add_compat_r.
apply summation_aux_compat.
intros i Hi.
simpl.
rewrite Nat.sub_0_r.
replace (b + len + S b - S (b + i)) with
 (b + S len - 1 + b - (b + i)) by omega.
reflexivity.
Qed.

Lemma summation_rtl : ∀ g b k,
  (Σ f (i = b, k) _ g i .= f Σ f (i = b, k) _ g (k + b - i))%F.
Proof.
(* supprimer ce putain de omega trop lent *)
intros g b k.
unfold summation.
rewrite summation_aux_rtl.
apply summation_aux_compat; intros i Hi.
simpl.
destruct b; simpl.
 rewrite Nat.sub_0_r; reflexivity.

 rewrite Nat.sub_0_r.
 replace (b + (k - b) + S b - S (b + i)) with (k + S b - S (b + i))
  by omega.
 reflexivity.
Qed.

Lemma summation_aux_mul_swap : ∀ a g b len,
  (summation_aux f b len (λ i, a .* f g i) .= f
   a .* f summation_aux f b len g)%F.
Proof.
intros a g b len; revert b.
induction len; intros; simpl.
 rewrite fld_mul_0_r; reflexivity.

 rewrite IHlen, fld_mul_add_distr_l.
 reflexivity.
Qed.

Lemma summation_aux_summation_aux_mul_swap : ∀ g₁ g₂ g₃ b₁ b₂ len,
  (summation_aux f b₁ len
     (λ i, summation_aux f b₂ (g₁ i) (λ j, g₂ i .* f g₃ i j))
   .= f summation_aux f b₁ len
       (λ i, g₂ i .* f summation_aux f b₂ (g₁ i) (λ j, g₃ i j)))%F.
Proof.
intros g₁ g₂ g₃ b₁ b₂ len.
revert b₁ b₂.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen.
apply fld_add_compat_r.
apply summation_aux_mul_swap.
Qed.

Lemma summation_summation_mul_swap : ∀ g₁ g₂ g₃ k,
  (Σ f (i = 0, k) _ Σ f (j = 0, g₁ i) _ g₂ i .* f g₃ i j
   .= f Σ f (i = 0, k) _ g₂ i .* f Σ f (j = 0, g₁ i) _ g₃ i j)%F.
Proof.
intros g₁ g₂ g₃ k.
apply summation_aux_summation_aux_mul_swap.
Qed.

Lemma summation_only_one_non_0 : ∀ g b v k,
  (b ≤ v ≤ k)
  → (∀ i, (b ≤ i ≤ k) → (i ≠ v) → (g i .= f .0 f)%F)
    → (Σ f (i = b, k) _ g i .= f g v)%F.
Proof.
intros g b v k (Hbv, Hvk) Hi.
unfold summation.
rewrite Nat.sub_succ_l; [ idtac | etransitivity; eassumption ].
remember (k - b) as len.
replace k with (b + len) in * by omega.
clear k Heqlen.
revert b v Hbv Hvk Hi.
induction len; intros.
 simpl.
 rewrite fld_add_0_r.
 replace b with v ; [ reflexivity | idtac ].
 rewrite Nat.add_0_r in Hvk.
 apply Nat.le_antisymm; assumption.

 remember (S len) as x; simpl; subst x.
 destruct (eq_nat_dec b v) as [H₁| H₁].
  subst b.
  rewrite all_0_summation_aux_0.
   rewrite fld_add_0_r; reflexivity.

   intros j Hj.
   apply Hi; omega.

  rewrite Hi; [ idtac | omega | assumption ].
  rewrite fld_add_0_l.
  apply IHlen.
   omega.

   rewrite Nat.add_succ_l, <- Nat.add_succ_r; assumption.

   intros j Hjb Hj.
   apply Hi; [ omega | assumption ].
Qed.

Lemma summation_summation_shift : ∀ g k,
  (Σ f (i = 0, k) _ Σ f (j = i, k) _ g i j .= f
   Σ f (i = 0, k) _ Σ f (j = 0, k - i) _ g i (i + j))%F.
Proof.
intros g k.
apply summation_compat; intros i Hi.
unfold summation.
rewrite Nat.sub_0_r.
rewrite Nat.sub_succ_l; [ idtac | destruct Hi; assumption ].
apply summation_aux_compat; intros j Hj.
rewrite Nat.add_0_l; reflexivity.
Qed.

Lemma summation_only_one : ∀ g n, (Σ f (i = n, n) _ g i .= f g n)%F.
Proof.
intros g n.
unfold summation.
rewrite Nat.sub_succ_l; [ idtac | reflexivity ].
rewrite Nat.sub_diag; simpl.
rewrite fld_add_0_r; reflexivity.
Qed.

Lemma summation_succ : ∀ g b k,
  (b ≤ S k)
  → (Σ f (i = b, S k) _ g i .= f Σ f (i = b, k) _ g i .+ f g (S k))%F.
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ_l; [ idtac | assumption ].
rewrite summation_aux_succ_last.
rewrite Nat.add_sub_assoc; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub.
reflexivity.
Qed.

Lemma summation_aux_succ_fst : ∀ g b len,
  (summation_aux f b (S len) g .= f g b .+ f summation_aux f (S b) len g)%F.
Proof. reflexivity. Qed.

Lemma summation_split_first : ∀ g b k,
  b ≤ k
  → (Σ f (i = b, k) _ g i .= f g b .+ f Σ f (i = S b, k) _ g i)%F.
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ.
rewrite <- summation_aux_succ_fst.
rewrite <- Nat.sub_succ_l; [ reflexivity | assumption ].
Qed.

Lemma summation_add_distr : ∀ g h b k,
  (Σ f (i = b, k) _ (g i .+ f h i) .= f
   Σ f (i = b, k) _ g i .+ f Σ f (i = b, k) _ h i)%F.
Proof.
intros g h b k.
destruct (le_dec b k) as [Hbk| Hbk].
 revert b Hbk.
 induction k; intros.
  destruct b.
   do 3 rewrite summation_only_one; reflexivity.

   unfold summation; simpl; rewrite fld_add_0_r; reflexivity.

  rewrite summation_succ; [ idtac | assumption ].
  rewrite summation_succ; [ idtac | assumption ].
  rewrite summation_succ; [ idtac | assumption ].
  destruct (eq_nat_dec b (S k)) as [H₂| H₂].
   subst b.
   unfold summation; simpl.
   rewrite Nat.sub_diag; simpl.
   do 2 rewrite fld_add_0_l; rewrite fld_add_0_l.
   reflexivity.

   apply le_neq_lt in Hbk; [ idtac | assumption ].
   apply Nat.succ_le_mono in Hbk.
   rewrite IHk; [ idtac | assumption ].
   do 2 rewrite <- fld_add_assoc.
   apply fld_add_compat_l.
   rewrite fld_add_comm.
   rewrite <- fld_add_assoc.
   apply fld_add_compat_l.
   rewrite fld_add_comm.
   reflexivity.

 unfold summation.
 apply Nat.nle_gt in Hbk.
 replace (S k - b) with O by omega; simpl.
 rewrite fld_add_0_r; reflexivity.
Qed.

Lemma summation_summation_exch : ∀ g k,
  (Σ f (j = 0, k) _ Σ f (i = 0, j) _ g i j .= f
   Σ f (i = 0, k) _ Σ f (j = i, k) _ g i j)%F.
Proof.
intros g k.
induction k; [ reflexivity | idtac ].
rewrite summation_succ; [ idtac | apply Nat.le_0_l ].
rewrite summation_succ; [ idtac | apply Nat.le_0_l ].
rewrite summation_succ; [ idtac | apply Nat.le_0_l ].
rewrite IHk.
rewrite summation_only_one.
rewrite fld_add_assoc.
apply fld_add_compat_r.
rewrite <- summation_add_distr.
apply summation_compat; intros i (_, Hi).
rewrite summation_succ; [ reflexivity | idtac ].
apply Nat.le_le_succ_r; assumption.
Qed.

Lemma summation_aux_fun_add : ∀ g h b len,
  (summation_aux f b len (λ i, g i .+ f h i) .= f
   summation_aux f b len g .+ f summation_aux f b len h)%F.
Proof.
intros g h b len.
symmetry.
revert b.
induction len; intros; simpl; [ apply fld_add_0_l | idtac ].
rewrite fld_add_shuffle0.
do 3 rewrite <- fld_add_assoc.
do 2 apply fld_add_compat_l.
rewrite fld_add_comm.
apply IHlen.
Qed.

Lemma summation_fun_add : ∀ g h b e,
  (Σ f (i = b, e) _ (g i .+ f h i) .= f
   Σ f (i = b, e) _ g i .+ f Σ f (i = b, e) _ h i)%F.
Proof.
intros g h b e.
apply summation_aux_fun_add.
Qed.

Lemma summation_aux_ub_add : ∀ g b k₁ k₂,
  (summation_aux f b (k₁ + k₂) g .= f
   summation_aux f b k₁ g .+ f summation_aux f (b + k₁) k₂ g)%F.
Proof.
intros g b k₁ k₂.
revert b k₁.
induction k₂; intros.
 simpl.
 rewrite Nat.add_0_r, fld_add_0_r; reflexivity.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 rewrite IHk₂; simpl.
 rewrite <- Nat.add_succ_r.
 rewrite fld_add_assoc.
 apply fld_add_compat_r.
 clear k₂ IHk₂.
 revert b.
 induction k₁; intros; simpl.
  rewrite Nat.add_0_r.
  apply fld_add_comm.

  rewrite <- fld_add_assoc.
  rewrite IHk₁.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l; reflexivity.
Qed.

Lemma summation_ub_add : ∀ g k₁ k₂,
  (Σ f (i = 0, k₁ + k₂) _ g i .= f
   Σ f (i = 0, k₁) _ g i .+ f Σ f (i = S k₁, k₁ + k₂) _ g i)%F.
Proof.
intros g k₁ k₂.
unfold summation.
do 2 rewrite Nat.sub_0_r.
rewrite <- Nat.add_succ_l.
rewrite summation_aux_ub_add; simpl.
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Lemma summation_aux_succ_first : ∀ g b k,
  (summation_aux f b (S k) g .= f g b .+ f summation_aux f (S b) k g)%F.
Proof. reflexivity. Qed.

Lemma summation_aux_mul_summation_aux_summation_aux : ∀ g k n,
  (summation_aux f 0 (S k * S n) g .= f
   summation_aux f 0 (S k)
     (λ i, summation_aux f 0 (S n) (λ j, g (i * S n + j)%nat)))%F.
Proof.
intros g k n.
revert n; induction k; intros.
 simpl; rewrite Nat.add_0_r, fld_add_0_r; reflexivity.

 remember (S n) as x.
 remember (S k) as y.
 simpl; subst x y.
 rewrite Nat.add_comm.
 rewrite summation_aux_ub_add, IHk.
 symmetry; rewrite fld_add_comm.
 symmetry.
 rewrite summation_aux_succ_first.
 rewrite fld_add_shuffle0, fld_add_comm.
 symmetry.
 replace (S k) with (k + 1)%nat by omega.
 rewrite summation_aux_ub_add.
 rewrite <- fld_add_assoc.
 apply fld_add_compat_l.
 simpl.
 rewrite fld_add_comm.
 apply fld_add_compat_l.
 symmetry; rewrite Nat.add_comm; simpl.
 rewrite Nat.add_0_r, fld_add_0_r.
 apply fld_add_compat_l.
 apply summation_aux_compat; intros i Hi; simpl.
 rewrite Nat.add_succ_r; reflexivity.
Qed.

Lemma summation_mul_summation_summation : ∀ g n k,
  (0 < n)%nat
  → (0 < k)%nat
    → (Σ f (i = 0, k * n - 1) _ g i .= f
       Σ f (i = 0, k - 1) _ Σ f (j = 0, n - 1) _ g (i * n + j)%nat)%F.
Proof.
intros g n k Hn Hk.
unfold summation.
do 2 rewrite Nat.sub_0_r.
destruct n; [ exfalso; revert Hn; apply Nat.lt_irrefl | clear Hn ].
destruct k; [ exfalso; revert Hk; apply Nat.lt_irrefl | clear Hk ].
rewrite Nat.sub_succ, Nat.sub_0_r.
rewrite <- Nat.sub_succ_l, Nat.sub_succ, Nat.sub_0_r.
 rewrite summation_aux_mul_summation_aux_summation_aux.
 apply summation_aux_compat; intros i Hi.
 rewrite Nat.sub_succ, Nat.sub_0_r, Nat.sub_0_r.
 reflexivity.

 simpl; apply le_n_S, Nat.le_0_l.
Qed.

Lemma inserted_0_summation : ∀ g h k n,
  n ≠ O
  → (∀ i, i mod n ≠ O → (g i .= f .0 f)%F)
    → (∀ i, (g (n * i)%nat .= f h i)%F)
      → (Σ f (i = 0, k * n) _ g i .= f Σ f (i = 0, k) _ h i)%F.
Proof.
intros g h k n Hn Hf Hfg.
destruct k.
 rewrite Nat.mul_0_l.
 apply summation_compat; intros i (_, Hi).
 apply Nat.le_0_r in Hi; subst i.
 rewrite <- Hfg, Nat.mul_0_r; reflexivity.

 destruct n; [ exfalso; apply Hn; reflexivity | clear Hn ].
 replace (S k * S n)%nat with (S k * S n - 1 + 1)%nat .
  rewrite summation_ub_add.
  rewrite summation_mul_summation_summation; try apply Nat.lt_0_succ.
  rewrite Nat_sub_succ_1, Nat.add_comm, summation_only_one.
  symmetry.
  rewrite <- Nat.add_1_r, summation_ub_add, Nat.add_1_r.
  rewrite summation_only_one, fld_add_comm, <- Hfg.
  symmetry.
  rewrite fld_add_comm.
  rewrite Nat.add_sub_assoc.
   rewrite Nat.add_comm, Nat.add_sub, Nat.mul_comm.
   apply fld_add_compat_l, summation_compat; intros i Hi.
   rewrite Nat_sub_succ_1.
   rewrite <- Hfg.
   rewrite Nat.mul_comm.
   rewrite summation_only_one_non_0 with (v := O).
    rewrite Nat.add_0_r, Nat.mul_comm.
    reflexivity.

    split; [ reflexivity | apply Nat.le_0_l ].

    intros j Hjn Hj.
    rewrite Hf; [ reflexivity | idtac ].
    rewrite Nat.add_comm.
    rewrite Nat.mul_comm, Nat.mod_add; auto.
    intros H; apply Hj; clear Hj.
    apply Nat.mod_divides in H; auto.
    destruct H as (c, Hc).
    destruct c.
     rewrite Nat.mul_0_r in Hc; assumption.

     rewrite Hc in Hjn.
     rewrite Nat.mul_comm in Hjn.
     simpl in Hjn.
     destruct Hjn as (_, H).
     apply Nat.nlt_ge in H.
     exfalso; apply H.
     apply le_n_S, Nat.le_add_r.

   simpl; apply le_n_S, Nat.le_0_l.

  simpl.
  rewrite Nat.sub_0_r.
  rewrite Nat.add_comm; reflexivity.
Qed.

Lemma summation_add_add_sub : ∀ g b k n,
  (Σ f (i = b, k) _ g i .= f Σ f (i = b + n, k + n) _ g (i - n)%nat)%F.
Proof.
intros g b k n.
unfold summation.
replace (S (k + n) - (b + n))%nat with (S k - b)%nat by omega.
apply summation_aux_compat.
intros i Hi.
replace (b + n + i - n)%nat with (b + i)%nat by omega.
reflexivity.
Qed.

End theorems_summation.

Close Scope nat_scope.
