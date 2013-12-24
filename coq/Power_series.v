(* Power_series.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Nbar.
Require Import Misc.

Set Implicit Arguments.

Record power_series α :=
  { terms : nat → α;
    stop : Nbar }.

Delimit Scope K_scope with K.
Delimit Scope series_scope with ser.

Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%nat (at level 70, y at next level).
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat (at level 70, y at next level).

Section definitions.

Variable α : Type.
Variable F : field α.

Delimit Scope K_scope with K.
Notation "0" := (fld_zero F) : K_scope.
Notation "1" := (fld_one F) : K_scope.
Notation "- a" := (fld_opp F a) : K_scope.
Notation "a = b" := (fld_eq F a b) : K_scope.
Notation "a ≠ b" := (not (fld_eq F a b)) : K_scope.
Notation "a + b" := (fld_add F a b) : K_scope.
Notation "a - b" := (fld_add F a (fld_opp F b)) : K_scope.
Notation "a * b" := (fld_mul F a b) : K_scope.
Notation "¹/ a" := (fld_inv F a) (at level 1) : K_scope.

Definition series_nth n (s : power_series α) :=
  if Nbar.lt_dec (fin n) (stop s) then terms s n else 0%K.

Notation "s [ i ]" := (series_nth i s) (at level 1).

Definition series_inf (a : power_series α) :=
  {| terms i := series_nth i a; stop := ∞ |}.

Definition series_0 := {| terms i := 0%K; stop := 0 |}.
Definition series_1 := {| terms i := 1%K; stop := 1 |}.

Inductive eq_series : power_series α → power_series α → Prop :=
  eq_series_base : ∀ s₁ s₂,
    (∀ i, (s₁ [i] = s₂ [i])%K)
    → eq_series s₁ s₂.

Notation "0" := series_0 : series_scope.
Notation "1" := series_1 : series_scope.
Notation "a = b" := (eq_series a b) : series_scope.
Notation "a ≠ b" := (not (eq_series a b)) : series_scope.

Theorem eq_series_refl : reflexive _ eq_series.
Proof.
intros s.
constructor; reflexivity.
Qed.

Theorem eq_series_sym : symmetric _ eq_series.
Proof.
intros s₁ s₂ H.
inversion H; subst.
constructor.
intros i; symmetry; apply H0.
Qed.

Theorem eq_series_trans : transitive _ eq_series.
Proof.
intros s₁ s₂ s₃ H₁ H₂.
inversion H₁; inversion H₂; subst.
constructor.
etransitivity; [ apply H | apply H2 ].
Qed.

End definitions.

Add Parametric Relation α (F : field α) : (power_series α) (eq_series F)
 reflexivity proved by (eq_series_refl F)
 symmetry proved by (eq_series_sym (F := F))
 transitivity proved by (eq_series_trans (F := F))
 as eq_series_rel.

(* *)

Lemma if_lt_dec_fin_inf : ∀ A i (a b : A),
  (if Nbar.lt_dec (fin i) ∞ then a else b) = a.
Proof.
intros A i a b.
destruct (Nbar.lt_dec (fin i) ∞) as [H| H]; [ reflexivity | idtac ].
exfalso; apply H; constructor.
Qed.

Lemma if_lt_dec_0_1 : ∀ A (a b : A),
  (if Nbar.lt_dec 0 1 then a else b) = a.
Proof.
intros A a b.
destruct (Nbar.lt_dec 0 1) as [H| H]; [ reflexivity | idtac ].
exfalso; apply H, Nbar.lt_0_1.
Qed.

Section add_mul.

Variable α : Type.
Variable F : field α.

Delimit Scope K_scope with K.
Notation "0" := (fld_zero F) : K_scope.
Notation "1" := (fld_one F) : K_scope.
Notation "- a" := (fld_opp F a) : K_scope.
Notation "a = b" := (fld_eq F a b) : K_scope.
Notation "a ≠ b" := (not (fld_eq F a b)) : K_scope.
Notation "a + b" := (fld_add F a b) : K_scope.
Notation "a - b" := (fld_add F a (fld_opp F b)) : K_scope.
Notation "a * b" := (fld_mul F a b) : K_scope.
Notation "¹/ a" := (fld_inv F a) (at level 1) : K_scope.
Notation "s [ i ]" := (series_nth F i s) (at level 1).

(* series_add *)

Definition series_add s₁ s₂ :=
  {| terms i := (s₁[i] + s₂[i])%K;
     stop := Nbar.max (stop s₁) (stop s₂) |}.

Definition series_opp s :=
  {| terms i := (- terms s i)%K; stop := stop s |}.

Notation "0" := (series_0 F) : series_scope.
Notation "1" := (series_1 F) : series_scope.
Notation "a = b" := (eq_series F a b) : series_scope.
Notation "a ≠ b" := (not (eq_series F a b)) : series_scope.
Notation "- a" := (series_opp a) : series_scope.
Notation "a + b" := (series_add a b) : series_scope.
Notation "a - b" := (series_add a (series_opp b)) : series_scope.

Theorem series_add_comm : ∀ s₁ s₂, (s₁ + s₂ = s₂ + s₁)%ser.
Proof.
intros s₁ s₂.
constructor; simpl.
intros i.
unfold series_nth; simpl.
rewrite Nbar.max_comm.
destruct (Nbar.max (stop s₂) (stop s₁)) as [n| ].
 destruct (Nbar.lt_dec (fin i) (fin n)) as [Hlt| ]; [ idtac | reflexivity ].
 rewrite fld_add_comm; reflexivity.

 do 2 rewrite if_lt_dec_fin_inf.
 rewrite fld_add_comm; reflexivity.
Qed.

Theorem series_add_assoc : ∀ s₁ s₂ s₃, (s₁ + (s₂ + s₃) = (s₁ + s₂) + s₃)%ser.
Proof.
intros s₁ s₂ s₃.
unfold series_add; simpl.
constructor; simpl.
intros i.
unfold series_nth; simpl.
rewrite Nbar.max_assoc.
remember (Nbar.lt_dec (fin i) (stop s₁)) as lt₁.
remember (Nbar.lt_dec (fin i) (stop s₂)) as lt₂.
remember (Nbar.lt_dec (fin i) (stop s₃)) as lt₃.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂))) as lt₄.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))) as lt₅.
clear Heqlt₁ Heqlt₂ Heqlt₃ Heqlt₄ Heqlt₅.
remember (Nbar.max (Nbar.max (stop s₁) (stop s₂)) (stop s₃)) as n.
destruct (Nbar.lt_dec (fin i) n) as [Hlt| ]; [ subst n | reflexivity ].
destruct lt₄ as [Hlt₄| Hge₄].
 destruct lt₅ as [Hlt₅| Hge₅].
  destruct lt₁ as [Hlt₁| Hge₁].
   destruct lt₂ as [Hlt₂| Hge₂].
    destruct lt₃ as [Hlt₃| Hge₃]; [ apply fld_add_assoc | idtac ].
    rewrite fld_add_0_r; symmetry.
    rewrite <- fld_add_assoc.
    rewrite fld_add_0_r; reflexivity.

    rewrite <- fld_add_assoc, fld_add_0_l; reflexivity.

   rewrite <- fld_add_assoc, fld_add_0_l; reflexivity.

  rewrite fld_add_0_r; symmetry.
  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₅; clear Hge₅.
   apply Nbar.max_lt_iff; left; assumption.

   rewrite <- fld_add_assoc, fld_add_0_l.
   destruct lt₃ as [Hlt₃| Hge₃].
    exfalso; apply Hge₅; clear Hge₅.
    apply Nbar.max_lt_iff; right; assumption.

    rewrite fld_add_0_r; reflexivity.

 rewrite fld_add_0_l.
 destruct lt₁ as [Hlt₁| Hge₁].
  exfalso; apply Hge₄; clear Hge₄.
  apply Nbar.max_lt_iff; left; assumption.

  rewrite fld_add_0_l.
  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₄; clear Hge₄.
   apply Nbar.max_lt_iff; right; assumption.

   destruct lt₅ as [Hlt₅| Hge₅].
    rewrite fld_add_0_l; reflexivity.

    destruct lt₃ as [Hlt₃| Hge₃]; [ idtac | reflexivity ].
    exfalso; apply Hge₅; clear Hge₅.
    apply Nbar.max_lt_iff; right; assumption.
Qed.

Lemma stop_series_add_0_l : ∀ s, stop (0 + s)%ser = stop s.
Proof.
intros s; simpl.
destruct (stop s); reflexivity.
Qed.

Lemma series_nth_series_0 : ∀ i, (0%ser [i] = 0)%K.
Proof.
intros i.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) 0); reflexivity.
Qed.

Theorem series_add_0_l : ∀ s, (0 + s = s)%ser.
Proof.
intros s.
constructor; intros i.
unfold series_nth.
rewrite stop_series_add_0_l; simpl.
remember (Nbar.lt_dec (fin i) (stop s)) as d.
destruct d as [H₁| H₁]; [ idtac | reflexivity ].
rewrite series_nth_series_0.
rewrite fld_add_0_l.
unfold series_nth.
rewrite <- Heqd; reflexivity.
Qed.

Theorem series_add_opp_r : ∀ s, (s - s = 0)%ser.
Proof.
intros s.
constructor; intros i.
unfold series_nth; simpl.
rewrite Nbar.max_id.
destruct (Nbar.lt_dec (fin i) 0) as [H₁| H₁].
 exfalso; revert H₁; apply Nbar.nlt_0_r.

 clear H₁.
 unfold series_nth; simpl.
 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₁| H₁]; [ idtac | reflexivity ].
 apply fld_add_opp_r.
Qed.

Theorem series_add_opp_l : ∀ s, (- s + s = 0)%ser.
Proof.
intros s.
rewrite series_add_comm.
apply series_add_opp_r.
Qed.

(* series_mul *)

Fixpoint sigma_aux b len f :=
  match len with
  | O => 0%K
  | S len₁ => (f b + sigma_aux (S b) len₁ f)%K
  end.

Definition sigma b e f := sigma_aux b (S e - b) f.

Notation "'Σ' ( i = b , e ) '_' f" := (sigma b e (λ i, (f)%K))
  (at level 0, i at level 0, b at level 60, e at level 60, f at level 40).

Definition convol_mul a b k := Σ (i = 0, k) _ a[i] * b[k-i].

Definition series_mul a b :=
  {| terms k := convol_mul a b k;
     stop := Nbar.add (stop a) (stop b) |}.

Notation "a * b" := (series_mul a b) : series_scope.

Lemma sigma_aux_compat : ∀ f g b₁ b₂ len,
  (∀ i, 0 ≤ i < len → (f (b₁ + i)%nat = g (b₂ + i)%nat)%K)
  → (sigma_aux b₁ len f = sigma_aux b₂ len g)%K.
Proof.
intros f g b₁ b₂ len Hfg.
revert b₁ b₂ Hfg.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen.
 apply fld_add_compat_r.
 assert (0 ≤ 0 < S len) as H.
  split; [ reflexivity | apply Nat.lt_0_succ ].

  apply Hfg in H.
  do 2 rewrite Nat.add_0_r in H; assumption.

 intros i Hi.
 do 2 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hfg.
 split; [ apply Nat.le_0_l | idtac ].
 apply lt_n_S.
 destruct Hi; assumption.
Qed.

Lemma sigma_compat : ∀ f g b k,
  (∀ i, b ≤ i ≤ k → (f i = g i)%K)
  → (Σ (i = b, k)_ f i = Σ (i = b, k) _ g i)%K.
Proof.
intros f g b k Hfg.
apply sigma_aux_compat.
intros i (_, Hi).
apply Hfg.
split; [ apply Nat.le_add_r | omega ].
Qed.

Lemma sigma_mul_comm : ∀ f g b k,
  (Σ (i = b, k) _ f i * g i
   = Σ (i = b, k) _ g i * f i)%K.
Proof.
intros f g b len.
apply sigma_compat; intros i Hi.
apply fld_mul_comm.
Qed.

Lemma all_0_sigma_aux_0 : ∀ f b len,
  (∀ i, (b ≤ i < b + len)%nat → (f i = 0)%K)
  → (sigma_aux b len (λ i, f i) = 0)%K.
Proof.
intros f b len H.
revert b H.
induction len; intros; [ reflexivity | simpl ].
rewrite H; [ idtac | omega ].
rewrite fld_add_0_l, IHlen; [ reflexivity | idtac ].
intros i Hi; apply H; omega.
Qed.

Lemma all_0_sigma_0 : ∀ f i₁ i₂,
  (∀ i, i₁ ≤ i ≤ i₂ → (f i = 0)%K) → (Σ (i = i₁, i₂) _ f i = 0)%K.
Proof.
intros f i₁ i₂ H.
apply all_0_sigma_aux_0.
intros i (H₁, H₂).
apply H.
split; [ assumption | omega ].
Qed.

End add_mul.

Add Parametric Morphism α (F : field α) : (series_mul F)
  with signature eq_series F ==> eq_series F ==> eq_series F
  as series_mul_morph.
Proof.
intros a b Hab c d Hcd.
constructor; intros k.
inversion Hab; subst.
inversion Hcd; subst.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin k) (stop a + stop c)) as [H₁| H₁].
 destruct (Nbar.lt_dec (fin k) (stop b + stop d)) as [H₂| H₂].
  unfold convol_mul.
  apply sigma_compat; intros i Hi.
  rewrite H, H0; reflexivity.

  unfold convol_mul.
  apply all_0_sigma_0; intros i Hi.
  rewrite H, H0.
  unfold series_nth.
  destruct (Nbar.lt_dec (fin i) (stop b)) as [H₄| H₄].
   destruct (Nbar.lt_dec (fin (k - i)) (stop d)) as [H₅| H₅].
    exfalso; apply H₂.
    replace k with (i + (k - i))%nat by omega.
    rewrite Nbar.fin_inj_add.
    remember (stop b) as st eqn:Hst .
    symmetry in Hst.
    destruct st; [ idtac | constructor ].
    apply Nbar.add_lt_mono; auto; intros HH; discriminate HH.

    rewrite fld_mul_0_r; reflexivity.

   rewrite fld_mul_0_l; reflexivity.

 destruct (Nbar.lt_dec (fin k) (stop b + stop d)) as [H₂| H₂].
  unfold convol_mul.
  symmetry.
  apply all_0_sigma_0; intros i Hi.
  rewrite <- H, <- H0.
  unfold series_nth.
  destruct (Nbar.lt_dec (fin i) (stop a)) as [H₄| H₄].
   destruct (Nbar.lt_dec (fin (k - i)) (stop c)) as [H₅| H₅].
    exfalso; apply H₁.
    replace k with (i + (k - i))%nat by omega.
    rewrite Nbar.fin_inj_add.
    remember (stop a) as st eqn:Hst .
    symmetry in Hst.
    destruct st; [ idtac | constructor ].
    apply Nbar.add_lt_mono; auto; intros HH; discriminate HH.

    rewrite fld_mul_0_r; reflexivity.

   rewrite fld_mul_0_l; reflexivity.

  reflexivity.
Qed.

Section misc_lemmas.

Variable α : Type.
Variable F : field α.

Notation "0" := (fld_zero F) : K_scope.
Notation "1" := (fld_one F) : K_scope.
Notation "- a" := (fld_opp F a) : K_scope.
Notation "a = b" := (fld_eq F a b) : K_scope.
Notation "a ≠ b" := (not (fld_eq F a b)) : K_scope.
Notation "a + b" := (fld_add F a b) : K_scope.
Notation "a - b" := (fld_add F a (fld_opp F b)) : K_scope.
Notation "a * b" := (fld_mul F a b) : K_scope.
Notation "¹/ a" := (fld_inv F a) (at level 1) : K_scope.

Notation "'Σ' ( i = b , e ) '_' f" := (sigma F b e (λ i, (f)%K))
  (at level 0, i at level 0, b at level 60, e at level 60, f at level 40).

Notation "0" := (series_0 F) : series_scope.
Notation "1" := (series_1 F) : series_scope.
Notation "a = b" := (eq_series F a b) : series_scope.
Notation "a ≠ b" := (not (eq_series F a b)) : series_scope.
Notation "- a" := (series_opp a) : series_scope.
Notation "a + b" := (series_add a b) : series_scope.
Notation "a - b" := (series_add a (series_opp b)) : series_scope.
Notation "a * b" := (series_mul F a b) : series_scope.

Lemma sigma_aux_succ : ∀ f b len,
  (sigma_aux F b (S len) f = sigma_aux F b len f + f (b + len)%nat)%K.
Proof.
intros f b len.
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

Lemma sigma_aux_rtl : ∀ f b len,
  (sigma_aux F b len f =
   sigma_aux F b len (λ i, f (b + len - 1 + b - i)%nat))%K.
Proof.
(* supprimer ce putain de omega trop lent *)
intros f b len.
revert f b.
induction len; intros; [ reflexivity | idtac ].
remember (S len) as x.
rewrite Heqx in |- * at 1.
simpl; subst x.
rewrite IHlen.
rewrite sigma_aux_succ.
replace (b + S len - 1 + b - (b + len))%nat with b by omega.
rewrite fld_add_comm.
apply fld_add_compat_r.
apply sigma_aux_compat.
intros i Hi.
simpl.
rewrite Nat.sub_0_r.
replace (b + len + S b - S (b + i))%nat with
 (b + S len - 1 + b - (b + i))%nat by omega.
reflexivity.
Qed.

Lemma sigma_rtl : ∀ f b k,
  (Σ (i = b, k) _ f i = Σ (i = b, k) _ f (k + b - i)%nat)%K.
Proof.
(* supprimer ce putain de omega trop lent *)
intros f b k.
unfold sigma.
rewrite sigma_aux_rtl.
apply sigma_aux_compat; intros i Hi.
simpl.
destruct b; simpl.
 rewrite Nat.sub_0_r; reflexivity.

 rewrite Nat.sub_0_r.
 replace (b + (k - b) + S b - S (b + i))%nat with (k + S b - S (b + i))%nat
  by omega.
 reflexivity.
Qed.

Theorem convol_mul_comm : ∀ a b i,
  (convol_mul F a b i = convol_mul F b a i)%K.
Proof.
intros a b k.
unfold convol_mul.
rewrite sigma_rtl.
apply sigma_compat; intros i Hi.
rewrite Nat.add_0_r.
rewrite Nat_sub_sub_distr; [ idtac | destruct Hi; auto ].
rewrite Nat.add_comm, Nat.add_sub, fld_mul_comm; reflexivity.
Qed.

Theorem series_mul_comm : ∀ a b, (a * b = b * a)%ser.
Proof.
intros a b.
constructor; intros k.
unfold series_nth; simpl.
rewrite Nbar.add_comm.
destruct (Nbar.lt_dec (fin k) (stop b + stop a)) as [H₁| H₁].
 apply convol_mul_comm.

 reflexivity.
Qed.

Lemma stop_series_mul_0_l : ∀ s, stop (0 * s)%ser = stop s.
Proof.
intros s; simpl.
destruct (stop s); reflexivity.
Qed.

Theorem convol_mul_0_l : ∀ a i, (convol_mul F 0%ser a i = 0)%K.
Proof.
intros a k.
unfold convol_mul.
apply all_0_sigma_0; intros i Hi.
rewrite series_nth_series_0.
rewrite fld_mul_0_l; reflexivity.
Qed.

Theorem series_mul_0_l : ∀ s, (0 * s = 0)%ser.
Proof.
intros s.
constructor; intros k.
unfold series_nth.
rewrite stop_series_mul_0_l; simpl.
destruct (Nbar.lt_dec (fin k) (stop s)) as [H₁| H₁].
 rewrite convol_mul_0_l.
 destruct (Nbar.lt_dec (fin k) 0); reflexivity.

 destruct (Nbar.lt_dec (fin k) 0); reflexivity.
Qed.

Lemma sigma_aux_mul_swap : ∀ a f b len,
  (sigma_aux F b len (λ i, a * f i) = a * sigma_aux F b len f)%K.
Proof.
intros a f b len; revert b.
induction len; intros; simpl.
 rewrite fld_mul_0_r; reflexivity.

 rewrite IHlen, fld_mul_add_distr_l.
 reflexivity.
Qed.

Lemma sigma_aux_sigma_aux_mul_swap : ∀ f g h b₁ b₂ len,
  (sigma_aux F b₁ len
     (λ i, sigma_aux F b₂ (f i) (λ j, g i * h i j))
   = sigma_aux F b₁ len
       (λ i, (g i * sigma_aux F b₂ (f i) (λ j, h i j))))%K.
Proof.
intros f g h b₁ b₂ len.
revert b₁ b₂.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen.
apply fld_add_compat_r.
apply sigma_aux_mul_swap.
Qed.

Lemma sigma_sigma_mul_swap : ∀ f g h k,
  (Σ (i = 0, k) _ Σ (j = 0, f i) _ g i * h i j
   = Σ (i = 0, k) _ g i * Σ (j = 0, f i) _ h i j)%K.
Proof.
intros f g h k.
apply sigma_aux_sigma_aux_mul_swap.
Qed.

Lemma sigma_only_one_non_0 : ∀ f b v k,
  (b ≤ v ≤ k)%nat
  → (∀ i, (b ≤ i ≤ k)%nat → (i ≠ v)%nat → (f i = 0)%K)
    → (Σ (i = b, k) _ f i = f v)%K.
Proof.
intros f b v k (Hbv, Hvk) Hi.
unfold sigma.
rewrite Nat.sub_succ_l; [ idtac | etransitivity; eassumption ].
remember (k - b)%nat as len.
replace k with (b + len)%nat in * by omega.
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
  rewrite all_0_sigma_aux_0.
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

Theorem series_mul_1_l : ∀ s, (1 * s = s)%ser.
Proof.
intros s.
constructor; intros k.
unfold series_nth; simpl.
remember (stop s) as st eqn:Hst .
symmetry in Hst.
destruct st as [st| ].
 destruct (Nbar.lt_dec (fin k) (fin st)) as [H₁| H₁].
  destruct (Nbar.lt_dec (fin k) (fin (S st))) as [H₂| H₂].
   unfold convol_mul.
   rewrite sigma_only_one_non_0 with (v := O).
    rewrite Nat.sub_0_r.
    unfold series_nth; simpl.
    rewrite if_lt_dec_0_1, fld_mul_1_l.
    rewrite <- Hst in H₁.
    destruct (Nbar.lt_dec (fin k) (stop s)); [ idtac | contradiction ].
    reflexivity.

    split; [ reflexivity | apply Nat.le_0_l ].

    intros i Hik Hi.
    unfold series_nth at 1; simpl.
    destruct (Nbar.lt_dec (fin i) 1) as [H₃| H₃].
     apply Nbar.fin_lt_mono in H₃.
     apply Nat.lt_1_r in H₃; contradiction.

     apply fld_mul_0_l.

   exfalso; apply H₂.
   eapply Nbar.lt_trans; [ eassumption | idtac ].
   apply Nbar.lt_fin, Nat.lt_succ_r; reflexivity.

  destruct (Nbar.lt_dec (fin k) (fin (S st))) as [H₂| H₂].
   unfold convol_mul.
   apply all_0_sigma_0; intros i Hi.
   unfold series_nth; simpl.
   destruct (Nbar.lt_dec (fin i) 1) as [H₃| H₃].
    destruct (Nbar.lt_dec (fin (k - i)) (stop s)) as [H₄| H₄].
     apply Nbar.fin_lt_mono in H₃.
     apply Nat.lt_1_r in H₃.
     rewrite Hst in H₄.
     subst i; rewrite Nat.sub_0_r in H₄; contradiction.

     rewrite fld_mul_0_r; reflexivity.

    rewrite fld_mul_0_l; reflexivity.

   reflexivity.

 do 2 rewrite if_lt_dec_fin_inf.
 unfold convol_mul; simpl.
 rewrite sigma_only_one_non_0 with (v := O).
  rewrite Nat.sub_0_r.
  unfold series_nth; simpl.
  rewrite if_lt_dec_0_1, fld_mul_1_l.
  rewrite Hst, if_lt_dec_fin_inf.
  reflexivity.

  split; [ reflexivity | apply Nat.le_0_l ].

  intros i Hik Hi.
  unfold series_nth at 1; simpl.
  destruct (Nbar.lt_dec (fin i) 1) as [H₃| H₃].
   apply Nbar.fin_lt_mono in H₃.
   apply Nat.lt_1_r in H₃; contradiction.

   apply fld_mul_0_l.
Qed.

Theorem series_mul_1_r : ∀ s, (s * 1 = s)%ser.
Proof.
intros s.
rewrite series_mul_comm.
apply series_mul_1_l.
Qed.

Definition convol_mul_inf a b k :=
  (Σ (i = 0, k) _ terms a i * terms b (k - i))%K.

Definition series_mul_inf a b :=
  {| terms k := convol_mul_inf a b k; stop := ∞ |}.

Lemma series_mul_mul_inf : ∀ a b,
  (a * b = series_mul_inf (series_inf F a) (series_inf F b))%ser.
Proof.
intros a b.
constructor; intros k.
unfold series_nth; simpl.
rewrite if_lt_dec_fin_inf.
destruct (Nbar.lt_dec (fin k) (stop a + stop b)) as [H₁| H₁].
 unfold convol_mul, convol_mul_inf.
 apply sigma_compat; intros i Hi.
 reflexivity.

 unfold convol_mul_inf.
 symmetry; unfold convol_mul_inf; simpl.
 apply all_0_sigma_0; intros i Hi.
 unfold series_nth.
 destruct (Nbar.lt_dec (fin i) (stop a)) as [H₂| H₂].
  destruct (Nbar.lt_dec (fin (k - i)) (stop b)) as [H₃| H₃].
   exfalso; apply H₁.
   replace k with (i + (k - i))%nat by omega.
   rewrite Nbar.fin_inj_add.
   remember (stop a) as st eqn:Hst .
   symmetry in Hst.
   destruct st as [st| ].
    apply Nbar.add_lt_mono; auto.
     intros H; discriminate H.

     intros H; discriminate H.

    constructor.

   rewrite fld_mul_0_r; reflexivity.

  destruct (Nbar.lt_dec (fin (k - i)) (stop b)) as [H₃| H₃].
   rewrite fld_mul_0_l; reflexivity.

   rewrite fld_mul_0_l; reflexivity.
Qed.

Lemma series_nth_mul_inf : ∀ a b i,
  (series_nth F i (series_mul_inf a b)
   = terms (series_mul_inf a b) i)%K.
Proof.
intros a b i.
unfold series_nth; simpl.
rewrite if_lt_dec_fin_inf.
reflexivity.
Qed.

Lemma sigma_sigma_shift : ∀ f k,
  (Σ (i = 0, k) _ Σ (j = i, k) _ f i j =
   Σ (i = 0, k) _ Σ (j = 0, k - i) _ f i (i + j)%nat)%K.
Proof.
intros f k.
apply sigma_compat; intros i Hi.
unfold sigma.
rewrite Nat.sub_0_r.
rewrite Nat.sub_succ_l; [ idtac | destruct Hi; assumption ].
apply sigma_aux_compat; intros j Hj.
rewrite Nat.add_0_l; reflexivity.
Qed.

Lemma sigma_only_one : ∀ f n, (Σ (i = n, n) _ f i = f n)%K.
Proof.
intros f n.
unfold sigma.
rewrite Nat.sub_succ_l; [ idtac | reflexivity ].
rewrite Nat.sub_diag; simpl.
rewrite fld_add_0_r; reflexivity.
Qed.

Lemma sigma_succ : ∀ f b k,
  (b ≤ S k)%nat
  → (Σ (i = b, S k) _ f i = Σ (i = b, k) _ f i + f (S k))%K.
Proof.
intros f b k Hbk.
unfold sigma.
rewrite Nat.sub_succ_l; [ idtac | assumption ].
rewrite sigma_aux_succ.
rewrite Nat.add_sub_assoc; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub.
reflexivity.
Qed.

Lemma sigma_aux_succ_fst : ∀ f b len,
  (sigma_aux F b (S len) f = f b + sigma_aux F (S b) len f)%K.
Proof. reflexivity. Qed.

Lemma sigma_split_first : ∀ f b k,
  b ≤ k
  → (Σ (i = b, k) _ f i = f b + Σ (i = S b, k) _ f i)%K.
Proof.
intros f b k Hbk.
unfold sigma.
rewrite Nat.sub_succ.
rewrite <- sigma_aux_succ_fst.
rewrite <- Nat.sub_succ_l; [ reflexivity | assumption ].
Qed.

Lemma sigma_add_distr : ∀ f g b k,
  (Σ (i = b, k) _ (f i + g i) =
   Σ (i = b, k) _ f i + Σ (i = b, k) _ g i)%K.
Proof.
intros f g b k.
destruct (le_dec b k) as [Hbk| Hbk].
 revert b Hbk.
 induction k; intros.
  destruct b.
   do 3 rewrite sigma_only_one; reflexivity.

   unfold sigma; simpl; rewrite fld_add_0_r; reflexivity.

  rewrite sigma_succ; [ idtac | assumption ].
  rewrite sigma_succ; [ idtac | assumption ].
  rewrite sigma_succ; [ idtac | assumption ].
  destruct (eq_nat_dec b (S k)) as [H₂| H₂].
   subst b.
   unfold sigma; simpl.
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

 unfold sigma.
 apply Nat.nle_gt in Hbk.
 replace (S k - b)%nat with O by omega; simpl.
 rewrite fld_add_0_r; reflexivity.
Qed.

Lemma sigma_sigma_exch : ∀ f k,
  (Σ (j = 0, k) _ Σ (i = 0, j) _ f i j =
   Σ (i = 0, k) _ Σ (j = i, k) _ f i j)%K.
Proof.
intros f k.
induction k; [ reflexivity | idtac ].
rewrite sigma_succ; [ idtac | apply Nat.le_0_l ].
rewrite sigma_succ; [ idtac | apply Nat.le_0_l ].
rewrite sigma_succ; [ idtac | apply Nat.le_0_l ].
rewrite IHk.
rewrite sigma_only_one.
rewrite fld_add_assoc.
apply fld_add_compat_r.
rewrite <- sigma_add_distr.
apply sigma_compat; intros i (_, Hi).
rewrite sigma_succ; [ reflexivity | idtac ].
apply Nat.le_le_succ_r; assumption.
Qed.

Theorem series_mul_assoc : ∀ a b c, (a * (b * c) = (a * b) * c)%ser.
Proof.
intros a b c.
pose proof (series_mul_mul_inf b c) as H.
rewrite H; clear H.
pose proof (series_mul_mul_inf a b) as H.
rewrite H; clear H.
rewrite series_mul_mul_inf; symmetry.
rewrite series_mul_mul_inf; symmetry.
remember (series_inf F a) as aa eqn:Haa .
remember (series_inf F b) as bb eqn:Hbb .
remember (series_inf F c) as cc eqn:Hcc .
constructor; intros k.
do 2 rewrite series_nth_mul_inf; simpl.
unfold convol_mul_inf; simpl.
remember (λ i, (terms aa i * terms (series_mul_inf bb cc) (k - i))%K) as f.
rewrite sigma_compat with (g := f); subst f.
 symmetry.
 remember (λ i, (terms (series_mul_inf aa bb) i * terms cc (k - i))%K) as f.
 rewrite sigma_compat with (g := f); subst f.
  symmetry.
  unfold series_mul_inf; simpl.
  unfold convol_mul_inf.
  symmetry.
  rewrite sigma_mul_comm.
  rewrite <- sigma_sigma_mul_swap.
  rewrite <- sigma_sigma_mul_swap.
  rewrite sigma_sigma_exch.
  rewrite sigma_sigma_shift.
  apply sigma_compat; intros i Hi.
  apply sigma_compat; intros j Hj.
  rewrite fld_mul_comm, fld_mul_assoc.
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite Nat.add_comm, Nat.sub_add_distr.
  reflexivity.

  intros i Hi; rewrite series_nth_mul_inf; reflexivity.

 intros i Hi; rewrite series_nth_mul_inf; reflexivity.
Qed.

Lemma sigma_aux_add : ∀ f g b len,
  (sigma_aux F b len f + sigma_aux F b len g =
   sigma_aux F b len (λ i, f i + g i))%K.
Proof.
intros f g b len.
revert b.
induction len; intros; simpl; [ apply fld_add_0_l | idtac ].
rewrite fld_add_shuffle0.
do 3 rewrite <- fld_add_assoc.
do 2 apply fld_add_compat_l.
rewrite fld_add_comm.
apply IHlen.
Qed.

Lemma sigma_add : ∀ f g b e,
  (Σ (i = b, e) _ f i + Σ (i = b, e) _ g i = Σ (i = b, e) _ (f i + g i))%K.
Proof.
intros f g b e.
apply sigma_aux_add.
Qed.

Notation "s [ i ]" := (series_nth F i s) (at level 1).
Notation "a + b" := (series_add F a b) : series_scope.

Lemma series_nth_add : ∀ a b i, (((a + b)%ser) [i] = a [i] + b [i])%K.
Proof.
intros a b i.
unfold series_nth; simpl.
destruct (Nbar.lt_dec (fin i) (Nbar.max (stop a) (stop b))) as [H₁| H₁].
 reflexivity.

 destruct (Nbar.lt_dec (fin i) (stop a)) as [H₂| H₂].
  exfalso; apply H₁.
  apply Nbar.max_lt_iff; left; assumption.

  destruct (Nbar.lt_dec (fin i) (stop b)) as [H₃| H₃].
   exfalso; apply H₁.
   apply Nbar.max_lt_iff; right; assumption.

   rewrite fld_add_0_l; reflexivity.
Qed.

Lemma convol_mul_add_distr_l : ∀ a b c i,
  (convol_mul F a (b + c)%ser i = convol_mul F a b i + convol_mul F a c i)%K.
Proof.
intros a b c k.
unfold convol_mul.
rewrite sigma_add.
apply sigma_compat; intros i Hi.
rewrite series_nth_add.
rewrite fld_mul_add_distr_l.
reflexivity.
Qed.

Lemma add_le_convol_mul_is_0 : ∀ a b i,
  (stop a + stop b ≤ fin i)%Nbar → (convol_mul F a b i = 0)%K.
Proof.
intros a b k Habk.
unfold convol_mul.
apply all_0_sigma_0; intros i Hi.
unfold series_nth.
destruct (Nbar.lt_dec (fin i) (stop a)) as [H₂| H₂].
 destruct (Nbar.lt_dec (fin (k - i)) (stop b)) as [H₃| H₃].
  rewrite Nbar.fin_inj_sub in H₃.
  apply Nbar.lt_sub_lt_add_r in H₃; [ idtac | intros H; discriminate H ].
  apply Nbar.nlt_ge in Habk.
  exfalso; apply Habk.
  remember (stop b) as stb eqn:Hstb .
  symmetry in Hstb.
  destruct stb as [stb| ].
   eapply Nbar.lt_trans; [ eassumption | idtac ].
   rewrite Nbar.add_comm.
   apply Nbar.add_lt_mono_r; [ idtac | assumption ].
   intros H; discriminate H.

   rewrite Nbar.add_comm; constructor.

  rewrite fld_mul_0_r; reflexivity.

 rewrite fld_mul_0_l; reflexivity.
Qed.

Theorem series_mul_add_distr_l : ∀ a b c, (a * (b + c) = a * b + a * c)%ser.
Proof.
intros a b c.
constructor; intros k.
unfold series_nth; simpl.
remember (stop a + Nbar.max (stop b) (stop c))%Nbar as x.
destruct (Nbar.lt_dec (fin k) x) as [H₁| H₁]; subst x.
 rewrite convol_mul_add_distr_l.
 remember (Nbar.max (stop a + stop b) (stop a + stop c)) as x.
 destruct (Nbar.lt_dec (fin k) x) as [H₂| H₂]; subst x.
  unfold series_nth; simpl.
  destruct (Nbar.lt_dec (fin k) (stop a + stop b)) as [H₃| H₃].
   apply fld_add_compat_l.
   destruct (Nbar.lt_dec (fin k) (stop a + stop c)) as [H₄| H₄].
    reflexivity.

    apply add_le_convol_mul_is_0, Nbar.nlt_ge; assumption.

   destruct (Nbar.lt_dec (fin k) (stop a + stop c)) as [H₄| H₄].
    apply fld_add_compat_r.
    apply add_le_convol_mul_is_0, Nbar.nlt_ge; assumption.

    apply Nbar.max_lt_iff in H₂.
    destruct H₂; contradiction.

  rewrite Nbar.add_max_distr_l in H₂.
  contradiction.

 remember (Nbar.max (stop a + stop b) (stop a + stop c)) as x.
 destruct (Nbar.lt_dec (fin k) x) as [H₂| H₂]; subst x.
  rewrite Nbar.add_max_distr_l in H₂.
  contradiction.

  reflexivity.
Qed.

End misc_lemmas.

Add Parametric Morphism : series_add
  with  signature eq_series ==> eq_series ==> eq_series
  as series_add_morph.
Proof.
intros s₁ s₂ Heq₁ s₃ s₄ Heq₂.
inversion Heq₁; subst.
inversion Heq₂; subst.
constructor; simpl.
intros i.
unfold series_nth; simpl.
unfold series_nth in H; simpl in H.
unfold series_nth in H0; simpl in H0.
pose proof (H i) as Hi₁.
pose proof (H0 i) as Hi₂.
clear H H0.
unfold series_nth.
remember (Nbar.lt_dec (fin i) (stop s₁)) as lt₁.
remember (Nbar.lt_dec (fin i) (stop s₂)) as lt₂.
remember (Nbar.lt_dec (fin i) (stop s₃)) as lt₃.
remember (Nbar.lt_dec (fin i) (stop s₄)) as lt₄.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₃))) as lt₅.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₄))) as lt₆.
clear Heqlt₁ Heqlt₂ Heqlt₃ Heqlt₄ Heqlt₅ Heqlt₆.
move Hi₁ at bottom.
move Hi₂ at bottom.
destruct lt₅ as [Hlt₅| Hge₅].
 rewrite Hi₁, Hi₂.
 destruct lt₆ as [Hlt₆| Hge₆]; [ reflexivity | idtac ].
 destruct lt₂ as [Hlt₂| Hge₂].
  exfalso; apply Hge₆; clear Hge₆.
  apply Nbar.max_lt_iff; left; assumption.

  destruct lt₄ as [Hlt₄| Hge₄].
   exfalso; apply Hge₆; clear Hge₆.
   apply Nbar.max_lt_iff; right; assumption.

   rewrite fld_add_0_l; reflexivity.

 destruct lt₁ as [Hlt₁| Hge₁].
  exfalso; apply Hge₅; clear Hge₅.
  apply Nbar.max_lt_iff; left; assumption.

  destruct lt₃ as [Hlt₃| Hge₃].
   exfalso; apply Hge₅; clear Hge₅.
   apply Nbar.max_lt_iff; right; assumption.

   destruct lt₆ as [Hlt₆| Hge₆]; [ idtac | reflexivity ].
   rewrite <- Hi₁, <- Hi₂.
   rewrite fld_add_0_l; reflexivity.
Qed.

Add Parametric Morphism : (series_nth rng)
with signature eq ==> eq_series ==> (fld_eq rng)
as series_nth_morph.
Proof.
intros s₁ s₂ i Heq.
inversion Heq; subst.
apply H.
Qed.

Theorem series_add_compat_l : ∀ a b c, (a = b)%ser → (c + a = c + b)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_compat_l : ∀ a b c, (a = b)%ser → (c * a = c * b)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_compat_r : ∀ a b c, (a = b)%ser → (a * c = b * c)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_add_distr_r : ∀ a b c, ((a + b) * c = a * c + b * c)%ser.
Proof.
intros a b c.
rewrite series_mul_comm, series_mul_add_distr_l.
rewrite series_mul_comm.
apply series_add_compat_l.
apply series_mul_comm.
Qed.

Theorem series_neq_1_0 : (1 ≠ 0)%ser.
Proof.
intros H.
inversion_clear H.
pose proof (H0 O) as H.
rewrite series_nth_series_0 in H.
unfold series_nth in H.
simpl in H.
rewrite if_lt_dec_0_1 in H.
revert H; apply fld_neq_1_0.
Qed.

Definition series_ring : fld_r (power_series α) :=
  {| fld_zero := series_0;
     fld_one := series_1;
     fld_add := series_add;
     fld_mul := series_mul;
     fld_opp := series_opp;
     fld_eq := eq_series;
     fld_eq_refl := eq_series_refl;
     fld_eq_sym := eq_series_sym;
     fld_eq_trans := eq_series_trans;
     fld_neq_1_0 := series_neq_1_0;
     fld_add_comm := series_add_comm;
     fld_add_assoc := series_add_assoc;
     fld_add_0_l := series_add_0_l;
     fld_add_opp_l := series_add_opp_l;
     fld_add_compat_l := series_add_compat_l;
     fld_mul_comm := series_mul_comm;
     fld_mul_assoc := series_mul_assoc;
     fld_mul_1_l := series_mul_1_l;
     fld_mul_compat_l := series_mul_compat_l;
     fld_mul_add_distr_l := series_mul_add_distr_l |}.

Fixpoint term_inv c s n :=
  if zerop n then fld_inv fld s[0]
  else
    match c with
    | O => 0%K
    | S c₁ =>
        (- fld_inv fld s[0] *
         Σ (i = 1, n) _ s[i] * term_inv c₁ s (n - i)%nat)%K
    end.

Definition series_inv s :=
  {| terms i := term_inv (S i) s i;
     stop := ∞ |}.

Notation "¹/ a" := (series_inv a) (at level 99) : series_scope.

Lemma inv_nth_0 : ∀ a, ((¹/a [0])%fld = (¹/a)%ser [0])%K.
Proof.
intros a.
unfold series_nth; simpl.
unfold series_nth; simpl.
rewrite if_lt_dec_fin_inf.
reflexivity.
Qed.

Lemma term_inv_iter_enough : ∀ a i j k,
  k ≤ i → k ≤ j → (term_inv i a k = term_inv j a k)%K.
Proof.
intros a i j k Hki Hkj.
revert j k Hki Hkj.
induction i; intros.
 apply Nat.le_0_r in Hki; subst k.
 destruct j; reflexivity.

 simpl.
 destruct k; simpl.
  destruct j; reflexivity.

  destruct j.
   apply Nat.nle_succ_0 in Hkj; contradiction.

   simpl.
   apply fld_mul_compat_l.
   apply sigma_compat; intros l (Hl, Hlj).
   apply fld_mul_compat_l.
   destruct l.
    apply Nat.nle_gt in Hl.
    exfalso; apply Hl; reflexivity.

    apply IHi; omega.
Qed.

Lemma term_inv_nth_gen_formula : ∀ k a a' i,
  (a[0] ≠ 0)%K
  → a' = series_inv a
    → (S k - i ≠ 0)%nat
      → (a' [S k - i] =
         - a' [0] *
         Σ (j = 1, S k - i)_ a [j] * term_inv (S k) a (S k - i - j))%K.
Proof.
(* à revoir... *)
intros k a a' i Ha Ha' Hki.
rewrite Ha'.
rewrite <- inv_nth_0.
unfold series_nth.
remember minus as f; simpl; subst f.
rewrite if_lt_dec_fin_inf.
destruct (zerop (S k - i)) as [| H₁]; [ contradiction | idtac ].
remember (S k - i)%nat as ki eqn:Hki₂ .
destruct ki.
 exfalso; apply Hki; reflexivity.

 clear H₁.
 apply fld_mul_compat_l.
 apply sigma_compat; intros j Hj.
 apply fld_mul_compat_l.
 remember minus as f; simpl; subst f.
 destruct (zerop (S ki - j)) as [H₁| H₁].
  reflexivity.

  apply fld_mul_compat_l.
  apply sigma_compat; intros l Hl.
  apply fld_mul_compat_l.
  apply term_inv_iter_enough; [ fast_omega Hl | idtac ].
  rewrite Hki₂.
  destruct Hl as (H, _).
  apply Nat.nle_gt in H.
  destruct l; [ exfalso; apply H, Nat.le_0_l | idtac ].
  do 2 rewrite <- Nat.sub_add_distr.
  do 2 rewrite Nat.add_succ_r.
  rewrite Nat.sub_succ.
  apply Nat.le_sub_l.
Qed.

Lemma term_inv_nth_formula : ∀ k a a',
  (a[0] ≠ 0)%K
  → a' = series_inv a
    → (a' [S k] = - a' [0] * Σ (i = 1, S k)_ a [i] * a' [S k - i])%K.
Proof.
intros k a a' Ha Ha'.
pose proof (term_inv_nth_gen_formula k O Ha Ha') as H.
rewrite Nat.sub_0_r in H.
rewrite H; [ idtac | intros HH; discriminate HH ].
apply fld_mul_compat_l.
apply sigma_compat; intros i Hi.
apply fld_mul_compat_l.
rewrite Ha'.
unfold series_nth.
remember minus as f; simpl; subst f.
rewrite if_lt_dec_fin_inf.
destruct (zerop (S k - i)) as [H₂| H₂].
 reflexivity.

 apply fld_mul_compat_l.
 apply sigma_compat; intros j Hj.
 apply fld_mul_compat_l.
 apply term_inv_iter_enough; fast_omega Hj.
Qed.

Lemma convol_mul_inv_r : ∀ k a a',
  (a[0] ≠ 0)%K
  → a' = series_inv a
    → (convol_mul a a' (S k) = 0)%K.
Proof.
intros k a a' Ha Ha'.
unfold convol_mul.
pose proof (term_inv_nth_formula k Ha Ha') as Hi.
apply fld_mul_compat_l with (c := a [0]%K) in Hi.
symmetry in Hi.
rewrite fld_mul_assoc in Hi.
rewrite fld_mul_opp_r in Hi.
rewrite Ha' in Hi.
rewrite <- inv_nth_0 in Hi.
rewrite fld_mul_inv_r in Hi; auto.
rewrite fld_mul_opp_l, fld_mul_1_l in Hi.
rewrite <- Ha' in Hi.
eapply fld_add_compat_r in Hi.
rewrite fld_add_opp_l in Hi.
symmetry in Hi.
rewrite sigma_split_first; [ idtac | apply Nat.le_0_l ].
rewrite Nat.sub_0_r; auto.
Qed.

Theorem series_mul_inv_r : ∀ a, (a [0] ≠ 0)%K → (a * series_inv a = 1)%ser.
Proof.
intros a Ha.
constructor; intros i.
unfold series_nth; simpl.
rewrite Nbar.add_comm; simpl.
rewrite if_lt_dec_fin_inf.
destruct (Nbar.lt_dec (fin i) 1) as [H₂| H₂].
 apply Nbar.fin_lt_mono in H₂.
 apply Nat.lt_1_r in H₂; subst i.
 unfold convol_mul; simpl.
 rewrite sigma_only_one.
 unfold series_nth; simpl.
 rewrite if_lt_dec_fin_inf.
 destruct (Nbar.lt_dec 0 (stop a)) as [H₂| H₂].
  unfold series_nth; simpl.
  unfold series_nth in Ha.
  destruct (Nbar.lt_dec 0 (stop a)) as [H₃| H₃].
   rewrite fld_mul_inv_r; [ reflexivity | assumption ].

   exfalso; apply Ha; reflexivity.

  exfalso; apply Ha.
  unfold series_nth; simpl.
  destruct (Nbar.lt_dec 0 (stop a)) as [H₃| H₃].
   contradiction.

   reflexivity.

 destruct i; [ exfalso; apply H₂, Nbar.lt_0_1 | idtac ].
 apply convol_mul_inv_r; [ assumption | reflexivity ].
Qed.

Theorem series_mul_inv_l : ∀ a, (a [0] ≠ 0)%K → (series_inv a * a = 1)%ser.
Proof.
intros a Ha.
rewrite series_mul_comm.
apply series_mul_inv_r.
assumption.
Qed.

End M.
