(* Power_series.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Nbar.
Require Import Misc.

Set Implicit Arguments.

Record power_series α := { terms : nat → α }.

Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%nat (at level 70, y at next level).
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat (at level 70, y at next level).

Delimit Scope series_scope with ser.

Notation "s .[ i ]" := (terms s i) (at level 1).

Definition series_0 α (f : field α) :=
  {| terms i := .0 f%F |}.

Definition series_const α (f : field α) c :=
  {| terms i := if zerop i then c else .0 f%F |}.
Definition series_1 α (f : field α) :=
  series_const f (.1 f%F).

Notation ".0 f" := (series_0 f) : series_scope.
Notation ".1 f" := (series_1 f) : series_scope.

Inductive eq_series α (f : field α) :
    power_series α → power_series α → Prop :=
  eq_series_base : ∀ s₁ s₂,
    (∀ i, (s₁ .[i] .= f s₂ .[i])%F)
    → eq_series f s₁ s₂.

Notation "a .= f b" := (eq_series f a b) : series_scope.
Notation "a .≠ f b" := (¬ eq_series f a b) : series_scope.

Theorem eq_series_refl α (f : field α) : reflexive _ (eq_series f).
Proof.
intros s.
constructor; reflexivity.
Qed.

Theorem eq_series_sym α (f : field α) : symmetric _ (eq_series f).
Proof.
intros s₁ s₂ H.
inversion H; subst.
constructor.
intros i; symmetry; apply H0.
Qed.

Theorem eq_series_trans α (f : field α) : transitive _ (eq_series f).
Proof.
intros s₁ s₂ s₃ H₁ H₂.
inversion H₁; inversion H₂; subst.
constructor.
etransitivity; [ apply H | apply H2 ].
Qed.

Add Parametric Relation α (f : field α) : (power_series α) (eq_series f)
 reflexivity proved by (eq_series_refl f)
 symmetry proved by (eq_series_sym (f := f))
 transitivity proved by (eq_series_trans (f := f))
 as eq_series_rel.

(* *)

Lemma fold_series_const : ∀ α (f : field α) c,
  {| terms := λ i, if zerop i then c else .0 f%F |} =
  series_const f c.
Proof. reflexivity. Qed.

(* series_add *)

Definition series_add α (f : field α) s₁ s₂ :=
  {| terms i := (s₁ .[i] .+ f s₂ .[i])%F |}.

Definition series_opp α (f : field α) s :=
  {| terms i := (.- f terms s i)%F |}.

Notation "a .+ f b" := (series_add f a b) : series_scope.
Notation "a .- f b" := (series_add f a (series_opp f b)) : series_scope.
Notation ".- f a" := (series_opp f a) : series_scope.

Section theorems_add.

Variable α : Type.
Variable f : field α.

Theorem series_add_comm : ∀ s₁ s₂, (s₁ .+ f s₂ .= f s₂ .+ f s₁)%ser.
Proof.
intros s₁ s₂.
constructor; intros i; simpl.
rewrite fld_add_comm; reflexivity.
Qed.

Theorem series_add_assoc : ∀ s₁ s₂ s₃,
  (s₁ .+ f (s₂ .+ f s₃) .= f (s₁ .+ f s₂) .+ f s₃)%ser.
Proof.
intros s₁ s₂ s₃.
unfold series_add; simpl.
constructor; intros i; simpl.
rewrite fld_add_assoc; reflexivity.
Qed.

Lemma series_nth_series_0 : ∀ i, (.0 f%ser .[i] = .0 f)%F.
Proof. reflexivity. Qed.

Theorem series_add_0_l : ∀ s, (.0 f .+ f s .= f s)%ser.
Proof.
intros s.
constructor; intros i; simpl.
rewrite fld_add_0_l; reflexivity.
Qed.

Theorem series_add_opp_r : ∀ s, (s .- f s .= f .0 f)%ser.
Proof.
intros s.
constructor; intros i; simpl.
apply fld_add_opp_r.
Qed.

Theorem series_add_opp_l : ∀ s, (.- f s .+ f s .= f .0 f)%ser.
Proof.
intros s.
rewrite series_add_comm.
apply series_add_opp_r.
Qed.

End theorems_add.

(* series_mul *)

Fixpoint sigma_aux α (f : field α) b len g :=
  match len with
  | O => .0 f%F
  | S len₁ => (g b .+ f sigma_aux f (S b) len₁ g)%F
  end.

Definition sigma α (f : field α) b e g := sigma_aux f b (S e - b) g.
Notation "'Σ' f ( i = b , e ) '_' g" := (sigma f b e (λ i, (g)%F))
  (at level 0, f at level 0, i at level 0, b at level 60, e at level 60,
   g at level 40).

Definition convol_mul α (f : field α) a b k :=
  Σ f (i = 0, k) _ a .[i] .* f b .[k-i].

Definition series_mul α (f : field α) a b :=
  {| terms k := convol_mul f a b k |}.

Notation "a .* f b" := (series_mul f a b) : series_scope.

Section theorems_mul.

Variable α : Type.
Variable f : field α.

Lemma sigma_aux_compat : ∀ g h b₁ b₂ len,
  (∀ i, 0 ≤ i < len → (g (b₁ + i)%nat .= f h (b₂ + i)%nat)%F)
  → (sigma_aux f b₁ len g .= f sigma_aux f b₂ len h)%F.
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

Lemma sigma_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i .= f h i)%F)
  → (Σ f (i = b, k)_ g i .= f Σ f (i = b, k) _ h i)%F.
Proof.
intros g h b k Hgh.
apply sigma_aux_compat.
intros i (_, Hi).
apply Hgh.
split; [ apply Nat.le_add_r | omega ].
Qed.

Lemma sigma_mul_comm : ∀ g h b k,
  (Σ f (i = b, k) _ g i .* f h i
   .= f Σ f (i = b, k) _ h i .* f g i)%F.
Proof.
intros g h b len.
apply sigma_compat; intros i Hi.
apply fld_mul_comm.
Qed.

Lemma all_0_sigma_aux_0 : ∀ g b len,
  (∀ i, (b ≤ i < b + len)%nat → (g i .= f .0 f)%F)
  → (sigma_aux f b len (λ i, g i) .= f .0 f)%F.
Proof.
intros g b len H.
revert b H.
induction len; intros; [ reflexivity | simpl ].
rewrite H; [ idtac | omega ].
rewrite fld_add_0_l, IHlen; [ reflexivity | idtac ].
intros i Hi; apply H; omega.
Qed.

Lemma all_0_sigma_0 : ∀ g i₁ i₂,
  (∀ i, i₁ ≤ i ≤ i₂ → (g i .= f .0 f)%F)
  → (Σ f (i = i₁, i₂) _ g i .= f .0 f)%F.
Proof.
intros g i₁ i₂ H.
apply all_0_sigma_aux_0.
intros i (H₁, H₂).
apply H.
split; [ assumption | omega ].
Qed.

End theorems_mul.

Add Parametric Morphism α (F : field α) : (series_mul F)
  with signature eq_series F ==> eq_series F ==> eq_series F
  as series_mul_morph.
Proof.
intros a b Hab c d Hcd.
constructor; intros k; simpl.
unfold convol_mul.
apply sigma_compat; intros i Hi.
inversion Hab; subst.
inversion Hcd; subst.
rewrite H, H0; reflexivity.
Qed.

Section misc_lemmas.

Variable α : Type.
Variable f : field α.

Lemma sigma_aux_succ : ∀ g b len,
  (sigma_aux f b (S len) g .= f sigma_aux f b len g .+ f g (b + len)%nat)%F.
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

Lemma sigma_aux_rtl : ∀ g b len,
  (sigma_aux f b len g .= f
   sigma_aux f b len (λ i, g (b + len - 1 + b - i)%nat))%F.
Proof.
(* supprimer ce putain de omega trop lent *)
intros g b len.
revert g b.
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

Lemma sigma_rtl : ∀ g b k,
  (Σ f (i = b, k) _ g i .= f Σ f (i = b, k) _ g (k + b - i)%nat)%F.
Proof.
(* supprimer ce putain de omega trop lent *)
intros g b k.
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
  (convol_mul f a b i .= f convol_mul f b a i)%F.
Proof.
intros a b k.
unfold convol_mul.
rewrite sigma_rtl.
apply sigma_compat; intros i Hi.
rewrite Nat.add_0_r.
rewrite Nat_sub_sub_distr; [ idtac | destruct Hi; auto ].
rewrite Nat.add_comm, Nat.add_sub, fld_mul_comm; reflexivity.
Qed.

Theorem series_mul_comm : ∀ a b, (a .* f b .= f b .* f a)%ser.
Proof.
intros a b.
constructor; intros k; simpl.
apply convol_mul_comm.
Qed.

Theorem convol_mul_0_l : ∀ a i, (convol_mul f .0 f%ser a i .= f .0 f)%F.
Proof.
intros a k.
unfold convol_mul.
apply all_0_sigma_0; intros i Hi.
rewrite series_nth_series_0.
rewrite fld_mul_0_l; reflexivity.
Qed.

Theorem series_mul_0_l : ∀ s, (.0 f .* f s .= f .0 f)%ser.
Proof.
intros s.
constructor; intros k.
unfold series_mul; simpl.
apply convol_mul_0_l.
Qed.

Lemma sigma_aux_mul_swap : ∀ a g b len,
  (sigma_aux f b len (λ i, a .* f g i) .= f a .* f sigma_aux f b len g)%F.
Proof.
intros a g b len; revert b.
induction len; intros; simpl.
 rewrite fld_mul_0_r; reflexivity.

 rewrite IHlen, fld_mul_add_distr_l.
 reflexivity.
Qed.

Lemma sigma_aux_sigma_aux_mul_swap : ∀ g₁ g₂ g₃ b₁ b₂ len,
  (sigma_aux f b₁ len
     (λ i, sigma_aux f b₂ (g₁ i) (λ j, g₂ i .* f g₃ i j))
   .= f sigma_aux f b₁ len
       (λ i, g₂ i .* f sigma_aux f b₂ (g₁ i) (λ j, g₃ i j)))%F.
Proof.
intros g₁ g₂ g₃ b₁ b₂ len.
revert b₁ b₂.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen.
apply fld_add_compat_r.
apply sigma_aux_mul_swap.
Qed.

Lemma sigma_sigma_mul_swap : ∀ g₁ g₂ g₃ k,
  (Σ f (i = 0, k) _ Σ f (j = 0, g₁ i) _ g₂ i .* f g₃ i j
   .= f Σ f (i = 0, k) _ g₂ i .* f Σ f (j = 0, g₁ i) _ g₃ i j)%F.
Proof.
intros g₁ g₂ g₃ k.
apply sigma_aux_sigma_aux_mul_swap.
Qed.

Lemma sigma_only_one_non_0 : ∀ g b v k,
  (b ≤ v ≤ k)%nat
  → (∀ i, (b ≤ i ≤ k)%nat → (i ≠ v)%nat → (g i .= f .0 f)%F)
    → (Σ f (i = b, k) _ g i .= f g v)%F.
Proof.
intros g b v k (Hbv, Hvk) Hi.
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

Theorem series_mul_1_l : ∀ s, (.1 f .* f s .= f s)%ser.
Proof.
intros s.
constructor; intros k; simpl.
unfold convol_mul; simpl.
rewrite sigma_only_one_non_0 with (v := O).
 rewrite Nat.sub_0_r; simpl.
 apply fld_mul_1_l.

 split; [ reflexivity | apply Nat.le_0_l ].

 intros i Hik Hi.
 destruct i; [ exfalso; apply Hi; reflexivity | simpl ].
 apply fld_mul_0_l.
Qed.

Theorem series_mul_1_r : ∀ s, (s .* f .1 f .= f s)%ser.
Proof.
intros s.
rewrite series_mul_comm.
apply series_mul_1_l.
Qed.

Lemma sigma_sigma_shift : ∀ g k,
  (Σ f (i = 0, k) _ Σ f (j = i, k) _ g i j .= f
   Σ f (i = 0, k) _ Σ f (j = 0, k - i) _ g i (i + j)%nat)%F.
Proof.
intros g k.
apply sigma_compat; intros i Hi.
unfold sigma.
rewrite Nat.sub_0_r.
rewrite Nat.sub_succ_l; [ idtac | destruct Hi; assumption ].
apply sigma_aux_compat; intros j Hj.
rewrite Nat.add_0_l; reflexivity.
Qed.

Lemma sigma_only_one : ∀ g n, (Σ f (i = n, n) _ g i .= f g n)%F.
Proof.
intros g n.
unfold sigma.
rewrite Nat.sub_succ_l; [ idtac | reflexivity ].
rewrite Nat.sub_diag; simpl.
rewrite fld_add_0_r; reflexivity.
Qed.

Lemma sigma_succ : ∀ g b k,
  (b ≤ S k)%nat
  → (Σ f (i = b, S k) _ g i .= f Σ f (i = b, k) _ g i .+ f g (S k))%F.
Proof.
intros g b k Hbk.
unfold sigma.
rewrite Nat.sub_succ_l; [ idtac | assumption ].
rewrite sigma_aux_succ.
rewrite Nat.add_sub_assoc; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub.
reflexivity.
Qed.

Lemma sigma_aux_succ_fst : ∀ g b len,
  (sigma_aux f b (S len) g .= f g b .+ f sigma_aux f (S b) len g)%F.
Proof. reflexivity. Qed.

Lemma sigma_split_first : ∀ g b k,
  b ≤ k
  → (Σ f (i = b, k) _ g i .= f g b .+ f Σ f (i = S b, k) _ g i)%F.
Proof.
intros g b k Hbk.
unfold sigma.
rewrite Nat.sub_succ.
rewrite <- sigma_aux_succ_fst.
rewrite <- Nat.sub_succ_l; [ reflexivity | assumption ].
Qed.

Lemma sigma_add_distr : ∀ g h b k,
  (Σ f (i = b, k) _ (g i .+ f h i) .= f
   Σ f (i = b, k) _ g i .+ f Σ f (i = b, k) _ h i)%F.
Proof.
intros g h b k.
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

Lemma sigma_sigma_exch : ∀ g k,
  (Σ f (j = 0, k) _ Σ f (i = 0, j) _ g i j .= f
   Σ f (i = 0, k) _ Σ f (j = i, k) _ g i j)%F.
Proof.
intros g k.
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

Theorem series_mul_assoc : ∀ a b c,
  (a .* f (b .* f c) .= f (a .* f b) .* f c)%ser.
Proof.
intros a b c.
constructor; intros k; simpl.
unfold convol_mul; simpl.
unfold convol_mul; simpl.
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
Qed.

Lemma sigma_aux_add : ∀ g h b len,
  (sigma_aux f b len g .+ f sigma_aux f b len h .= f
   sigma_aux f b len (λ i, g i .+ f h i))%F.
Proof.
intros g h b len.
revert b.
induction len; intros; simpl; [ apply fld_add_0_l | idtac ].
rewrite fld_add_shuffle0.
do 3 rewrite <- fld_add_assoc.
do 2 apply fld_add_compat_l.
rewrite fld_add_comm.
apply IHlen.
Qed.

Lemma sigma_add : ∀ g h b e,
  (Σ f (i = b, e) _ g i .+ f Σ f (i = b, e) _ h i .= f
   Σ f (i = b, e) _ (g i .+ f h i))%F.
Proof.
intros g h b e.
apply sigma_aux_add.
Qed.

Lemma series_nth_add : ∀ a b i,
  (((a .+ f b)%ser) .[i] .= f a .[i] .+ f b .[i])%F.
Proof. reflexivity. Qed.

Lemma convol_mul_add_distr_l : ∀ a b c i,
  (convol_mul f a (b .+ f c)%ser i .= f
   convol_mul f a b i .+ f convol_mul f a c i)%F.
Proof.
intros a b c k.
unfold convol_mul.
rewrite sigma_add.
apply sigma_compat; intros i Hi.
rewrite series_nth_add.
rewrite fld_mul_add_distr_l.
reflexivity.
Qed.

Theorem series_mul_add_distr_l : ∀ a b c,
  (a .* f (b .+ f c) .= f a .* f b .+ f a .* f c)%ser.
Proof.
intros a b c.
constructor; intros k; simpl.
apply convol_mul_add_distr_l.
Qed.

End misc_lemmas.

Add Parametric Morphism α (F : field α) : (series_add F)
  with signature eq_series F ==> eq_series F ==> eq_series F
  as series_add_morph.
Proof.
intros s₁ s₂ Heq₁ s₃ s₄ Heq₂.
inversion Heq₁; subst.
inversion Heq₂; subst.
constructor; intros i; simpl.
rewrite H, H0; reflexivity.
Qed.

Add Parametric Morphism α (F : field α) : (@terms α)
  with signature eq_series F ==> eq ==> (fld_eq F)
  as series_nth_morph.
Proof.
intros s₁ s₂ Heq i.
inversion Heq; subst.
apply H.
Qed.

Section other_lemmas.

Variable α : Type.
Variable f : field α.

Theorem series_add_compat_l : ∀ a b c,
  (a .= f b)%ser
  → (c .+ f a .= f c .+ f b)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_compat_l : ∀ a b c,
  (a .= f b)%ser
  → (c .* f a .= f c .* f b)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_compat_r : ∀ a b c,
  (a .= f b)%ser
  → (a .* f c .= f b .* f c)%ser.
Proof.
intros a b c Hab.
rewrite Hab.
reflexivity.
Qed.

Theorem series_mul_add_distr_r : ∀ a b c,
  ((a .+ f b) .* f c .= f a .* f c .+ f b .* f c)%ser.
Proof.
intros a b c.
rewrite series_mul_comm, series_mul_add_distr_l.
rewrite series_mul_comm.
apply series_add_compat_l.
apply series_mul_comm.
Qed.

Theorem series_neq_1_0 : (.1 f .≠ f .0 f)%ser.
Proof.
intros H.
inversion_clear H.
pose proof (H0 O) as H.
rewrite series_nth_series_0 in H.
simpl in H.
revert H; apply fld_neq_1_0.
Qed.

End other_lemmas.

Fixpoint term_inv α (f : field α) c s n :=
  if zerop n then .¹/f (s .[0])%F
  else
   match c with
   | O => .0 f%F
   | S c₁ =>
       (.-f .¹/f (s .[0]) .* f
        Σ f (i = 1, n)_ s .[i] .* f term_inv f c₁ s (n - i)%nat)%F
   end.

Definition series_inv α (f : field α) s :=
  {| terms i := term_inv f (S i) s i |}.

Notation ".¹/ f a" := (series_inv f a) : series_scope.

Section lemmas_again.

Variable α : Type.
Variable f : field α.

Lemma term_inv_iter_enough : ∀ a i j k,
  k ≤ i → k ≤ j → (term_inv f i a k .= f term_inv f j a k)%F.
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
  (a.[0] .≠ f .0 f)%F
  → a' = series_inv f a
    → (S k - i ≠ 0)%nat
      → (a' .[S k - i] .= f
         .- f a' .[0] .* f
         Σ f (j = 1, S k - i) _
         a .[j] .* f term_inv f (S k) a (S k - i - j))%F.
Proof.
(* à revoir... *)
intros k a a' i Ha Ha' Hki.
rewrite Ha'.
remember minus as g; simpl; subst g.
destruct (zerop (S k - i)) as [| H₁]; [ contradiction | idtac ].
remember (S k - i)%nat as ki eqn:Hki₂ .
destruct ki.
 exfalso; apply Hki; reflexivity.

 clear H₁.
 apply fld_mul_compat_l.
 apply sigma_compat; intros j Hj.
 apply fld_mul_compat_l.
 remember minus as g; simpl; subst g.
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
  (a.[0] .≠ f .0 f)%F
  → a' = series_inv f a
    → (a' .[S k] .= f
       .- f a' .[0] .* f Σ f (i = 1, S k)_ a .[i] .* f a' .[S k - i])%F.
Proof.
intros k a a' Ha Ha'.
pose proof (term_inv_nth_gen_formula k O Ha Ha') as H.
rewrite Nat.sub_0_r in H.
rewrite H; [ idtac | intros HH; discriminate HH ].
apply fld_mul_compat_l.
apply sigma_compat; intros i Hi.
apply fld_mul_compat_l.
rewrite Ha'.
remember minus as g; simpl; subst g.
destruct (zerop (S k - i)) as [H₂| H₂].
 reflexivity.

 apply fld_mul_compat_l.
 apply sigma_compat; intros j Hj.
 apply fld_mul_compat_l.
 apply term_inv_iter_enough; fast_omega Hj.
Qed.

Lemma convol_mul_inv_r : ∀ k a a',
  (a.[0] .≠ f .0 f)%F
  → a' = series_inv f a
    → (convol_mul f a a' (S k) .= f .0 f)%F.
Proof.
intros k a a' Ha Ha'.
unfold convol_mul.
pose proof (term_inv_nth_formula k Ha Ha') as Hi.
apply fld_mul_compat_l with (c := a .[0]%F) in Hi.
symmetry in Hi.
rewrite fld_mul_assoc in Hi.
rewrite fld_mul_opp_r in Hi.
rewrite Ha' in Hi.
rewrite fld_mul_inv_r in Hi; auto.
rewrite fld_mul_opp_l, fld_mul_1_l in Hi.
rewrite <- Ha' in Hi.
eapply fld_add_compat_r in Hi.
rewrite fld_add_opp_l in Hi.
symmetry in Hi.
rewrite sigma_split_first; [ idtac | apply Nat.le_0_l ].
rewrite Nat.sub_0_r; auto.
Qed.

Theorem series_mul_inv_r : ∀ a,
  (a .[0] .≠ f .0 f)%F
  → (a .* f .¹/f a .= f .1 f)%ser.
Proof.
intros a Ha.
constructor; intros i; simpl.
destruct i; simpl.
 unfold convol_mul; simpl.
 rewrite sigma_only_one; simpl.
 rewrite fld_mul_inv_r; [ reflexivity | assumption ].

 apply convol_mul_inv_r; [ assumption | reflexivity ].
Qed.

Theorem series_mul_inv_l : ∀ a,
  (a .[0] .≠ f .0 f)%F
  → (.¹/f a .* f a .= f .1 f)%ser.
Proof.
intros a Ha.
rewrite series_mul_comm.
apply series_mul_inv_r.
assumption.
Qed.

End lemmas_again.
