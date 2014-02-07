(* Fpolynomial.v *)

(* polynomials on a field *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Field.
Require Import Fsummation.

Set Implicit Arguments.

Record polynomial α := mkpol { al : list α }.

Inductive list_eq α (f : field α) : list α → list α → Prop :=
  | list_eq_nil : list_eq f [] []
  | list_eq_cons : ∀ x₁ x₂ l₁ l₂,
      (x₁ .= f x₂)%K
      → list_eq f l₁ l₂
        → list_eq f [x₁ … l₁] [x₂ … l₂]
  | list_eq_cons_nil : ∀ x l,
      (x .= f .0 f)%K
      → list_eq f l []
        → list_eq f [x … l] []
  | list_eq_nil_cons : ∀ x l,
      (x .= f .0 f)%K
      → list_eq f [] l
        → list_eq f [] [x … l].

Delimit Scope poly_scope with pol.
Notation "'POL' l" := {| al := l |} (at level 1) : poly_scope.

Definition eq_poly α (f : field α) x y := list_eq f (al x) (al y).

Notation "a .= f b" := (eq_poly f a b) : poly_scope.

Definition poly_one α (f : field α) := POL [.1 f%K]%pol.
Notation ".1 f" := (poly_one f) : poly_scope.

Lemma list_eq_cons_inv : ∀ α (f : field α) x₁ x₂ l₁ l₂,
  list_eq f [x₁ … l₁] [x₂ … l₂]
  → (x₁ .= f x₂)%K ∧ list_eq f l₁ l₂.
Proof.
intros α f x₁ x₂ l₁ l₂ H.
inversion H; split; assumption.
Qed.

Lemma list_eq_cons_nil_inv : ∀ α (f : field α) x l,
  list_eq f [x … l] []
  → (x .= f .0 f)%K ∧ list_eq f l [].
Proof.
intros α f x l H.
inversion H; split; assumption.
Qed.

Lemma list_eq_nil_cons_inv : ∀ α (f : field α) x l,
  list_eq f [] [x … l]
  → (x .= f .0 f)%K ∧ list_eq f [] l.
Proof.
intros α f x l H.
inversion H; split; assumption.
Qed.

Theorem list_eq_refl α (f : field α) : reflexive _ (list_eq f).
Proof.
intros l.
induction l; constructor; [ reflexivity | assumption ].
Qed.

Theorem list_eq_sym α (f : field α) : symmetric _ (list_eq f).
Proof.
intros l₁ l₂ Heq.
revert l₂ Heq.
induction l₁ as [| x₁]; intros.
 induction l₂ as [| x₂]; constructor; apply list_eq_nil_cons_inv in Heq.
  destruct Heq; assumption.

  apply IHl₂; destruct Heq; assumption.

 induction l₂ as [| x₂].
  apply list_eq_cons_nil_inv in Heq; destruct Heq.
  constructor; [ assumption | apply IHl₁; assumption ].

  apply list_eq_cons_inv in Heq; destruct Heq.
  constructor; [ symmetry; assumption | apply IHl₁; assumption ].
Qed.

Theorem list_eq_trans α (f : field α) : transitive _ (list_eq f).
Proof.
intros l₁ l₂ l₃ H₁ H₂.
revert l₁ l₃ H₁ H₂.
induction l₂ as [| x₂]; intros.
 revert l₃ H₂.
 induction l₁ as [| x₁]; intros; [ assumption | idtac ].
 destruct l₃ as [| x₃]; [ assumption | idtac ].
 apply list_eq_cons_nil_inv in H₁.
 apply list_eq_nil_cons_inv in H₂.
 constructor.
  etransitivity; [ destruct H₁; eassumption | idtac ].
  destruct H₂; symmetry; assumption.

  apply IHl₁; [ destruct H₁ | destruct H₂ ]; assumption.

 destruct l₁ as [| x₁].
  apply list_eq_nil_cons_inv in H₁.
  destruct l₃ as [| x₃]; constructor.
   apply list_eq_cons_inv in H₂.
   destruct H₁, H₂.
   etransitivity; [ symmetry; eassumption | assumption ].

   apply list_eq_cons_inv in H₂.
   apply IHl₂; [ destruct H₁ | destruct H₂ ]; assumption.

  apply list_eq_cons_inv in H₁.
  destruct l₃ as [| x₃]; constructor.
   apply list_eq_cons_nil_inv in H₂.
   destruct H₁, H₂.
   etransitivity; eassumption.

   apply list_eq_cons_nil_inv in H₂.
   apply IHl₂; [ destruct H₁ | destruct H₂ ]; assumption.

   apply list_eq_cons_inv in H₂.
   destruct H₁, H₂.
   etransitivity; eassumption.

   apply list_eq_cons_inv in H₂.
   apply IHl₂; [ destruct H₁ | destruct H₂ ]; assumption.
Qed.

Add Parametric Relation α (f : field α) : (list α) (list_eq f)
 reflexivity proved by (list_eq_refl f)
 symmetry proved by (list_eq_sym (f := f))
 transitivity proved by (list_eq_trans (f := f))
 as list_eq_rel.

Theorem eq_poly_refl α (f : field α) : reflexive _ (eq_poly f).
Proof.
intros pol.
unfold eq_poly; reflexivity.
Qed.

Theorem eq_poly_sym α (f : field α) : symmetric _ (eq_poly f).
Proof.
intros pol₁ pol₂ Heq.
unfold eq_poly; symmetry; assumption.
Qed.

Theorem eq_poly_trans α (f : field α) : transitive _ (eq_poly f).
Proof.
intros pol₁ pol₂ pol₃ H₁ H₂.
unfold eq_poly; etransitivity; eassumption.
Qed.

Add Parametric Relation α (f : field α) : (polynomial α) (eq_poly f)
 reflexivity proved by (eq_poly_refl f)
 symmetry proved by (eq_poly_sym (f := f))
 transitivity proved by (eq_poly_trans (f := f))
 as eq_poly_rel.

(* addition *)

Fixpoint list_add α (f : field α) al₁ al₂ :=
  match al₁ with
  | [] => al₂
  | [a₁ … bl₁] =>
      match al₂ with
      | [] => al₁
      | [a₂ … bl₂] => [(a₁ .+ f a₂)%K … list_add f bl₁ bl₂]
      end
  end.

Definition poly_add α (f : field α) pol₁ pol₂ :=
  {| al := list_add f (al pol₁) (al pol₂) |}.

(* multiplication *)

Fixpoint list_convol_mul α (f : field α) al₁ al₂ i len :=
  match len with
  | O => []
  | S len₁ =>
      [Σ f (j = 0, i) _ List.nth j al₁ .0 f .* f List.nth (i - j) al₂ .0 f …
       list_convol_mul f al₁ al₂ (S i) len₁]
  end.

Definition list_mul α (f : field α) la lb :=
  list_convol_mul f la lb 0 (pred (length la + length lb)).

Definition poly_mul α (f : field α) pol₁ pol₂ :=
  {| al := list_mul f (al pol₁) (al pol₂) |}.

(* *)

Notation "a .+ f b" := (poly_add f a b) : poly_scope.
Notation "a .* f b" := (poly_mul f a b) : poly_scope.

Definition Pdivide α (f : field α) x y := ∃ z, (y .= f z .* f x)%pol.

Add Parametric Morphism α (f : field α) : (@al α)
  with signature eq_poly f ==> list_eq f
  as al_morph.
Proof. intros; assumption. Qed.

Lemma list_eq_nil_list_add_r : ∀ α (f : field α) la lb,
  list_eq f [] la
  → list_eq f lb (list_add f la lb).
Proof.
intros α f la lb H.
revert lb.
induction la as [| a]; intros; [ reflexivity | simpl ].
destruct lb as [| b]; [ assumption | idtac ].
apply list_eq_nil_cons_inv in H.
destruct H as (Ha, Hla).
constructor; [ rewrite Ha, fld_add_0_l; reflexivity | idtac ].
apply IHla; assumption.
Qed.

Lemma list_eq_nil_list_add_l : ∀ α (f : field α) la lb,
  list_eq f [] lb
  → list_eq f la (list_add f la lb).
Proof.
intros α f la lb H.
revert la.
induction lb as [| b]; intros; [ destruct la; reflexivity | idtac ].
destruct la as [| a]; [ assumption | simpl ].
apply list_eq_nil_cons_inv in H.
destruct H as (Hb, Hlb).
constructor; [ rewrite Hb, fld_add_0_r; reflexivity | idtac ].
apply IHlb; assumption.
Qed.

Add Parametric Morphism α (f : field α) : (list_add f)
  with signature (list_eq f) ==> (list_eq f) ==> (list_eq f)
  as list_add_morph.
Proof.
intros la lc Hac lb ld Hbd.
revert lb lc ld Hac Hbd.
induction la as [| a]; intros.
 destruct lc as [| c]; intros; [ assumption | idtac ].
 apply list_eq_nil_cons_inv in Hac.
 destruct Hac as (Hc, Hlc); simpl.
 destruct ld as [| d].
  etransitivity; [ eassumption | constructor; assumption ].

  destruct lb as [| b].
   apply list_eq_nil_cons_inv in Hbd.
   destruct Hbd as (Hd, Hld).
   constructor; [ rewrite Hc, fld_add_0_l; assumption | idtac ].
   etransitivity; [ eassumption | idtac ].
   apply list_eq_nil_list_add_r; assumption.

   apply list_eq_cons_inv in Hbd.
   destruct Hbd as (Hbd, Hlbd).
   constructor; [ rewrite Hc, fld_add_0_l; assumption | idtac ].
   etransitivity; [ eassumption | idtac ].
   apply list_eq_nil_list_add_r; assumption.

 destruct lb as [| b].
  destruct lc as [| c]; [ etransitivity; eassumption | idtac ].
  destruct ld as [| d]; [ assumption | simpl ].
  apply list_eq_cons_inv in Hac.
  destruct Hac as (Hac, Hlac).
  apply list_eq_nil_cons_inv in Hbd.
  destruct Hbd as (Hd, Hld).
  constructor; [ rewrite Hd, fld_add_0_r; assumption | idtac ].
  etransitivity; [ eassumption | idtac ].
  apply list_eq_nil_list_add_l; assumption.

  destruct lc as [| c].
   apply list_eq_cons_nil_inv in Hac.
   destruct Hac as (Ha, Hla); simpl.
   destruct ld as [| d].
    apply list_eq_cons_nil_inv in Hbd.
    destruct Hbd as (Hb, Hlb).
    constructor; [ rewrite Ha, fld_add_0_l; assumption | idtac ].
    rewrite IHla; try eassumption; reflexivity.

    apply list_eq_cons_inv in Hbd.
    destruct Hbd as (Hbd, Hlbd).
    constructor; [ rewrite Ha, fld_add_0_l; assumption | idtac ].
    rewrite IHla; try eassumption; reflexivity.

   apply list_eq_cons_inv in Hac.
   destruct Hac as (Hac, Hlac); simpl.
   destruct ld as [| d].
    apply list_eq_cons_nil_inv in Hbd.
    destruct Hbd as (Hb, Hlb).
    constructor; [ rewrite Hb, fld_add_0_r; assumption | idtac ].
    rewrite IHla; try eassumption.
    destruct lc; reflexivity.

    apply list_eq_cons_inv in Hbd.
    destruct Hbd as (Hbd, Hlbd).
    constructor; [ rewrite Hac, Hbd; reflexivity | apply IHla; assumption ].
Qed.

Add Parametric Morphism α (f : field α) : (poly_add f)
  with signature (eq_poly f) ==> (eq_poly f) ==> (eq_poly f)
  as poly_add_morph.
Proof.
intros a c Hac b d Hbd.
unfold eq_poly, poly_add; simpl.
unfold eq_poly in Hac, Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Lemma list_convol_mul_comm : ∀ α (f : field α) l₁ l₂ i len,
  list_eq f (list_convol_mul f l₁ l₂ i len) (list_convol_mul f l₂ l₁ i len).
Proof.
intros α f l₁ l₂ i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite summation_rtl.
apply summation_compat; intros j (_, Hj).
rewrite Nat.add_0_r.
rewrite fld_mul_comm.
apply fld_mul_compat; [ idtac | reflexivity ].
rewrite Nat_sub_sub_distr; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Lemma list_convol_mul_nil_l : ∀ α (f : field α) l i len,
  list_eq f (list_convol_mul f [] l i len) [].
Proof.
intros α f l i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite all_0_summation_0; [ reflexivity | idtac ].
intros k (_, Hk).
destruct k; rewrite fld_mul_0_l; reflexivity.
Qed.

Lemma list_convol_mul_nil_r : ∀ α (f : field α) l i len,
  list_eq f (list_convol_mul f l [] i len) [].
Proof.
intros α f l i len.
rewrite list_convol_mul_comm.
apply list_convol_mul_nil_l.
Qed.

Lemma list_convol_mul_compat : ∀ α (f : field α) la lb lc ld i len,
  list_eq f la lc
  → list_eq f lb ld
    → list_eq f (list_convol_mul f la lb i len)
        (list_convol_mul f lc ld i len).
Proof.
intros α f la lb lc ld i len Hac Hbd.
revert la lb lc ld i Hac Hbd.
induction len; intros; [ reflexivity | simpl ].
constructor.
 apply summation_compat; intros j (_, Hj).
 apply fld_mul_compat.
  clear Hj; revert j.
  induction Hac; intros.
   reflexivity.

   destruct j; [ assumption | apply IHHac ].

   destruct j; [ assumption | simpl; rewrite IHHac ].
   destruct j; reflexivity.

   symmetry.
   destruct j; [ assumption | simpl; rewrite <- IHHac ].
   destruct j; reflexivity.

  remember (i - j)%nat as k; clear Heqk; revert k.
  induction Hbd; intros.
   reflexivity.

   destruct k; [ assumption | apply IHHbd ].

   destruct k; [ assumption | simpl; rewrite IHHbd ].
   destruct k; reflexivity.

   symmetry.
   destruct k; [ assumption | simpl; rewrite <- IHHbd ].
   destruct k; reflexivity.

 apply IHlen; assumption.
Qed.

Lemma list_eq_nil_list_convol_mul_nil_l : ∀ α (f : field α) la lb i len,
  list_eq f la []
  → list_eq f (list_convol_mul f la lb i len) [].
Proof.
intros α f la lb i len Heq.
revert la lb i Heq.
induction len; intros; [ reflexivity | simpl ].
constructor.
 rewrite all_0_summation_0; [ reflexivity | idtac ].
 intros j (_, Hj).
 remember (i - j)%nat as h.
 revert Heq; clear; intros.
 revert j.
 induction la as [| a]; intros.
  simpl; destruct j; rewrite fld_mul_0_l; reflexivity.

  apply list_eq_cons_nil_inv in Heq.
  destruct Heq as (Ha, Hla).
  destruct j; simpl; [ rewrite Ha, fld_mul_0_l; reflexivity | idtac ].
  apply IHla; assumption.

 apply IHlen; assumption.
Qed.

Lemma list_eq_nil_list_convol_mul_nil_r : ∀ α (f : field α) la lb i len,
  list_eq f lb []
  → list_eq f (list_convol_mul f la lb i len) [].
Proof.
intros α f la lb i len Heq.
revert la lb i Heq.
induction len; intros; [ reflexivity | simpl ].
constructor.
 rewrite all_0_summation_0; [ reflexivity | idtac ].
 intros j (_, Hj).
 remember (i - j)%nat as h.
 revert Heq; clear; intros.
 revert h.
 induction lb as [| b]; intros.
  simpl; destruct h; rewrite fld_mul_0_r; reflexivity.

  apply list_eq_cons_nil_inv in Heq.
  destruct Heq as (Hb, Hlb).
  destruct h; simpl; [ rewrite Hb, fld_mul_0_r; reflexivity | idtac ].
  apply IHlb; assumption.

 apply IHlen; assumption.
Qed.

Lemma list_eq_list_nth : ∀ α (f : field α) la lb n,
  list_eq f la lb
  → (List.nth n la .0 f .= f List.nth n lb .0 f)%K.
Proof.
intros α f la lb n Heq.
revert la lb Heq.
induction n; intros.
 destruct la as [| a].
  destruct lb as [| b]; [ reflexivity | simpl ].
  apply list_eq_nil_cons_inv in Heq.
  destruct Heq; symmetry; assumption.

  destruct lb as [| b].
   apply list_eq_cons_nil_inv in Heq.
   destruct Heq; assumption.

   apply list_eq_cons_inv in Heq.
   destruct Heq; assumption.

 destruct la as [| a]; simpl.
  destruct lb as [| b]; [ reflexivity | simpl ].
  apply list_eq_nil_cons_inv in Heq.
  destruct Heq as (Hb, Hlb).
  rewrite <- IHn; [ idtac | eassumption ].
  destruct n; reflexivity.

  destruct lb as [| b]; simpl.
   apply list_eq_cons_nil_inv in Heq.
   destruct Heq as (Ha, Hla).
   rewrite IHn; [ idtac | eassumption ].
   destruct n; reflexivity.

   apply list_eq_cons_inv in Heq.
   apply IHn; destruct Heq; assumption.
Qed.

Add Parametric Morphism α (f : field α) : (list_convol_mul f)
  with signature (list_eq f) ==> (list_eq f) ==> eq ==> eq ==> (list_eq f)
  as list_convol_mul_morph.
Proof.
intros la lc Hac lb ld Hbd i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
apply summation_compat; intros j (_, Hj).
apply fld_mul_compat; apply list_eq_list_nth; assumption.
Qed.

Lemma list_convol_mul_succ : ∀ α (f : field α) la lb i len,
  list_eq f
    (list_convol_mul f la lb i (S len))
    (list_convol_mul f la lb i len ++
     [Σ f (j = 0, i + len)_
      List.nth j la .0 f .* f List.nth (i + len - j) lb .0 f])%K.
Proof.
intros α f la lb i len.
revert la lb i.
induction len; intros; simpl.
 rewrite Nat.add_0_r; reflexivity.

 constructor; [ reflexivity | idtac ].
 simpl in IHlen.
 rewrite IHlen.
 rewrite Nat.add_succ_r, Nat.add_succ_l.
 reflexivity.
Qed.

Lemma list_eq_app_0s : ∀ α (f : field α) la lb,
  List.Forall (λ b, b .= f .0 f)%K lb
  → list_eq f la (la ++ lb).
Proof.
intros α f la lb Hz.
induction la as [| a]; simpl.
 induction lb as [| b]; [ reflexivity | idtac ].
 constructor.
  apply list_Forall_inv in Hz; destruct Hz; assumption.

  apply IHlb.
  apply list_Forall_inv in Hz; destruct Hz; assumption.

 constructor; [ reflexivity | assumption ].
Qed.

Lemma list_convol_mul_more : ∀ α (f : field α) la lb i n,
  list_eq f (list_convol_mul f la lb i (pred (length la + length lb)))
    (list_convol_mul f la lb i (pred (length la + length lb) + n)).
Proof.
intros α f la lb i n.
induction n; [ rewrite Nat.add_0_r; reflexivity | idtac ].
rewrite Nat.add_succ_r.
rewrite list_convol_mul_succ.
rewrite IHn.
apply list_eq_app_0s.
constructor; [ idtac | constructor ].
apply all_0_summation_0.
intros j (_, Hj).
apply fld_mul_eq_0.
destruct (le_dec (length la) j) as [H₁| H₁].
 left.
 rewrite List.nth_overflow; [ reflexivity | assumption ].

 apply Nat.nle_gt in H₁.
 destruct (le_dec (length lb) (i + (pred (length la + length lb) + n) - j))
  as [H₂| H₂].
  right.
  rewrite List.nth_overflow; [ reflexivity | assumption ].

  exfalso; apply H₂; fast_omega H₁.
Qed.

Add Parametric Morphism α (f : field α) : (list_mul f)
  with signature list_eq f ==> list_eq f ==> list_eq f
  as list_mul_morph.
Proof.
intros a c Hac b d Hbd.
unfold list_mul; simpl.
do 2 rewrite list_convol_mul_more.
rewrite Hac, Hbd in |- * at 1.
rewrite Nat.add_comm.
reflexivity.
Qed.

Add Parametric Morphism α (f : field α) : (poly_mul f)
  with signature (eq_poly f) ==> (eq_poly f) ==> (eq_poly f)
  as poly_mul_morph.
Proof.
intros a c Hac b d Hbd.
unfold eq_poly, poly_mul, list_mul; simpl.
unfold eq_poly in Hac, Hbd.
remember (al a) as la.
remember (al b) as lb.
remember (al c) as lc.
remember (al d) as ld.
revert Hac Hbd; clear; intros.
do 2 rewrite list_convol_mul_more.
rewrite Hac, Hbd in |- * at 1.
rewrite Nat.add_comm.
reflexivity.
Qed.

Add Parametric Morphism α (f : field α) : (@cons α)
  with signature fld_eq f ==> list_eq f ==> list_eq f
  as cons_list_eq_morph.
Proof.
intros a b H la lb Hab.
constructor; assumption.
Qed.

(* composition *)

Definition list_compose α (f : field α) la lb :=
  List.fold_right (λ c accu, list_add f (list_mul f accu lb) [c]) [] la.

Definition poly_compose α (f : field α) a b :=
  POL (list_compose f (al a) (al b))%pol.

(* test
Load Q_field.
Definition Qtest_comp := list_compose Q_field.
Eval vm_compute in Qtest_comp [5#1; -4#1; 3#1; 2#1 … []] [2#1; -4#1; 7#1; 6#1 … []].
     = [25 # 1; -128 # 1; 464 # 1; -776 # 1; 687 # 1;
       660 # 1; -790 # 1; 900 # 1; 1512 # 1; 432 # 1; 0; 0 …
       []]
     : list Q
Eval vm_compute in Qtest_comp [2#1; -4#1; 7#1; 6#1 … []] [5#1; -4#1; 3#1; 2#1 … []].
     = [907 # 1; -2064 # 1; 3100 # 1; -1680 # 1; 185 # 1;
       1092 # 1; -314 # 1; 36 # 1; 216 # 1; 48 # 1; 0; 0 …
       []]
     : list Q
Eval vm_compute in Qtest_comp [-2#1; 4#1; -3#1 … []] [-1#1; 4#1 … []].
     = [-9 # 1; 40 # 1; -48 # 1 … []]
     : list Q
Eval vm_compute in Qtest_comp [-1#1; 4#1 … []] [-2#1; 4#1; -3#1 … []].
     = [-9 # 1; 16 # 1; -12 # 1; 0 … []]
     : list Q
*)

Section poly.

Variable α : Type.
Variable f : field α.

(* addition theorems *)

Lemma list_add_compat : ∀ a b c d,
  list_eq f a c
  → list_eq f b d
    → list_eq f (list_add f a b) (list_add f c d).
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Theorem poly_add_compat : ∀ a b c d,
  (a .= f c)%pol
  → (b .= f d)%pol
    → (a .+ f b .= f c .+ f d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Lemma list_add_comm : ∀ al₁ al₂,
  list_eq f (list_add f al₁ al₂) (list_add f al₂ al₁).
Proof.
intros al₁ al₂.
revert al₂.
induction al₁; intros.
 destruct al₂; [ apply list_eq_refl | simpl ].
 constructor; [ reflexivity | apply list_eq_refl ].

 destruct al₂.
  constructor; [ reflexivity | apply list_eq_refl ].

  constructor; [ apply fld_add_comm | apply IHal₁ ].
Qed.

Theorem poly_add_comm : ∀ pol₁ pol₂, (pol₁ .+ f pol₂ .= f pol₂ .+ f pol₁)%pol.
Proof.
intros pol₁ pol₂.
unfold eq_poly.
eapply list_add_comm; reflexivity.
Qed.

Lemma list_add_assoc : ∀ al₁ al₂ al₃,
  list_eq f (list_add f (list_add f al₁ al₂) al₃)
    (list_add f al₁ (list_add f al₂ al₃)).
Proof.
intros al₁ al₂ al₃.
revert al₂ al₃.
induction al₁; intros.
 destruct al₂.
  destruct al₃; [ apply list_eq_refl | idtac ].
  constructor; [ reflexivity | apply list_eq_refl ].

  destruct al₃; simpl.
   constructor; [ reflexivity | apply list_eq_refl ].

   constructor; [ reflexivity | apply list_eq_refl ].

 destruct al₂.
  destruct al₃; simpl.
   constructor; [ reflexivity | apply list_eq_refl ].

   constructor; [ reflexivity | apply list_eq_refl ].

  destruct al₃; simpl.
   constructor; [ reflexivity | apply list_eq_refl ].

   constructor; [ symmetry; apply fld_add_assoc | apply IHal₁ ].
Qed.

Lemma poly_add_assoc : ∀ pol₁ pol₂ pol₃,
  ((pol₁ .+ f pol₂) .+ f pol₃ .= f pol₁ .+ f (pol₂ .+ f pol₃))%pol.
Proof.
intros pol₁ pol₂ pol₃.
unfold eq_poly.
eapply list_add_assoc; reflexivity.
Qed.

Lemma list_add_nil_l : ∀ la,
  list_eq f (list_add f [] la) la.
Proof. intros la; destruct la; reflexivity. Qed.

Lemma list_add_nil_r : ∀ la,
  list_eq f (list_add f la []) la.
Proof. intros la; destruct la; reflexivity. Qed.

(* multiplication theorems *)

Lemma list_mul_compat : ∀ a b c d,
  list_eq f a c
  → list_eq f b d
    → list_eq f (list_mul f a b) (list_mul f c d).
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Theorem poly_mul_compat : ∀ a b c d,
  (a .= f c)%pol
  → (b .= f d)%pol
    → (a .* f b .= f c .* f d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Lemma list_nth_list_eq : ∀ la lb,
  (∀ i, List.nth i la .0 f .= f List.nth i lb .0 f)%K
  → list_eq f la lb.
Proof.
intros la lb Hi.
revert lb Hi.
induction la as [| a]; intros.
 induction lb as [| b]; [ reflexivity | constructor ].
  pose proof (Hi O) as H.
  symmetry; assumption.

  apply IHlb; intros i.
  pose proof (Hi (S i)) as H; simpl in H; rewrite <- H.
  destruct i; reflexivity.

 induction lb as [| b].
  constructor.
   pose proof (Hi O) as H.
   assumption.

   apply IHla; intros i.
   pose proof (Hi (S i)) as H; simpl in H; rewrite H.
   destruct i; reflexivity.

  constructor.
   pose proof (Hi O) as H.
   assumption.

   apply IHla; intros i.
   pose proof (Hi (S i)) as H.
   assumption.
Qed.

Lemma list_mul_comm : ∀ a b, list_eq f (list_mul f a b) (list_mul f b a).
Proof.
intros a b.
unfold list_mul.
rewrite list_convol_mul_comm, Nat.add_comm; reflexivity.
Qed.

Theorem poly_mul_comm : ∀ a b, (a .* f b .= f b .* f a)%pol.
Proof.
intros a b.
unfold eq_poly; simpl.
unfold list_mul; simpl.
rewrite Nat.add_comm.
rewrite list_convol_mul_comm; reflexivity.
Qed.

Lemma list_mul_assoc : ∀ al₁ al₂ al₃,
  list_eq f (list_mul f (list_mul f al₁ al₂) al₃)
    (list_mul f al₁ (list_mul f al₂ al₃)).
Proof.
intros al₁ al₂ al₃.
bbb.

Lemma list_nth_list_convol_mul_aux : ∀ la lb n i len,
  pred (List.length la + List.length lb) = (i + len)%nat
  → (List.nth n (list_convol_mul f la lb i len) .0 f%K .= f
     Σ f (j = 0, n + i)_
     List.nth j la .0 f .* f List.nth (n + i - j) lb .0 f)%K.
Proof.
intros la lb n i len Hlen.
revert la lb i n Hlen.
induction len; intros.
 simpl.
 rewrite Nat.add_0_r in Hlen.
 rewrite all_0_summation_0; [ destruct n; reflexivity | idtac ].
 intros j (_, Hj).
 destruct (le_dec (length la) j) as [H₁| H₁].
  rewrite List.nth_overflow; [ idtac | assumption ].
  rewrite fld_mul_0_l; reflexivity.

  destruct (le_dec (length lb) (n + i - j)) as [H₂| H₂].
   rewrite fld_mul_comm.
   rewrite List.nth_overflow; [ idtac | assumption ].
   rewrite fld_mul_0_l; reflexivity.

   exfalso; fast_omega Hlen H₁ H₂.

 simpl.
 destruct n; [ reflexivity | idtac ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
 rewrite IHlen; [ idtac | assumption ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l; reflexivity.
Qed.

Lemma list_nth_list_convol_mul : ∀ la lb i len,
  len = pred (length la + length lb)
  → (List.nth i (list_convol_mul f la lb 0 len) .0 f .= f
     Σ f (j = 0, i) _ List.nth j la .0 f .* f List.nth (i - j) lb .0 f)%K.
Proof.
intros la lb i len Hlen.
symmetry in Hlen.
rewrite list_nth_list_convol_mul_aux; [ idtac | assumption ].
rewrite Nat.add_0_r; reflexivity.
Qed.

Lemma list_eq_skipn_succ : ∀ cl i,
  list_eq f [List.nth i cl .0 f%K … List.skipn (S i) cl] (List.skipn i cl).
Proof.
intros cl i.
revert i.
induction cl as [| c]; intros; simpl.
 destruct i; constructor; reflexivity.

 destruct i; [ reflexivity | apply IHcl ].
Qed.

Lemma list_convol_mul_1_l : ∀ cl i len,
  length cl = (i + len)%nat
  → list_eq f (list_convol_mul f [.1 f%K] cl i len) (List.skipn i cl).
Proof.
intros cl i len Hlen.
revert cl i Hlen.
induction len; intros.
 simpl.
 rewrite Nat.add_0_r in Hlen.
 rewrite list_skipn_overflow; subst; reflexivity.

 simpl.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite fld_mul_1_l, Nat.sub_0_r.
 rewrite all_0_summation_0.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
  rewrite fld_add_0_r, IHlen; [ clear | assumption ].
  apply list_eq_skipn_succ.

  intros j (Hj, Hji).
  destruct j; [ exfalso; omega | idtac ].
  destruct j; rewrite fld_mul_0_l; reflexivity.
Qed.

Lemma list_convol_mul_x_l : ∀ cl i len,
  length cl = (i + len)%nat
  → list_eq f
      (list_convol_mul f [.0 f%K; .1 f%K … []] cl (S i) len)
      (List.skipn i cl).
Proof.
intros cl i len Hlen.
revert cl i Hlen.
induction len; intros.
 simpl.
 rewrite Nat.add_0_r in Hlen.
 rewrite list_skipn_overflow; subst; reflexivity.

 simpl.
 rewrite summation_only_one_non_0 with (v := 1%nat).
  rewrite fld_mul_1_l, Nat.sub_0_r.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
  rewrite IHlen; [ idtac | assumption ].
  apply list_eq_skipn_succ.

  split; [ apply Nat.le_0_l | apply le_n_S, Nat.le_0_l ].

  intros j (_, Hj) Hjn1.
  destruct j; [ rewrite fld_mul_0_l; reflexivity | simpl ].
  destruct j; [ exfalso; apply Hjn1; reflexivity | idtac ].
  destruct j; rewrite fld_mul_0_l; reflexivity.
Qed.

Theorem poly_mul_1_l : ∀ a, (.1 f .* f a .= f a)%pol.
Proof.
intros a.
unfold eq_poly; simpl.
unfold list_mul; simpl.
rewrite list_convol_mul_1_l; reflexivity.
Qed.

Theorem poly_mul_1_r : ∀ a, (a .* f .1 f .= f a)%pol.
Proof.
intros a.
rewrite poly_mul_comm.
apply poly_mul_1_l.
Qed.

Lemma list_mul_nil_l : ∀ la, list_eq f (list_mul f [] la) [].
Proof.
intros la.
apply list_convol_mul_nil_l.
Qed.

Lemma list_mul_nil_r : ∀ la, list_eq f (list_mul f la []) [].
Proof.
intros la.
apply list_convol_mul_nil_r.
Qed.

Fixpoint list_convol_mul_add al₁ al₂ al₃ i len :=
  match len with
  | O => []
  | S len₁ =>
      [Σ f (j = 0, i) _
       List.nth j al₁ .0 f .* f
       (List.nth (i - j) al₂ .0 f .+ f List.nth (i - j) al₃ .0 f) …
       list_convol_mul_add al₁ al₂ al₃ (S i) len₁]
  end.

Lemma list_nth_add : ∀ k la lb,
  (List.nth k (list_add f la lb) .0 f .= f
   List.nth k la .0 f .+ f List.nth k lb .0 f)%K.
Proof.
intros k la lb.
revert la lb.
induction k; intros.
 destruct la as [| a]; simpl; [ rewrite fld_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite fld_add_0_r; reflexivity | idtac ].
 reflexivity.

 destruct la as [| a]; simpl; [ rewrite fld_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite fld_add_0_r; reflexivity | idtac ].
 apply IHk.
Qed.

Lemma list_convol_mul_list_add : ∀ la lb lc i len,
   list_eq f
     (list_convol_mul f la (list_add f lb lc) i len)
     (list_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
apply summation_compat; intros j (_, Hj).
apply fld_mul_compat_l.
rewrite list_nth_add; reflexivity.
Qed.

Lemma list_add_list_convol_mul : ∀ la lb lc i len,
   list_eq f
     (list_add f
        (list_convol_mul f la lb i len)
        (list_convol_mul f la lc i len))
     (list_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite <- summation_add_distr.
apply summation_compat; intros j (_, Hj).
rewrite fld_mul_add_distr_l; reflexivity.
Qed.

Lemma list_mul_add_distr_l : ∀ la lb lc,
  list_eq f (list_mul f la (list_add f lb lc))
    (list_add f (list_mul f la lb) (list_mul f la lc)).
Proof.
intros la lb lc.
unfold list_mul.
remember (pred (length la + length (list_add f lb lc))) as labc.
remember (pred (length la + length lb)) as lab.
remember (pred (length la + length lc)) as lac.
rewrite Heqlabc.
rewrite list_convol_mul_more with (n := (lab + lac)%nat).
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite list_convol_mul_more with (n := (labc + lac)%nat).
rewrite <- Heqlab.
rewrite list_add_comm.
rewrite Heqlac.
rewrite list_convol_mul_more with (n := (labc + lab)%nat).
rewrite <- Heqlac.
rewrite Nat.add_comm.
rewrite list_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite list_convol_mul_list_add.
rewrite list_add_list_convol_mul.
reflexivity.
Qed.

Lemma list_mul_add_distr_r : ∀ la lb lc,
  list_eq f (list_mul f (list_add f la lb) lc)
    (list_add f (list_mul f la lc) (list_mul f lb lc)).
Proof.
intros la lb lc.
rewrite list_mul_comm, list_mul_add_distr_l, list_mul_comm.
apply list_add_compat; [ reflexivity | apply list_mul_comm ].
Qed.

End poly.

(* Horner's algorithm *)
Definition horner α β γ
    (zero_c : α) (add_v_c : α → β → α) (mul_v_x : α → γ → α)
    (pol : polynomial β) (x : γ) :=
  List.fold_right (λ c accu, add_v_c (mul_v_x accu x) c) zero_c (al pol).
