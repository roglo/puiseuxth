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

(* lap : list as polynomial, i.e. the only field of the record in the
   definition of polynomial above *)

Inductive lap_eq α (f : field α) : list α → list α → Prop :=
  | lap_eq_nil : lap_eq f [] []
  | lap_eq_cons : ∀ x₁ x₂ l₁ l₂,
      (x₁ .= f x₂)%K
      → lap_eq f l₁ l₂
        → lap_eq f [x₁ … l₁] [x₂ … l₂]
  | lap_eq_cons_nil : ∀ x l,
      (x .= f .0 f)%K
      → lap_eq f l []
        → lap_eq f [x … l] []
  | lap_eq_nil_cons : ∀ x l,
      (x .= f .0 f)%K
      → lap_eq f [] l
        → lap_eq f [] [x … l].

Delimit Scope poly_scope with pol.
Notation "'POL' l" := {| al := l |} (at level 1) : poly_scope.

Definition eq_poly α (f : field α) x y := lap_eq f (al x) (al y).

Notation "a .= f b" := (eq_poly f a b) : poly_scope.

Definition poly_one α (f : field α) := POL [.1 f%K]%pol.
Notation ".1 f" := (poly_one f) : poly_scope.

Lemma lap_eq_cons_inv : ∀ α (f : field α) x₁ x₂ l₁ l₂,
  lap_eq f [x₁ … l₁] [x₂ … l₂]
  → (x₁ .= f x₂)%K ∧ lap_eq f l₁ l₂.
Proof.
intros α f x₁ x₂ l₁ l₂ H.
inversion H; split; assumption.
Qed.

Lemma lap_eq_cons_nil_inv : ∀ α (f : field α) x l,
  lap_eq f [x … l] []
  → (x .= f .0 f)%K ∧ lap_eq f l [].
Proof.
intros α f x l H.
inversion H; split; assumption.
Qed.

Lemma lap_eq_nil_cons_inv : ∀ α (f : field α) x l,
  lap_eq f [] [x … l]
  → (x .= f .0 f)%K ∧ lap_eq f [] l.
Proof.
intros α f x l H.
inversion H; split; assumption.
Qed.

Theorem lap_eq_refl α (f : field α) : reflexive _ (lap_eq f).
Proof.
intros l.
induction l; constructor; [ reflexivity | assumption ].
Qed.

Theorem lap_eq_sym α (f : field α) : symmetric _ (lap_eq f).
Proof.
intros l₁ l₂ Heq.
revert l₂ Heq.
induction l₁ as [| x₁]; intros.
 induction l₂ as [| x₂]; constructor; apply lap_eq_nil_cons_inv in Heq.
  destruct Heq; assumption.

  apply IHl₂; destruct Heq; assumption.

 induction l₂ as [| x₂].
  apply lap_eq_cons_nil_inv in Heq; destruct Heq.
  constructor; [ assumption | apply IHl₁; assumption ].

  apply lap_eq_cons_inv in Heq; destruct Heq.
  constructor; [ symmetry; assumption | apply IHl₁; assumption ].
Qed.

Theorem lap_eq_trans α (f : field α) : transitive _ (lap_eq f).
Proof.
intros l₁ l₂ l₃ H₁ H₂.
revert l₁ l₃ H₁ H₂.
induction l₂ as [| x₂]; intros.
 revert l₃ H₂.
 induction l₁ as [| x₁]; intros; [ assumption | idtac ].
 destruct l₃ as [| x₃]; [ assumption | idtac ].
 apply lap_eq_cons_nil_inv in H₁.
 apply lap_eq_nil_cons_inv in H₂.
 constructor.
  etransitivity; [ destruct H₁; eassumption | idtac ].
  destruct H₂; symmetry; assumption.

  apply IHl₁; [ destruct H₁ | destruct H₂ ]; assumption.

 destruct l₁ as [| x₁].
  apply lap_eq_nil_cons_inv in H₁.
  destruct l₃ as [| x₃]; constructor.
   apply lap_eq_cons_inv in H₂.
   destruct H₁, H₂.
   etransitivity; [ symmetry; eassumption | assumption ].

   apply lap_eq_cons_inv in H₂.
   apply IHl₂; [ destruct H₁ | destruct H₂ ]; assumption.

  apply lap_eq_cons_inv in H₁.
  destruct l₃ as [| x₃]; constructor.
   apply lap_eq_cons_nil_inv in H₂.
   destruct H₁, H₂.
   etransitivity; eassumption.

   apply lap_eq_cons_nil_inv in H₂.
   apply IHl₂; [ destruct H₁ | destruct H₂ ]; assumption.

   apply lap_eq_cons_inv in H₂.
   destruct H₁, H₂.
   etransitivity; eassumption.

   apply lap_eq_cons_inv in H₂.
   apply IHl₂; [ destruct H₁ | destruct H₂ ]; assumption.
Qed.

Add Parametric Relation α (f : field α) : (list α) (lap_eq f)
 reflexivity proved by (lap_eq_refl f)
 symmetry proved by (lap_eq_sym (f := f))
 transitivity proved by (lap_eq_trans (f := f))
 as lap_eq_rel.

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

Lemma lap_eq_list_fold_right : ∀ α (K : field α) β g h x (l : list β),
  (∀ i a b, i ∈ l → lap_eq K a b → lap_eq K (g i a) (h i b))
  → lap_eq K (List.fold_right g x l) (List.fold_right h x l).
Proof.
intros α K β g h x l H.
induction l as [| y]; intros; [ reflexivity | simpl ].
apply H; [ left; reflexivity | idtac ].
apply IHl; intros i a b Hi Heq.
apply H; [ right; assumption | assumption ].
Qed.

(* addition *)

Fixpoint lap_add α (f : field α) al₁ al₂ :=
  match al₁ with
  | [] => al₂
  | [a₁ … bl₁] =>
      match al₂ with
      | [] => al₁
      | [a₂ … bl₂] => [(a₁ .+ f a₂)%K … lap_add f bl₁ bl₂]
      end
  end.

Definition poly_add α (f : field α) pol₁ pol₂ :=
  {| al := lap_add f (al pol₁) (al pol₂) |}.

(* multiplication *)

Fixpoint lap_convol_mul α (f : field α) al₁ al₂ i len :=
  match len with
  | O => []
  | S len₁ =>
      [Σ f (j = 0, i), List.nth j al₁ .0 f .* f List.nth (i - j) al₂ .0 f …
       lap_convol_mul f al₁ al₂ (S i) len₁]
  end.

Definition lap_mul α (f : field α) la lb :=
  lap_convol_mul f la lb 0 (pred (length la + length lb)).

Definition poly_mul α (f : field α) pol₁ pol₂ :=
  {| al := lap_mul f (al pol₁) (al pol₂) |}.

(* power *)

Fixpoint lap_power α (f : field α) la n :=
  match n with
  | O => [.1 f%K]
  | S m => lap_mul f la (lap_power f la m)
  end.

Definition poly_power α (f : field α) pol n :=
  (POL (lap_power f (al pol) n))%pol.

(* composition *)

Definition lap_compose α (f : field α) la lb :=
  List.fold_right (λ c accu, lap_add f (lap_mul f accu lb) [c]) [] la.

Definition poly_compose α (f : field α) a b :=
  POL (lap_compose f (al a) (al b))%pol.

Definition lap_compose2 α (f : field α) la lb :=
  List.fold_right
    (λ i accu,
     lap_add f accu (lap_mul f [List.nth i la .0 f] (lap_power f lb i)))%K
    [] (List.seq 0 (length la)).

Definition poly_compose2 α (f : field α) a b :=
  POL (lap_compose2 f (al a) (al b))%pol.

(* *)

Fixpoint list_pad α n (zero : α) rem :=
  match n with
  | O => rem
  | S n₁ => [zero … list_pad n₁ zero rem]
  end.

Notation "a .+ f b" := (poly_add f a b) : poly_scope.
Notation "a .* f b" := (poly_mul f a b) : poly_scope.
Notation "a .^ f b" := (poly_power f a b) : poly_scope.
Notation "a .∘ f b" := (poly_compose f a b) : poly_scope.

Definition Pdivide α (f : field α) x y := ∃ z, (y .= f z .* f x)%pol.

Definition list_nth_def_0 α (f : field α) n l := List.nth n l .0 f%K.

Lemma fold_list_nth_def_0 : ∀ α (f : field α) n l,
  List.nth n l .0 f%K = list_nth_def_0 f n l.
Proof. reflexivity. Qed.

(* *)

Add Parametric Morphism α (f : field α) : (@al α)
  with signature eq_poly f ==> lap_eq f
  as al_morph.
Proof. intros; assumption. Qed.

Add Parametric Morphism α (f : field α) : (list_nth_def_0 f)
  with signature eq ==> lap_eq f ==> fld_eq f
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
 apply lap_eq_nil_cons_inv in Hab.
 destruct Hab as (Hb, Hlb).
 destruct n; [ assumption | simpl ].
 apply IHlb; assumption.

 destruct n; simpl.
  destruct lb as [| b]; simpl.
   apply lap_eq_cons_nil_inv in Hab.
   destruct Hab; assumption.

   apply lap_eq_cons_inv in Hab.
   destruct Hab; assumption.

  destruct lb as [| b]; simpl.
   apply lap_eq_cons_nil_inv in Hab.
   destruct Hab as (_, Hla).
   clear a IHla.
   revert n.
   induction la as [| a]; intros.
    destruct n; reflexivity.

    destruct n; simpl.
     apply lap_eq_cons_nil_inv in Hla.
     destruct Hla; assumption.

     apply lap_eq_cons_nil_inv in Hla.
     apply IHla; destruct Hla; assumption.

   apply lap_eq_cons_inv in Hab.
   destruct Hab as (_, Hab).
   apply IHla; assumption.
Qed.

Lemma lap_eq_nil_lap_add_r : ∀ α (f : field α) la lb,
  lap_eq f [] la
  → lap_eq f lb (lap_add f la lb).
Proof.
intros α f la lb H.
revert lb.
induction la as [| a]; intros; [ reflexivity | simpl ].
destruct lb as [| b]; [ assumption | idtac ].
apply lap_eq_nil_cons_inv in H.
destruct H as (Ha, Hla).
constructor; [ rewrite Ha, fld_add_0_l; reflexivity | idtac ].
apply IHla; assumption.
Qed.

Lemma lap_eq_nil_lap_add_l : ∀ α (f : field α) la lb,
  lap_eq f [] lb
  → lap_eq f la (lap_add f la lb).
Proof.
intros α f la lb H.
revert la.
induction lb as [| b]; intros; [ destruct la; reflexivity | idtac ].
destruct la as [| a]; [ assumption | simpl ].
apply lap_eq_nil_cons_inv in H.
destruct H as (Hb, Hlb).
constructor; [ rewrite Hb, fld_add_0_r; reflexivity | idtac ].
apply IHlb; assumption.
Qed.

Add Parametric Morphism α (f : field α) : (lap_add f)
  with signature (lap_eq f) ==> (lap_eq f) ==> (lap_eq f)
  as lap_add_morph.
Proof.
intros la lc Hac lb ld Hbd.
revert lb lc ld Hac Hbd.
induction la as [| a]; intros.
 destruct lc as [| c]; intros; [ assumption | idtac ].
 apply lap_eq_nil_cons_inv in Hac.
 destruct Hac as (Hc, Hlc); simpl.
 destruct ld as [| d].
  etransitivity; [ eassumption | constructor; assumption ].

  destruct lb as [| b].
   apply lap_eq_nil_cons_inv in Hbd.
   destruct Hbd as (Hd, Hld).
   constructor; [ rewrite Hc, fld_add_0_l; assumption | idtac ].
   etransitivity; [ eassumption | idtac ].
   apply lap_eq_nil_lap_add_r; assumption.

   apply lap_eq_cons_inv in Hbd.
   destruct Hbd as (Hbd, Hlbd).
   constructor; [ rewrite Hc, fld_add_0_l; assumption | idtac ].
   etransitivity; [ eassumption | idtac ].
   apply lap_eq_nil_lap_add_r; assumption.

 destruct lb as [| b].
  destruct lc as [| c]; [ etransitivity; eassumption | idtac ].
  destruct ld as [| d]; [ assumption | simpl ].
  apply lap_eq_cons_inv in Hac.
  destruct Hac as (Hac, Hlac).
  apply lap_eq_nil_cons_inv in Hbd.
  destruct Hbd as (Hd, Hld).
  constructor; [ rewrite Hd, fld_add_0_r; assumption | idtac ].
  etransitivity; [ eassumption | idtac ].
  apply lap_eq_nil_lap_add_l; assumption.

  destruct lc as [| c].
   apply lap_eq_cons_nil_inv in Hac.
   destruct Hac as (Ha, Hla); simpl.
   destruct ld as [| d].
    apply lap_eq_cons_nil_inv in Hbd.
    destruct Hbd as (Hb, Hlb).
    constructor; [ rewrite Ha, fld_add_0_l; assumption | idtac ].
    rewrite IHla; try eassumption; reflexivity.

    apply lap_eq_cons_inv in Hbd.
    destruct Hbd as (Hbd, Hlbd).
    constructor; [ rewrite Ha, fld_add_0_l; assumption | idtac ].
    rewrite IHla; try eassumption; reflexivity.

   apply lap_eq_cons_inv in Hac.
   destruct Hac as (Hac, Hlac); simpl.
   destruct ld as [| d].
    apply lap_eq_cons_nil_inv in Hbd.
    destruct Hbd as (Hb, Hlb).
    constructor; [ rewrite Hb, fld_add_0_r; assumption | idtac ].
    rewrite IHla; try eassumption.
    destruct lc; reflexivity.

    apply lap_eq_cons_inv in Hbd.
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

Lemma lap_convol_mul_comm : ∀ α (f : field α) l₁ l₂ i len,
  lap_eq f (lap_convol_mul f l₁ l₂ i len) (lap_convol_mul f l₂ l₁ i len).
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

Lemma lap_convol_mul_nil_l : ∀ α (f : field α) l i len,
  lap_eq f (lap_convol_mul f [] l i len) [].
Proof.
intros α f l i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite all_0_summation_0; [ reflexivity | idtac ].
intros k (_, Hk).
destruct k; rewrite fld_mul_0_l; reflexivity.
Qed.

Lemma lap_convol_mul_nil_r : ∀ α (f : field α) l i len,
  lap_eq f (lap_convol_mul f l [] i len) [].
Proof.
intros α f l i len.
rewrite lap_convol_mul_comm.
apply lap_convol_mul_nil_l.
Qed.

Lemma lap_convol_mul_compat : ∀ α (f : field α) la lb lc ld i len,
  lap_eq f la lc
  → lap_eq f lb ld
    → lap_eq f (lap_convol_mul f la lb i len)
        (lap_convol_mul f lc ld i len).
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

Lemma lap_eq_nil_lap_convol_mul_nil_l : ∀ α (f : field α) la lb i len,
  lap_eq f la []
  → lap_eq f (lap_convol_mul f la lb i len) [].
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

  apply lap_eq_cons_nil_inv in Heq.
  destruct Heq as (Ha, Hla).
  destruct j; simpl; [ rewrite Ha, fld_mul_0_l; reflexivity | idtac ].
  apply IHla; assumption.

 apply IHlen; assumption.
Qed.

Lemma lap_eq_nil_lap_convol_mul_nil_r : ∀ α (f : field α) la lb i len,
  lap_eq f lb []
  → lap_eq f (lap_convol_mul f la lb i len) [].
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

  apply lap_eq_cons_nil_inv in Heq.
  destruct Heq as (Hb, Hlb).
  destruct h; simpl; [ rewrite Hb, fld_mul_0_r; reflexivity | idtac ].
  apply IHlb; assumption.

 apply IHlen; assumption.
Qed.

Lemma list_nth_fld_eq : ∀ α (f : field α) la lb n,
  lap_eq f la lb → (List.nth n la .0 f .= f List.nth n lb .0 f)%K.
Proof.
intros α f la lb n Hlab.
revert lb n Hlab.
induction la as [| a]; intros.
 revert n.
 induction lb as [| b]; intros; [ reflexivity | simpl ].
 apply lap_eq_nil_cons_inv in Hlab.
 destruct Hlab as (Hb, Hlb).
 symmetry in Hb.
 destruct n; [ assumption | idtac ].
 rewrite <- IHlb; [ destruct n; reflexivity | assumption ].

 revert n.
 induction lb as [| b]; intros.
  simpl.
  apply lap_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Ha, Hla).
  destruct n; [ assumption | idtac ].
  rewrite IHla; [ idtac | eassumption ].
  destruct n; reflexivity.

  apply lap_eq_cons_inv in Hlab.
  destruct Hlab as (Hab, Hlab).
  destruct n; [ assumption | simpl ].
  apply IHla; assumption.
Qed.

Add Parametric Morphism α (f : field α) : (lap_convol_mul f)
  with signature lap_eq f ==> lap_eq f ==> eq ==> eq ==> lap_eq f
  as lap_convol_mul_morph.
Proof.
intros la lb Hlab lc ld Hlcd i len.
revert la lb lc ld Hlab Hlcd i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen; assumption ].
apply summation_compat; intros j (_, Hj).
apply fld_mul_compat; apply list_nth_fld_eq; assumption.
Qed.

Lemma lap_convol_mul_succ : ∀ α (f : field α) la lb i len,
  lap_eq f
    (lap_convol_mul f la lb i (S len))
    (lap_convol_mul f la lb i len ++
     [Σ f (j = 0, i + len),
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

Lemma lap_eq_app_0s : ∀ α (f : field α) la lb,
  List.Forall (λ b, b .= f .0 f)%K lb
  → lap_eq f la (la ++ lb).
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

Lemma lap_convol_mul_more : ∀ α (f : field α) la lb i n,
  lap_eq f (lap_convol_mul f la lb i (pred (length la + length lb)))
    (lap_convol_mul f la lb i (pred (length la + length lb) + n)).
Proof.
intros α f la lb i n.
induction n; [ rewrite Nat.add_0_r; reflexivity | idtac ].
rewrite Nat.add_succ_r.
rewrite lap_convol_mul_succ.
rewrite IHn.
apply lap_eq_app_0s.
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

Add Parametric Morphism α (f : field α) : (lap_mul f)
  with signature lap_eq f ==> lap_eq f ==> lap_eq f
  as lap_mul_morph.
Proof.
intros a c Hac b d Hbd.
unfold lap_mul; simpl.
do 2 rewrite lap_convol_mul_more.
rewrite Hac, Hbd in |- * at 1.
rewrite Nat.add_comm.
reflexivity.
Qed.

Add Parametric Morphism α (f : field α) : (poly_mul f)
  with signature (eq_poly f) ==> (eq_poly f) ==> (eq_poly f)
  as poly_mul_morph.
Proof.
intros a c Hac b d Hbd.
unfold eq_poly, poly_mul, lap_mul; simpl.
unfold eq_poly in Hac, Hbd.
remember (al a) as la.
remember (al b) as lb.
remember (al c) as lc.
remember (al d) as ld.
revert Hac Hbd; clear; intros.
do 2 rewrite lap_convol_mul_more.
rewrite Hac, Hbd in |- * at 1.
rewrite Nat.add_comm.
reflexivity.
Qed.

Add Parametric Morphism α (f : field α) : (@cons α)
  with signature fld_eq f ==> lap_eq f ==> lap_eq f
  as cons_lap_eq_morph.
Proof.
intros a b H la lb Hab.
constructor; assumption.
Qed.

Lemma list_nth_lap_eq : ∀ α (f : field α) la lb,
  (∀ i, List.nth i la .0 f .= f List.nth i lb .0 f)%K
  → lap_eq f la lb.
Proof.
intros α f la lb Hi.
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

(* test
Load Q_field.
Definition Qtest_comp := lap_compose Q_field.
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

Lemma lap_add_nil_l : ∀ α (f : field α) la,
  lap_eq f (lap_add f [] la) la.
Proof. intros α f la; destruct la; reflexivity. Qed.

Lemma lap_add_nil_r : ∀ α (f : field α) la,
  lap_eq f (lap_add f la []) la.
Proof. intros α f la; destruct la; reflexivity. Qed.

Lemma lap_mul_nil_l : ∀ α (f : field α) la, lap_eq f (lap_mul f [] la) [].
Proof. intros α f la; apply lap_convol_mul_nil_l. Qed.

Lemma lap_mul_nil_r : ∀ α (f : field α) la, lap_eq f (lap_mul f la []) [].
Proof. intros α f la; apply lap_convol_mul_nil_r. Qed.

Lemma lap_add_compat : ∀ α (f : field α) a b c d,
  lap_eq f a c
  → lap_eq f b d
    → lap_eq f (lap_add f a b) (lap_add f c d).
Proof.
intros α f a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Lemma lap_mul_compat : ∀ α (f : field α) a b c d,
  lap_eq f a c
  → lap_eq f b d
    → lap_eq f (lap_mul f a b) (lap_mul f c d).
Proof.
intros α f a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Add Parametric Morphism α (f : field α) : (lap_compose f)
  with signature lap_eq f ==> lap_eq f ==> lap_eq f
  as lap_compose_morph.
Proof.
intros la lb Hlab lc ld Hlcd.
revert lb lc ld Hlab Hlcd.
induction la as [| a]; intros.
 induction lb as [| b]; [ reflexivity | simpl ].
 apply lap_eq_nil_cons_inv in Hlab.
 destruct Hlab as (Hb, Hlb).
 simpl in IHlb.
 assert (lap_eq f [b] []) as H by (rewrite Hb; constructor; reflexivity).
 rewrite H; clear H.
 rewrite lap_add_nil_r.
 rewrite <- IHlb; [ rewrite lap_mul_nil_l; reflexivity | assumption ].

 simpl.
 destruct lb as [| b]; simpl.
  apply lap_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Ha, Hla).
  assert (lap_eq f [a] []) as H by (rewrite Ha; constructor; reflexivity).
  rewrite H; clear H.
  rewrite lap_add_nil_r.
  rewrite IHla; try eassumption; simpl.
  rewrite lap_mul_nil_l; reflexivity.

  apply lap_eq_cons_inv in Hlab.
  destruct Hlab as (Hab, Hlab).
  rewrite Hab.
  rewrite IHla; try eassumption.
  apply lap_add_compat; [ idtac | reflexivity ].
  apply lap_mul_compat; [ idtac | assumption ].
  reflexivity.
Qed.

Add Parametric Morphism α (K : field α) : (poly_compose K)
  with signature eq_poly K ==> eq_poly K ==> eq_poly K
  as poly_compose_morph.
Proof.
intros A C HAC B D HBD.
unfold eq_poly; simpl.
rewrite HAC, HBD; reflexivity.
Qed.

Section poly.

Variable α : Type.
Variable f : field α.

(* addition theorems *)

Theorem poly_add_compat : ∀ a b c d,
  (a .= f c)%pol
  → (b .= f d)%pol
    → (a .+ f b .= f c .+ f d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Lemma lap_add_comm : ∀ al₁ al₂,
  lap_eq f (lap_add f al₁ al₂) (lap_add f al₂ al₁).
Proof.
intros al₁ al₂.
revert al₂.
induction al₁; intros.
 destruct al₂; [ apply lap_eq_refl | simpl ].
 constructor; [ reflexivity | apply lap_eq_refl ].

 destruct al₂.
  constructor; [ reflexivity | apply lap_eq_refl ].

  constructor; [ apply fld_add_comm | apply IHal₁ ].
Qed.

Theorem poly_add_comm : ∀ pol₁ pol₂, (pol₁ .+ f pol₂ .= f pol₂ .+ f pol₁)%pol.
Proof.
intros pol₁ pol₂.
unfold eq_poly.
eapply lap_add_comm; reflexivity.
Qed.

Lemma lap_add_assoc : ∀ al₁ al₂ al₃,
  lap_eq f (lap_add f (lap_add f al₁ al₂) al₃)
    (lap_add f al₁ (lap_add f al₂ al₃)).
Proof.
intros al₁ al₂ al₃.
revert al₂ al₃.
induction al₁; intros.
 destruct al₂.
  destruct al₃; [ apply lap_eq_refl | idtac ].
  constructor; [ reflexivity | apply lap_eq_refl ].

  destruct al₃; simpl.
   constructor; [ reflexivity | apply lap_eq_refl ].

   constructor; [ reflexivity | apply lap_eq_refl ].

 destruct al₂.
  destruct al₃; simpl.
   constructor; [ reflexivity | apply lap_eq_refl ].

   constructor; [ reflexivity | apply lap_eq_refl ].

  destruct al₃; simpl.
   constructor; [ reflexivity | apply lap_eq_refl ].

   constructor; [ symmetry; apply fld_add_assoc | apply IHal₁ ].
Qed.

Lemma poly_add_assoc : ∀ pol₁ pol₂ pol₃,
  ((pol₁ .+ f pol₂) .+ f pol₃ .= f pol₁ .+ f (pol₂ .+ f pol₃))%pol.
Proof.
intros pol₁ pol₂ pol₃.
unfold eq_poly.
eapply lap_add_assoc; reflexivity.
Qed.

Lemma lap_add_shuffle0 : ∀ la lb lc,
  lap_eq f (lap_add f (lap_add f la lb) lc)
     (lap_add f (lap_add f la lc) lb).
Proof.
intros la lb lc.
do 2 rewrite lap_add_assoc.
apply lap_add_compat; [ reflexivity | simpl ].
apply lap_add_comm.
Qed.

Lemma length_lap_add : ∀ la lb,
  length (lap_add f la lb) = max (length la) (length lb).
Proof.
intros la lb.
revert lb.
induction la as [| a]; intros; [ reflexivity | simpl ].
destruct lb as [| b]; [ reflexivity | simpl ].
rewrite IHla; reflexivity.
Qed.

(* multiplication theorems *)

Theorem poly_mul_compat : ∀ a b c d,
  (a .= f c)%pol
  → (b .= f d)%pol
    → (a .* f b .= f c .* f d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Lemma lap_mul_comm : ∀ a b, lap_eq f (lap_mul f a b) (lap_mul f b a).
Proof.
intros a b.
unfold lap_mul.
rewrite lap_convol_mul_comm, Nat.add_comm; reflexivity.
Qed.

Theorem poly_mul_comm : ∀ a b, (a .* f b .= f b .* f a)%pol.
Proof.
intros a b.
unfold eq_poly; simpl.
unfold lap_mul; simpl.
rewrite Nat.add_comm.
rewrite lap_convol_mul_comm; reflexivity.
Qed.

Lemma list_nth_lap_convol_mul_aux : ∀ la lb n i len,
  pred (List.length la + List.length lb) = (i + len)%nat
  → (List.nth n (lap_convol_mul f la lb i len) .0 f%K .= f
     Σ f (j = 0, n + i),
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

Lemma list_nth_lap_convol_mul : ∀ la lb i len,
  len = pred (length la + length lb)
  → (List.nth i (lap_convol_mul f la lb 0 len) .0 f .= f
     Σ f (j = 0, i), List.nth j la .0 f .* f List.nth (i - j) lb .0 f)%K.
Proof.
intros la lb i len Hlen.
symmetry in Hlen.
rewrite list_nth_lap_convol_mul_aux; [ idtac | assumption ].
rewrite Nat.add_0_r; reflexivity.
Qed.

Lemma summation_mul_list_nth_lap_convol_mul : ∀ la lb lc k,
  (Σ f (i = 0, k),
     List.nth i la .0 f .* f
     List.nth (k - i)
       (lap_convol_mul f lb lc 0 (pred (length lb + length lc))) 
       .0 f .= f
   Σ f (i = 0, k),
     List.nth i la .0 f .* f
     Σ f (j = 0, k - i),
       List.nth j lb .0 f .* f List.nth (k - i - j) lc .0 f)%K.
Proof.
intros la lb lc k.
apply summation_compat; intros i (_, Hi).
apply fld_mul_compat_l.
rewrite list_nth_lap_convol_mul; reflexivity.
Qed.

Lemma summation_mul_list_nth_lap_convol_mul_2 : ∀ la lb lc k,
   (Σ f (i = 0, k),
      List.nth i lc .0 f .* f
      List.nth (k - i)
        (lap_convol_mul f la lb 0 (pred (length la + length lb)))  .0 f .= f
    Σ f (i = 0, k),
      List.nth (k - i) lc .0 f .* f
      Σ f (j = 0, i),
        List.nth j la .0 f .* f List.nth (i - j) lb .0 f)%K.
Proof.
intros la lb lc k.
rewrite summation_rtl.
apply summation_compat; intros i (_, Hi).
rewrite Nat.add_0_r.
apply fld_mul_compat_l.
rewrite Nat_sub_sub_distr; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub.
apply list_nth_lap_convol_mul; reflexivity.
Qed.

(* inspired from series_mul_assoc *)
Lemma lap_mul_assoc : ∀ la lb lc,
  lap_eq f (lap_mul f la (lap_mul f lb lc))
    (lap_mul f (lap_mul f la lb) lc).
Proof.
intros la lb lc.
symmetry; rewrite lap_mul_comm.
unfold lap_mul.
apply list_nth_lap_eq; intros k.
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
rewrite summation_mul_list_nth_lap_convol_mul_2; symmetry.
rewrite summation_mul_list_nth_lap_convol_mul; symmetry.
rewrite <- summation_summation_mul_swap.
rewrite <- summation_summation_mul_swap.
rewrite summation_summation_exch.
rewrite summation_summation_shift.
apply summation_compat; intros i Hi.
apply summation_compat; intros j Hj.
rewrite fld_mul_comm, fld_mul_assoc.
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm, Nat.sub_add_distr.
reflexivity.
Qed.

Lemma poly_mul_assoc : ∀ P Q R,
  (P .* f (Q .* f R) .= f (P .* f Q) .* f R)%pol.
Proof.
intros P Q R.
apply lap_mul_assoc.
Qed.

Lemma lap_mul_shuffle0 : ∀ la lb lc,
  lap_eq f (lap_mul f (lap_mul f la lb) lc) (lap_mul f (lap_mul f la lc) lb).
Proof.
intros la lb lc.
do 2 rewrite <- lap_mul_assoc.
apply lap_mul_compat; [ reflexivity | apply lap_mul_comm ].
Qed.

Lemma lap_eq_skipn_succ : ∀ cl i,
  lap_eq f [List.nth i cl .0 f%K … List.skipn (S i) cl] (List.skipn i cl).
Proof.
intros cl i.
revert i.
induction cl as [| c]; intros; simpl.
 destruct i; constructor; reflexivity.

 destruct i; [ reflexivity | apply IHcl ].
Qed.

Lemma lap_convol_mul_1_l : ∀ cl i len,
  length cl = (i + len)%nat
  → lap_eq f (lap_convol_mul f [.1 f%K] cl i len) (List.skipn i cl).
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
  apply lap_eq_skipn_succ.

  intros j (Hj, Hji).
  destruct j; [ exfalso; omega | idtac ].
  destruct j; rewrite fld_mul_0_l; reflexivity.
Qed.

Lemma lap_convol_mul_x_l : ∀ cl i len,
  length cl = (i + len)%nat
  → lap_eq f
      (lap_convol_mul f [.0 f%K; .1 f%K … []] cl (S i) len)
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
  apply lap_eq_skipn_succ.

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
unfold lap_mul; simpl.
rewrite lap_convol_mul_1_l; reflexivity.
Qed.

Theorem poly_mul_1_r : ∀ a, (a .* f .1 f .= f a)%pol.
Proof.
intros a.
rewrite poly_mul_comm.
apply poly_mul_1_l.
Qed.

Fixpoint lap_convol_mul_add al₁ al₂ al₃ i len :=
  match len with
  | O => []
  | S len₁ =>
      [Σ f (j = 0, i),
       List.nth j al₁ .0 f .* f
       (List.nth (i - j) al₂ .0 f .+ f List.nth (i - j) al₃ .0 f) …
       lap_convol_mul_add al₁ al₂ al₃ (S i) len₁]
  end.

(* *)

Lemma list_nth_add : ∀ k la lb,
  (List.nth k (lap_add f la lb) .0 f .= f
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

Lemma lap_convol_mul_lap_add : ∀ la lb lc i len,
  lap_eq f
    (lap_convol_mul f la (lap_add f lb lc) i len)
    (lap_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
apply summation_compat; intros j (_, Hj).
apply fld_mul_compat_l.
rewrite list_nth_add; reflexivity.
Qed.

Lemma lap_add_lap_convol_mul : ∀ la lb lc i len,
   lap_eq f
     (lap_add f
        (lap_convol_mul f la lb i len)
        (lap_convol_mul f la lc i len))
     (lap_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite <- summation_add_distr.
apply summation_compat; intros j (_, Hj).
rewrite fld_mul_add_distr_l; reflexivity.
Qed.

Lemma lap_mul_add_distr_l : ∀ la lb lc,
  lap_eq f (lap_mul f la (lap_add f lb lc))
    (lap_add f (lap_mul f la lb) (lap_mul f la lc)).
Proof.
intros la lb lc.
unfold lap_mul.
remember (pred (length la + length (lap_add f lb lc))) as labc.
remember (pred (length la + length lb)) as lab.
remember (pred (length la + length lc)) as lac.
rewrite Heqlabc.
rewrite lap_convol_mul_more with (n := (lab + lac)%nat).
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite lap_convol_mul_more with (n := (labc + lac)%nat).
rewrite <- Heqlab.
rewrite lap_add_comm.
rewrite Heqlac.
rewrite lap_convol_mul_more with (n := (labc + lab)%nat).
rewrite <- Heqlac.
rewrite Nat.add_comm.
rewrite lap_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite lap_convol_mul_lap_add.
rewrite lap_add_lap_convol_mul.
reflexivity.
Qed.

Lemma lap_mul_add_distr_r : ∀ la lb lc,
  lap_eq f (lap_mul f (lap_add f la lb) lc)
    (lap_add f (lap_mul f la lc) (lap_mul f lb lc)).
Proof.
intros la lb lc.
rewrite lap_mul_comm, lap_mul_add_distr_l, lap_mul_comm.
apply lap_add_compat; [ reflexivity | apply lap_mul_comm ].
Qed.

Lemma poly_mul_add_distr_l : ∀ P Q R,
  (P .* f (Q .+ f R) .= f P .* f Q .+ f P .* f R)%pol.
Proof.
intros P Q R.
apply lap_mul_add_distr_l.
Qed.

Lemma poly_mul_add_distr_r : ∀ P Q R,
  ((P .+ f Q) .* f R .= f P .* f R .+ f Q .* f R)%pol.
Proof.
intros P Q R.
apply lap_mul_add_distr_r.
Qed.

Lemma lap_convol_mul_1_r : ∀ la i len,
  (i + len = length la)%nat
  → lap_eq f (lap_convol_mul f la [.1 f%K] i len) (List.skipn i la).
Proof.
intros la i len Hlen.
revert la i Hlen.
induction len; intros; simpl.
 rewrite Nat.add_0_r in Hlen; subst i.
 rewrite list_skipn_overflow; reflexivity.

 rewrite summation_rtl.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite Nat.add_0_r, Nat.sub_0_r.
 rewrite Nat.sub_diag; simpl.
 rewrite fld_mul_1_r.
 rewrite all_0_summation_0.
  rewrite fld_add_0_r.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
  rewrite IHlen; [ idtac | assumption ].
  apply lap_eq_skipn_succ.

  intros j (Hj, Hji).
  rewrite Nat_sub_sub_distr; [ idtac | assumption ].
  rewrite Nat.add_comm, Nat.add_sub.
  destruct j; [ exfalso; omega | idtac ].
  destruct j; rewrite fld_mul_0_r; reflexivity.
Qed.

Lemma lap_mul_1_l : ∀ la, lap_eq f (lap_mul f [.1 f%K] la) la.
Proof.
intros la.
unfold lap_mul.
apply lap_convol_mul_1_l; simpl.
reflexivity.
Qed.

Lemma lap_mul_1_r : ∀ la, lap_eq f (lap_mul f la [.1 f%K]) la.
Proof.
intros la.
unfold lap_mul.
apply lap_convol_mul_1_r; simpl.
rewrite Nat.add_comm; reflexivity.
Qed.

Lemma length_lap_mul : ∀ la lb,
  length (lap_mul f la lb) = pred (length la + length lb).
Proof.
intros la lb.
unfold lap_mul.
remember (pred (length la + length lb)) as len.
remember 0%nat as i.
clear Heqlen Heqi.
revert i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; reflexivity.
Qed.

Lemma list_nth_convol_mul : ∀ la lb i k len,
  (i + len)%nat = pred (length la + length lb)
  → (List.nth k (lap_convol_mul f la lb i len) .0 f .= f
     Σ f (j = 0, i + k),
     List.nth j la .0 f .* f List.nth (i + k - j) lb .0 f)%K.
Proof.
intros la lb i k len Hilen.
revert la lb i k Hilen.
induction len; intros; simpl.
 rewrite match_id; simpl.
 rewrite all_0_summation_0; [ reflexivity | simpl ].
 intros j (_, Hj).
 destruct (lt_dec j (length la)) as [Hja| Hja].
  destruct (lt_dec (i + k - j) (length lb)) as [Hjb| Hjb].
   exfalso; omega.

   apply fld_mul_eq_0; right.
   apply Nat.nlt_ge in Hjb.
   rewrite List.nth_overflow; [ reflexivity | assumption ].

  apply fld_mul_eq_0; left.
  apply Nat.nlt_ge in Hja.
  rewrite List.nth_overflow; [ reflexivity | assumption ].

 destruct k; [ rewrite Nat.add_0_r; reflexivity | idtac ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hilen.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 apply IHlen; assumption.
Qed.

Lemma list_nth_lap_mul : ∀ la lb k,
  (List.nth k (lap_mul f la lb) .0 f .= f
   Σ f (i = 0, k), List.nth i la .0 f .* f List.nth (k - i) lb .0 f)%K.
Proof.
intros la lb k.
apply list_nth_convol_mul; reflexivity.
Qed.

(* compose theorems *)

Lemma lap_mul_fold_add_distr : ∀ β la li (g : β → list α) x,
  lap_eq f
    (lap_mul f x (List.fold_right (λ i accu, lap_add f accu (g i)) la li))
    (List.fold_right (λ i accu, lap_add f accu (lap_mul f x (g i)))
       (lap_mul f x la) li).
Proof.
intros uβ la li g x.
revert la x.
induction li as [| j]; intros; [ reflexivity | simpl ].
rewrite lap_mul_add_distr_l.
rewrite IHli; reflexivity.
Qed.

Lemma list_fold_right_seq : ∀ g h la lb s t len,
  lap_eq f la lb
  → (∀ x y z, lap_eq f y z → lap_eq f (g x y) (g x z))
    → (∀ i accu, lap_eq f (g (s + i)%nat accu) (h (t + i)%nat accu))
      → lap_eq f
          (List.fold_right g la (List.seq s len))
          (List.fold_right h lb (List.seq t len)).
Proof.
intros g h la lb s t len Hab Hg Hgh.
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

Lemma lap_compose_compose2 : ∀ la lb,
  lap_eq f (lap_compose f la lb) (lap_compose2 f la lb).
Proof.
intros la lb.
revert lb.
induction la as [| a]; intros; [ reflexivity | simpl ].
rewrite IHla.
symmetry; clear.
unfold lap_compose2.
rewrite lap_mul_comm.
rewrite lap_mul_fold_add_distr.
rewrite lap_add_comm.
remember [a] as aa; simpl; subst aa.
rewrite lap_add_comm.
apply lap_add_compat; [ apply lap_mul_1_r | idtac ].
apply list_fold_right_seq.
 rewrite lap_mul_nil_r; reflexivity.

 intros x y z Hyz.
 rewrite Hyz; reflexivity.

 intros i accu; simpl.
 apply lap_add_compat; [ reflexivity | simpl ].
 rewrite lap_mul_comm, <- lap_mul_assoc.
 apply lap_mul_compat; [ reflexivity | idtac ].
 apply lap_mul_comm.
Qed.

Lemma lap_compose_compat : ∀ la lb lc ld,
  lap_eq f la lc
  → lap_eq f lb ld
    → lap_eq f (lap_compose f la lb) (lap_compose f lc ld).
Proof.
intros la lb lc ld Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Theorem poly_compose_compat : ∀ a b c d,
  (a .= f c)%pol
  → (b .= f d)%pol
    → (poly_compose f a b .= f poly_compose f c  d)%pol.
Proof.
intros a b c d Hac Hbd.
apply lap_compose_compat; assumption.
Qed.

(* power *)

Lemma lap_power_add : ∀ la i j,
  lap_eq f (lap_power f la (i + j))
    (lap_mul f (lap_power f la i) (lap_power f la j)).
Proof.
intros la i j.
revert j.
induction i; intros; simpl.
 rewrite lap_mul_1_l; reflexivity.

 rewrite IHi, lap_mul_assoc; reflexivity.
Qed.

Lemma lap_power_mul : ∀ la lb n,
  lap_eq f
    (lap_power f (lap_mul f la lb) n)
    (lap_mul f (lap_power f la n) (lap_power f lb n)).
Proof.
intros la lb n.
revert la lb.
induction n; intros; simpl.
 rewrite lap_mul_1_l; reflexivity.

 rewrite IHn.
 do 2 rewrite <- lap_mul_assoc.
 apply lap_mul_compat; [ reflexivity | idtac ].
 do 2 rewrite lap_mul_assoc.
 apply lap_mul_compat; [ idtac | reflexivity ].
 apply lap_mul_comm.
Qed.

Lemma length_lap_power : ∀ la n,
  la ≠ []
  → length (lap_power f la n) = S (n * pred (length la)).
Proof.
intros la n Hla.
induction n; [ reflexivity | simpl ].
rewrite length_lap_mul; simpl.
rewrite IHn; simpl.
rewrite Nat.add_succ_r; simpl.
rewrite <- Nat.add_succ_l.
destruct la; [ exfalso; apply Hla; reflexivity | reflexivity ].
Qed.

Lemma list_nth_pad_lt : ∀ i s (v : α) cl d,
  (i < s)%nat
  → List.nth i (list_pad s v cl) d = v.
Proof.
intros i s v cl d His.
revert i His.
induction s; intros.
 exfalso; revert His; apply lt_n_0.

 simpl.
 destruct i; [ reflexivity | idtac ].
 apply IHs, lt_S_n; assumption.
Qed.

Lemma list_nth_pad_sub : ∀ i s (v : α) cl d,
  (s ≤ i)%nat
  → List.nth i (list_pad s v cl) d = List.nth (i - s) cl d.
Proof.
intros i s v cl d Hsi.
revert i Hsi.
induction s; intros; [ rewrite Nat.sub_0_r; reflexivity | simpl ].
destruct i; [ exfalso; revert Hsi; apply Nat.nle_succ_0 | idtac ].
apply le_S_n in Hsi.
rewrite Nat.sub_succ.
apply IHs; assumption.
Qed.

Lemma lap_power_x : ∀ n,
  lap_eq f (lap_power f [.0 f; .1 f … []] n)%K (list_pad n .0 f [.1 f])%K.
Proof.
intros n.
apply list_nth_lap_eq; intros i.
destruct (lt_dec i n) as [Hin| Hin].
 rewrite list_nth_pad_lt; [ idtac | assumption ].
 revert i Hin.
 induction n; intros; [ exfalso; revert Hin; apply Nat.nlt_0_r | simpl ].
 destruct i; simpl.
  unfold summation; simpl.
  rewrite fld_mul_0_l, fld_add_0_l; reflexivity.

  apply lt_S_n in Hin.
  rewrite length_lap_power; [ idtac | intros H; discriminate H ].
  unfold length; rewrite Nat.mul_1_r.
  rewrite list_nth_convol_mul.
   rewrite all_0_summation_0; [ reflexivity | idtac ].
   intros j (_, Hj).
   destruct (lt_dec (1 + i - j) n) as [Hijn| Hijn].
    rewrite IHn; [ idtac | assumption ].
    rewrite fld_mul_0_r; reflexivity.

    apply Nat.nlt_ge in Hijn.
    destruct j; [ rewrite fld_mul_0_l; reflexivity | idtac ].
    exfalso; fast_omega Hin Hijn.

   rewrite length_lap_power; [ simpl | intros H; discriminate H ].
   rewrite Nat.mul_1_r; reflexivity.

 apply Nat.nlt_ge in Hin.
 rewrite list_nth_pad_sub; [ idtac | assumption ].
 destruct (eq_nat_dec n i) as [Heq| Hne].
  subst i; clear Hin.
  rewrite Nat.sub_diag.
  remember S as g; simpl; subst g.
  induction n; [ reflexivity | simpl ].
  rewrite length_lap_power; [ idtac | intros H; discriminate H ].
  unfold length; rewrite Nat.mul_1_r.
  rewrite list_nth_convol_mul.
   rewrite summation_only_one_non_0 with (v := 1%nat).
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite IHn; simpl.
    rewrite fld_mul_1_r; reflexivity.

    split; [ apply Nat.le_0_l | apply le_n_S, Nat.le_0_l ].

    intros i (_, Hin) Hi.
    destruct i; [ rewrite fld_mul_0_l; reflexivity | simpl ].
    destruct i; [ exfalso; apply Hi; reflexivity | idtac ].
    rewrite match_id, fld_mul_0_l; reflexivity.

   rewrite length_lap_power; [ simpl | intros H; discriminate H ].
   rewrite Nat.mul_1_r; reflexivity.

  apply le_neq_lt in Hin; [ idtac | assumption ].
  symmetry.
  rewrite List.nth_overflow; [ idtac | simpl; omega ].
  symmetry; clear Hne.
  revert i Hin.
  induction n; intros.
   simpl.
   destruct i; [ exfalso; revert Hin; apply Nat.lt_irrefl | idtac ].
   rewrite match_id; reflexivity.

   destruct i.
    exfalso; revert Hin; apply Nat.nlt_0_r.

    apply lt_S_n in Hin.
    simpl.
    rewrite length_lap_power; [ idtac | intros H; discriminate H ].
    remember S as g; simpl; subst g.
    rewrite Nat.mul_1_r.
    rewrite list_nth_convol_mul.
     rewrite all_0_summation_0; [ reflexivity | idtac ].
     intros j (_, Hj).
     destruct j; [ rewrite fld_mul_0_l; reflexivity | simpl ].
     destruct j.
      rewrite Nat.sub_0_r.
      rewrite IHn; [ idtac | assumption ].
      rewrite fld_mul_0_r; reflexivity.

      rewrite match_id, fld_mul_0_l; reflexivity.

     rewrite length_lap_power; [ simpl | intros H; discriminate H ].
     rewrite Nat.mul_1_r; reflexivity.
Qed.

Lemma lap_mul_cons_l : ∀ a la lb,
  lap_eq f (lap_mul f [a … la] lb)
    (lap_add f (lap_mul f [a] lb) [.0 f%K … lap_mul f la lb]).
Proof.
intros a la lb.
unfold lap_mul.
apply list_nth_lap_eq; intros k.
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
rewrite list_nth_add.
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
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
  rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
  rewrite summation_succ_succ; reflexivity.

  intros i (Hi, Hik); simpl.
  destruct i; [ exfalso; omega | simpl ].
  destruct i; rewrite fld_mul_0_l; reflexivity.
Qed.

Lemma lap_mul_cons_r : ∀ la b lb,
  lap_eq f (lap_mul f la [b … lb])
    (lap_add f (lap_mul f la [b]) [.0 f%K … lap_mul f la lb]).
Proof.
intros la b lb.
rewrite lap_mul_comm.
rewrite lap_mul_cons_l.
rewrite lap_mul_comm.
apply lap_add_compat; [ reflexivity | idtac ].
rewrite lap_mul_comm; reflexivity.
Qed.

Lemma lap_eq_0 : lap_eq f [.0 f%K] [].
Proof. constructor; reflexivity. Qed.

Lemma lap_convol_mul_cons_succ : ∀ a b lb i len,
  lap_eq f (lap_convol_mul f [a] [b … lb] (S i) len)
    (lap_convol_mul f [a] lb i len).
Proof.
intros a b lb i len.
revert a b lb i.
induction len; intros; [ reflexivity | idtac ].
constructor; [ idtac | apply IHlen ].
rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
rewrite List.nth_overflow; [ idtac | simpl; fast_omega  ].
rewrite fld_mul_0_l, fld_add_0_r.
apply summation_compat; intros j (_, Hj).
apply fld_mul_compat_l.
rewrite Nat.sub_succ_l; [ reflexivity | assumption ].
Qed.

Lemma lap_mul_cons : ∀ a b la lb,
  lap_eq f (lap_mul f [a … la] [b … lb])
    [(a .* f b)%K
    … lap_add f (lap_add f (lap_mul f la [b]) (lap_mul f [a] lb))
        [.0 f%K … lap_mul f la lb]].
Proof.
intros a b la lb.
rewrite lap_mul_cons_l; simpl.
rewrite summation_only_one.
rewrite fld_add_0_r.
constructor; [ reflexivity | idtac ].
rewrite lap_mul_cons_r.
unfold lap_mul; simpl.
rewrite <- lap_add_assoc.
apply lap_add_compat; [ idtac | reflexivity ].
rewrite lap_add_comm.
apply lap_add_compat; [ reflexivity | idtac ].
apply lap_convol_mul_cons_succ.
Qed.

Lemma lap_mul_power : ∀ n la,
  lap_eq f
    (lap_mul f (lap_power f [.0 f; .1 f … []] n) la)%K
    (list_pad n .0 f la)%K.
Proof.
intros n la.
rewrite lap_power_x.
revert la.
induction n; intros; [ rewrite lap_mul_1_l; reflexivity | simpl ].
destruct la as [| a]; simpl.
 rewrite lap_mul_nil_r; simpl.
 constructor; [ reflexivity | idtac ].
 clear IHn; induction n; [ reflexivity | simpl ].
 constructor; [ reflexivity | assumption ].

 rewrite lap_mul_cons.
 rewrite fld_mul_0_l.
 constructor; [ reflexivity | simpl ].
 rewrite lap_eq_0, lap_mul_nil_l.
 rewrite lap_add_nil_r.
 do 2 rewrite IHn.
 clear.
 revert a la.
 induction n; intros; simpl.
  rewrite fld_add_0_r; reflexivity.

  rewrite fld_add_0_r.
  constructor; [ reflexivity | idtac ].
  apply IHn.
Qed.

Lemma nth_lap_power_id : ∀ n,
  (List.nth n (lap_power f [.0 f; .1 f … []] n) .0 f .= f .1 f)%K.
Proof.
intros n.
rewrite fold_list_nth_def_0.
rewrite lap_power_x.
unfold list_nth_def_0; simpl.
rewrite list_nth_pad_sub, Nat.sub_diag; reflexivity.
Qed.

Lemma nth_lap_power_lt : ∀ i n,
  (i < n)%nat
  → (List.nth i (lap_power f [.0 f; .1 f … []] n) .0 f .= f .0 f)%K.
Proof.
intros i n Hin.
Admitted.

(* *)

Lemma lap_fold_compat_l : ∀ A (g h : A → _) la lb l,
  lap_eq f la lb
  → lap_eq f
      (List.fold_right (λ v accu, lap_add f accu (lap_mul f (g v) (h v)))
         la l)
      (List.fold_right (λ v accu, lap_add f accu (lap_mul f (g v) (h v)))
         lb l).
Proof.
intros A g h la lb l Heq.
induction l; [ assumption | simpl; rewrite IHl; reflexivity ].
Qed.

End poly.

Add Parametric Morphism α (f : field α) : (lap_compose2 f)
  with signature lap_eq f ==> lap_eq f ==> lap_eq f
  as lap_compose2_morph.
Proof.
intros la lb Hlab lc ld Hlcd.
rewrite <- lap_compose_compose2.
rewrite <- lap_compose_compose2.
rewrite Hlab, Hlcd; reflexivity.
Qed.

(* Horner's algorithm *)
Definition horner α β γ
    (zero_c : α) (add_v_c : α → β → α) (mul_v_x : α → γ → α)
    (pol : polynomial β) (x : γ) :=
  List.fold_right (λ c accu, add_v_c (mul_v_x accu x) c) zero_c (al pol).
