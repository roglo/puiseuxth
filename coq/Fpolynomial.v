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

Fixpoint poly_add_loop α (f : field α) al₁ al₂ :=
  match al₁ with
  | [] => al₂
  | [a₁ … bl₁] =>
      match al₂ with
      | [] => al₁
      | [a₂ … bl₂] => [(a₁ .+ f a₂)%K … poly_add_loop f bl₁ bl₂]
      end
  end.

Definition poly_add α (f : field α) pol₁ pol₂ :=
  {| al := poly_add_loop f (al pol₁) (al pol₂) |}.

(* multiplication *)

Fixpoint poly_convol_mul α (f : field α) al₁ al₂ i len :=
  match len with
  | O => []
  | S len₁ =>
      [Σ f (j = 0, i) _ List.nth j al₁ .0 f .* f List.nth (i - j) al₂ .0 f …
       poly_convol_mul f al₁ al₂ (S i) len₁]
  end.

Definition poly_mul α (f : field α) pol₁ pol₂ :=
  {| al :=
       poly_convol_mul f (al pol₁) (al pol₂) O
         (pred (List.length (al pol₁) + List.length (al pol₂))) |}.

(* *)

Notation "a .+ f b" := (poly_add f a b) : poly_scope.
Notation "a .* f b" := (poly_mul f a b) : poly_scope.

Definition Pdivide α (f : field α) x y := ∃ z, (y .= f z .* f x)%pol.

Add Parametric Morphism α (f : field α) : (@al α)
  with signature eq_poly f ==> list_eq f
  as al_morph.
Proof. intros; assumption. Qed.

Lemma list_eq_nil_poly_add_loop_r : ∀ α (f : field α) la lb,
  list_eq f [] la
  → list_eq f lb (poly_add_loop f la lb).
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

Lemma list_eq_nil_poly_add_loop_l : ∀ α (f : field α) la lb,
  list_eq f [] lb
  → list_eq f la (poly_add_loop f la lb).
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

Add Parametric Morphism α (f : field α) : (poly_add_loop f)
  with signature (list_eq f) ==> (list_eq f) ==> (list_eq f)
  as poly_add_loop_morph.
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
   apply list_eq_nil_poly_add_loop_r; assumption.

   apply list_eq_cons_inv in Hbd.
   destruct Hbd as (Hbd, Hlbd).
   constructor; [ rewrite Hc, fld_add_0_l; assumption | idtac ].
   etransitivity; [ eassumption | idtac ].
   apply list_eq_nil_poly_add_loop_r; assumption.

 destruct lb as [| b].
  destruct lc as [| c]; [ etransitivity; eassumption | idtac ].
  destruct ld as [| d]; [ assumption | simpl ].
  apply list_eq_cons_inv in Hac.
  destruct Hac as (Hac, Hlac).
  apply list_eq_nil_cons_inv in Hbd.
  destruct Hbd as (Hd, Hld).
  constructor; [ rewrite Hd, fld_add_0_r; assumption | idtac ].
  etransitivity; [ eassumption | idtac ].
  apply list_eq_nil_poly_add_loop_l; assumption.

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

Lemma poly_convol_mul_comm : ∀ α (f : field α) l₁ l₂ i len,
  list_eq f (poly_convol_mul f l₁ l₂ i len) (poly_convol_mul f l₂ l₁ i len).
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

Lemma poly_convol_mul_nil_l : ∀ α (f : field α) l i len,
  list_eq f (poly_convol_mul f [] l i len) [].
Proof.
intros α f l i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite all_0_summation_0; [ reflexivity | idtac ].
intros k (_, Hk).
destruct k; rewrite fld_mul_0_l; reflexivity.
Qed.

Lemma poly_convol_mul_nil_r : ∀ α (f : field α) l i len,
  list_eq f (poly_convol_mul f l [] i len) [].
Proof.
intros α f l i len.
rewrite poly_convol_mul_comm.
apply poly_convol_mul_nil_l.
Qed.

Lemma poly_convol_mul_compat : ∀ α (f : field α) la lb lc ld i len,
  list_eq f la lc
  → list_eq f lb ld
    → list_eq f (poly_convol_mul f la lb i len)
        (poly_convol_mul f lc ld i len).
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

Lemma list_eq_nil_poly_convol_mul_nil_l : ∀ α (f : field α) la lb i len,
  list_eq f la []
  → list_eq f (poly_convol_mul f la lb i len) [].
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

Lemma list_eq_nil_poly_convol_mul_nil_r : ∀ α (f : field α) la lb i len,
  list_eq f lb []
  → list_eq f (poly_convol_mul f la lb i len) [].
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

Add Parametric Morphism α (f : field α) : (poly_convol_mul f)
  with signature (list_eq f) ==> (list_eq f) ==> eq ==> eq ==> (list_eq f)
  as poly_convol_mul_morph.
Proof.
intros la lc Hac lb ld Hbd i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
apply summation_compat; intros j (_, Hj).
apply fld_mul_compat; apply list_eq_list_nth; assumption.
Qed.

Lemma poly_convol_mul_succ : ∀ α (f : field α) la lb i len,
  list_eq f
    (poly_convol_mul f la lb i (S len))
    (poly_convol_mul f la lb i len ++
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

Lemma poly_convol_mul_more : ∀ α (f : field α) la lb i n,
  list_eq f (poly_convol_mul f la lb i (pred (length la + length lb)))
    (poly_convol_mul f la lb i (pred (length la + length lb) + n)).
Proof.
intros α f la lb i n.
induction n; [ rewrite Nat.add_0_r; reflexivity | idtac ].
rewrite Nat.add_succ_r.
rewrite poly_convol_mul_succ.
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

Add Parametric Morphism α (f : field α) : (poly_mul f)
  with signature (eq_poly f) ==> (eq_poly f) ==> (eq_poly f)
  as poly_mul_morph.
Proof.
intros a c Hac b d Hbd.
unfold eq_poly, poly_mul; simpl.
unfold eq_poly in Hac, Hbd.
remember (al a) as la.
remember (al b) as lb.
remember (al c) as lc.
remember (al d) as ld.
revert Hac Hbd; clear; intros.
do 2 rewrite poly_convol_mul_more.
rewrite Hac, Hbd in |- * at 1.
rewrite Nat.add_comm.
reflexivity.
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

Lemma poly_add_loop_al_comm : ∀ al₁ al₂ rp₁ rp₂,
  rp₁ = poly_add_loop f al₁ al₂
  → rp₂ = poly_add_loop f al₂ al₁
    → list_eq f rp₁ rp₂.
Proof.
intros al₁ al₂ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
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
eapply poly_add_loop_al_comm; reflexivity.
Qed.

Lemma poly_add_loop_al_assoc : ∀ al₁ al₂ al₃ rp₁ rp₂,
  rp₁ = poly_add_loop f (poly_add_loop f al₁ al₂) al₃
  → rp₂ = poly_add_loop f al₁ (poly_add_loop f al₂ al₃)
    → list_eq f rp₁ rp₂.
Proof.
intros al₁ al₂ al₃ rp₁ rp₂ H₁ H₂.
subst rp₁ rp₂.
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
eapply poly_add_loop_al_assoc; reflexivity.
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

(*
Lemma yyy : ∀ cl i,
  list_eq f (poly_convol_mul f [.1 f%K] cl i (length cl - i))
    (List.skipn i cl).
Proof.
intros cl i.
bbb.
*)

Lemma zzz : ∀ cl i len,
  length cl ≤ len
  → list_eq f (poly_convol_mul f [.1 f%K] cl i len) (List.skipn i cl).
Proof.
intros cl i len Hlen.
revert i cl Hlen.
induction len; intros.
 simpl.
 apply Nat.le_0_r in Hlen.
 destruct cl; [ destruct i; reflexivity | discriminate Hlen ].

 simpl.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
bbb.
rewrite all_0_summation_0.

intros cl i len Hlen.
revert i cl Hlen.
induction len; intros.
 simpl.
 apply Nat.le_0_r in Hlen.
 destruct cl; [ destruct i; reflexivity | discriminate Hlen ].

 destruct cl as [| c].
  simpl.
  destruct i; simpl.
   constructor.
    rewrite summation_only_one.
    rewrite fld_mul_1_l; reflexivity.

    apply poly_convol_mul_nil_r.

   constructor.
    rewrite all_0_summation_0; [ reflexivity | idtac ].
    intros j (_, Hj).
    destruct j.
     rewrite fld_mul_1_l; reflexivity.

     destruct j; rewrite fld_mul_0_l; reflexivity.

    apply poly_convol_mul_nil_r.

  simpl.
  destruct i; simpl.
   constructor.
    rewrite summation_only_one.
    rewrite fld_mul_1_l; reflexivity.

    simpl in Hlen.
    apply Nat.succ_le_mono in Hlen.
bbb.

Theorem poly_mul_1_l : ∀ a, (.1 f .* f a .= f a)%pol.
Proof.
intros a.
unfold eq_poly; simpl.
remember (al a) as cl; clear.
replace (length cl) with (length cl - 0)%nat .
 rewrite yyy; reflexivity.

 rewrite Nat.sub_0_r; reflexivity.
bbb.

intros a.
unfold eq_poly; simpl.
remember (al a) as cl; clear.
destruct cl as [| c₁]; simpl; constructor.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite all_0_summation_0.
  rewrite fld_mul_1_l, fld_add_0_r; reflexivity.

  intros i (Hi₁, Hi₂).
  destruct i; [ exfalso; omega | idtac ].
  destruct i; rewrite fld_mul_0_l; reflexivity.

 destruct cl as [| c₂]; simpl; constructor.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite all_0_summation_0.
   rewrite fld_mul_1_l, fld_add_0_r; reflexivity.

   intros i (Hi₁, Hi₂).
   destruct i; [ exfalso; omega | idtac ].
   destruct i; rewrite fld_mul_0_l; reflexivity.

  destruct cl as [| c₃]; simpl; constructor.
   rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
   rewrite all_0_summation_0.
    rewrite fld_mul_1_l, fld_add_0_r; reflexivity.

    intros i (Hi₁, Hi₂).
    destruct i; [ exfalso; omega | idtac ].
    destruct i; rewrite fld_mul_0_l; reflexivity.
bbb.

End poly.

(* Horner's algorithm *)
Definition apply_poly α β γ
    (zero_c : α) (add_v_c : α → β → α) (mul_v_x : α → γ → α)
    (pol : polynomial β) (x : γ) :=
  List.fold_right (λ c accu, add_v_c (mul_v_x accu x) c) zero_c (al pol).
