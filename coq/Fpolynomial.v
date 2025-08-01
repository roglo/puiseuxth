(* Fpolynomial.v *)

(* polynomials on a ring *)

From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Morphisms Relations.

Require Import Misc.
Require Import Field2.
Require Import Fsummation.

Set Implicit Arguments.

(* lap : list as polynomial, i.e. the only field of the record in the
   definition of polynomial after *)

Inductive lap_eq {α} {r : ring α} : list α → list α → Prop :=
  | lap_eq_nil : lap_eq [] []
  | lap_eq_cons : ∀ x₁ x₂ l₁ l₂,
      (x₁ = x₂)%K
      → lap_eq l₁ l₂
        → lap_eq [x₁ … l₁] [x₂ … l₂]
  | lap_eq_cons_nil : ∀ x l,
      (x = 0)%K
      → lap_eq l []
        → lap_eq [x … l] []
  | lap_eq_nil_cons : ∀ x l,
      (x = 0)%K
      → lap_eq [] l
        → lap_eq [] [x … l].

Definition lap_zero {α} {r : ring α} := ([] : list α).
Definition lap_one {α} {r : ring α} := [1%K].

Theorem lap_eq_cons_inv : ∀ α (r : ring α) x₁ x₂ l₁ l₂,
  lap_eq [x₁ … l₁] [x₂ … l₂]
  → (x₁ = x₂)%K ∧ lap_eq l₁ l₂.
Proof.
intros α r x₁ x₂ l₁ l₂ H.
inversion H; split; assumption.
Qed.

Theorem lap_eq_cons_nil_inv : ∀ α (r : ring α) x l,
  lap_eq [x … l] []
  → (x = 0)%K ∧ lap_eq l [].
Proof.
intros α r x l H.
inversion H; split; assumption.
Qed.

Theorem lap_eq_nil_cons_inv : ∀ α (r : ring α) x l,
  lap_eq [] [x … l]
  → (x = 0)%K ∧ lap_eq [] l.
Proof.
intros α r x l H.
inversion H; split; assumption.
Qed.

Theorem lap_eq_refl {α} {r : ring α} : reflexive _ lap_eq.
Proof.
intros l.
induction l; constructor; [ reflexivity | assumption ].
Qed.

Theorem lap_eq_sym {α} {r : ring α} : symmetric _ lap_eq.
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

Theorem lap_eq_trans {α} {r : ring α} : transitive _ lap_eq.
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

Add Parametric Relation α (r : ring α) : (list α) lap_eq
 reflexivity proved by lap_eq_refl
 symmetry proved by lap_eq_sym
 transitivity proved by lap_eq_trans
 as lap_eq_rel.

Theorem lap_eq_list_fold_right : ∀ α (K : ring α) β g h x (l : list β),
  (∀ i a b, i ∈ l → lap_eq a b → lap_eq (g i a) (h i b))
  → lap_eq (List.fold_right g x l) (List.fold_right h x l).
Proof.
intros α K β g h x l H.
induction l as [| y]; intros; [ reflexivity | simpl ].
apply H; [ left; reflexivity | idtac ].
apply IHl; intros i a b Hi Heq.
apply H; [ right; assumption | assumption ].
Qed.

(* addition *)

Fixpoint lap_add {α} {r : ring α} al₁ al₂ :=
  match al₁ with
  | [] => al₂
  | [a₁ … bl₁] =>
      match al₂ with
      | [] => al₁
      | [a₂ … bl₂] => [(a₁ + a₂)%K … lap_add bl₁ bl₂]
      end
  end.

Definition lap_opp {α} {r : ring α} la := List.map rng_opp la.

(* multiplication *)

Fixpoint lap_convol_mul α (r : ring α) al₁ al₂ i len :=
  match len with
  | O => []
  | S len₁ =>
      [Σ (j = 0, i), (List.nth j al₁ 0 * List.nth (i - j) al₂ 0)%K …
       lap_convol_mul r al₁ al₂ (S i) len₁]
  end.

Definition lap_mul {α} {R : ring α} la lb :=
  lap_convol_mul R la lb 0 (pred (length la + length lb)).

(* power *)

Fixpoint lap_power {α} {r : ring α} la n :=
  match n with
  | O => [1%K]
  | S m => lap_mul la (lap_power la m)
  end.

(* composition *)

Definition lap_compose {α} {r : ring α} la lb :=
  List.fold_right (λ c accu, lap_add (lap_mul accu lb) [c]) [] la.

Definition lap_compose2 {α} {r : ring α} la lb :=
  List.fold_right
    (λ i accu,
     lap_add accu (lap_mul [List.nth i la 0] (lap_power lb i)))%K
    [] (List.seq 0 (length la)).

(* *)

Fixpoint list_pad α n (zero : α) rem :=
  match n with
  | O => rem
  | S n₁ => [zero … list_pad n₁ zero rem]
  end.

Declare Scope lap_scope.
Delimit Scope lap_scope with lap.
Notation "0" := lap_zero : lap_scope.
Notation "1" := lap_one : lap_scope.
Notation "- a" := (lap_opp a) : lap_scope.
Notation "a = b" := (lap_eq a b) : lap_scope.
Notation "a ≠ b" := (¬lap_eq a b) : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a - b" := (lap_add a (lap_opp b)) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.
Notation "a ^ b" := (lap_power a b) : lap_scope.

Definition list_nth_def_0 α {R : ring α} n l := List.nth n l 0%K.

(* *)

Global Instance list_nth_rng_morph α (R : ring α) :
  Proper (eq ==> lap_eq ==> rng_eq) (@list_nth_def_0 _ R).
Proof.
intros m n Hmn la lb Hab.
subst m.
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

Theorem lap_eq_nil_lap_add_r : ∀ α (r : ring α) la lb,
  lap_eq [] la
  → lap_eq lb (lap_add la lb).
Proof.
intros α r la lb H.
revert lb.
induction la as [| a]; intros; [ reflexivity | simpl ].
destruct lb as [| b]; [ assumption | idtac ].
apply lap_eq_nil_cons_inv in H.
destruct H as (Ha, Hla).
constructor; [ rewrite Ha, rng_add_0_l; reflexivity | idtac ].
apply IHla; assumption.
Qed.

Theorem lap_eq_nil_lap_add_l : ∀ α (r : ring α) la lb,
  lap_eq [] lb
  → lap_eq la (lap_add la lb).
Proof.
intros α r la lb H.
revert la.
induction lb as [| b]; intros; [ destruct la; reflexivity | idtac ].
destruct la as [| a]; [ assumption | simpl ].
apply lap_eq_nil_cons_inv in H.
destruct H as (Hb, Hlb).
constructor; [ rewrite Hb, rng_add_0_r; reflexivity | idtac ].
apply IHlb; assumption.
Qed.

Global Instance lap_add_morph α (r : ring α) : 
  Proper (lap_eq ==> lap_eq ==> lap_eq) lap_add.
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
   constructor; [ rewrite Hc, rng_add_0_l; assumption | idtac ].
   etransitivity; [ eassumption | idtac ].
   apply lap_eq_nil_lap_add_r; assumption.

   apply lap_eq_cons_inv in Hbd.
   destruct Hbd as (Hbd, Hlbd).
   constructor; [ rewrite Hc, rng_add_0_l; assumption | idtac ].
   etransitivity; [ eassumption | idtac ].
   apply lap_eq_nil_lap_add_r; assumption.

 destruct lb as [| b].
  destruct lc as [| c]; [ etransitivity; eassumption | idtac ].
  destruct ld as [| d]; [ assumption | simpl ].
  apply lap_eq_cons_inv in Hac.
  destruct Hac as (Hac, Hlac).
  apply lap_eq_nil_cons_inv in Hbd.
  destruct Hbd as (Hd, Hld).
  constructor; [ rewrite Hd, rng_add_0_r; assumption | idtac ].
  etransitivity; [ eassumption | idtac ].
  apply lap_eq_nil_lap_add_l; assumption.

  destruct lc as [| c].
   apply lap_eq_cons_nil_inv in Hac.
   destruct Hac as (Ha, Hla); simpl.
   destruct ld as [| d].
    apply lap_eq_cons_nil_inv in Hbd.
    destruct Hbd as (Hb, Hlb).
    constructor; [ rewrite Ha, rng_add_0_l; assumption | idtac ].
    rewrite IHla; try eassumption; reflexivity.

    apply lap_eq_cons_inv in Hbd.
    destruct Hbd as (Hbd, Hlbd).
    constructor; [ rewrite Ha, rng_add_0_l; assumption | idtac ].
    rewrite IHla; try eassumption; reflexivity.

   apply lap_eq_cons_inv in Hac.
   destruct Hac as (Hac, Hlac); simpl.
   destruct ld as [| d].
    apply lap_eq_cons_nil_inv in Hbd.
    destruct Hbd as (Hb, Hlb).
    constructor; [ rewrite Hb, rng_add_0_r; assumption | idtac ].
    rewrite IHla; try eassumption.
    destruct lc; reflexivity.

    apply lap_eq_cons_inv in Hbd.
    destruct Hbd as (Hbd, Hlbd).
    constructor; [ rewrite Hac, Hbd; reflexivity | apply IHla; assumption ].
Qed.

Theorem lap_convol_mul_comm : ∀ α (R : ring α) l₁ l₂ i len,
  lap_eq (lap_convol_mul R l₁ l₂ i len) (lap_convol_mul R l₂ l₁ i len).
Proof.
intros α R l₁ l₂ i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite summation_rtl.
apply summation_compat; intros j (_, Hj).
rewrite Nat.add_0_r.
rewrite rng_mul_comm.
apply rng_mul_compat; [ idtac | reflexivity ].
rewrite Nat_sub_sub_distr; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Theorem lap_convol_mul_nil_l : ∀ α (R : ring α) l i len,
  lap_eq (lap_convol_mul R [] l i len) [].
Proof.
intros α R l i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite all_0_summation_0; [ reflexivity | idtac ].
intros k (_, Hk).
destruct k; rewrite rng_mul_0_l; reflexivity.
Qed.

Theorem lap_convol_mul_nil_r : ∀ α (R : ring α) l i len,
  lap_eq (lap_convol_mul R l [] i len) [].
Proof.
intros α R l i len.
rewrite lap_convol_mul_comm.
apply lap_convol_mul_nil_l.
Qed.

Theorem list_nth_rng_eq : ∀ α (r : ring α) la lb n,
  lap_eq la lb → (List.nth n la 0 = List.nth n lb 0)%K.
Proof.
intros α r la lb n Hlab.
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

Global Instance lap_convol_mul_morph α (R : ring α) :
  Proper (lap_eq ==> lap_eq ==> eq ==> eq ==> lap_eq) (lap_convol_mul R).
Proof.
intros la lb Hlab lc ld Hlcd i j Hij len len' Hlen.
subst j len'.
revert la lb lc ld Hlab Hlcd i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen; assumption ].
apply summation_compat; intros j (_, Hj).
apply rng_mul_compat; apply list_nth_rng_eq; assumption.
Qed.

Theorem lap_convol_mul_succ : ∀ α (r : ring α) la lb i len,
  lap_eq
    (lap_convol_mul r la lb i (S len))
    (lap_convol_mul r la lb i len ++
     [Σ (j = 0, i + len),
      List.nth j la 0 * List.nth (i + len - j) lb 0])%K.
Proof.
intros α r la lb i len.
revert la lb i.
induction len; intros; simpl.
 rewrite Nat.add_0_r; reflexivity.

 constructor; [ reflexivity | idtac ].
 simpl in IHlen.
 rewrite IHlen.
 rewrite Nat.add_succ_r, Nat.add_succ_l.
 reflexivity.
Qed.

Theorem lap_eq_app_0s : ∀ α (r : ring α) la lb,
  List.Forall (λ b, b = 0)%K lb
  → lap_eq la (la ++ lb).
Proof.
intros α r la lb Hz.
induction la as [| a]; simpl.
 induction lb as [| b]; [ reflexivity | idtac ].
 constructor.
  apply list_Forall_inv in Hz; destruct Hz; assumption.

  apply IHlb.
  apply list_Forall_inv in Hz; destruct Hz; assumption.

 constructor; [ reflexivity | assumption ].
Qed.

Theorem lap_convol_mul_more : ∀ α (r : ring α) la lb i n,
  lap_eq (lap_convol_mul r la lb i (pred (length la + length lb)))
    (lap_convol_mul r la lb i (pred (length la + length lb) + n)).
Proof.
intros α r la lb i n.
induction n; [ rewrite Nat.add_0_r; reflexivity | idtac ].
rewrite Nat.add_succ_r.
rewrite lap_convol_mul_succ.
rewrite IHn.
apply lap_eq_app_0s.
constructor; [ idtac | constructor ].
apply all_0_summation_0.
intros j (_, Hj).
apply rng_mul_eq_0.
destruct (le_dec (length la) j) as [H₁| H₁].
 left.
 rewrite List.nth_overflow; [ reflexivity | assumption ].

 apply Nat.nle_gt in H₁.
 destruct (le_dec (length lb) (i + (pred (length la + length lb) + n) - j))
  as [H₂| H₂].
  right.
  rewrite List.nth_overflow; [ reflexivity | assumption ].

  exfalso; apply H₂; clear H₂.
  rewrite <- Nat.add_pred_l.
   apply Nat.lt_le_pred in H₁.
   apply Nat.le_add_le_sub_l.
   rewrite Nat.add_shuffle0, Nat.add_assoc.
   apply Nat.add_le_mono_r.
   rewrite Nat.add_comm, <- Nat.add_assoc.
   eapply Nat.le_trans; eauto .
   apply Nat.le_sub_le_add_l.
   rewrite Nat.sub_diag.
   apply Nat.le_0_l.

   intros H; rewrite H in H₁.
   revert H₁; apply Nat.nlt_0_r.
Qed.

Global Instance lap_mul_morph α (R : ring α) :
  Proper (lap_eq ==> lap_eq ==> lap_eq) (@lap_mul _ R).
Proof.
intros a c Hac b d Hbd.
unfold lap_mul; simpl.
do 2 rewrite lap_convol_mul_more.
rewrite Hac, Hbd in |- * at 1.
rewrite Nat.add_comm.
reflexivity.
Qed.

Global Instance lap_power_morph α (r : ring α) :
  Proper (lap_eq ==> eq ==> lap_eq) lap_power.
Proof.
intros la lb Hlab m n Hmn.
subst m.
induction n; [ reflexivity | simpl ].
rewrite IHn, Hlab; reflexivity.
Qed.

Global Instance cons_lap_eq_morph α (r : ring α) :
  Proper (rng_eq ==> lap_eq ==> lap_eq) (@cons α).
Proof.
intros a b H la lb Hab.
constructor; assumption.
Qed.

Theorem list_nth_lap_eq : ∀ α (r : ring α) la lb,
  (∀ i, (List.nth i la 0 = List.nth i lb 0)%K)
  → lap_eq la lb.
Proof.
intros α r la lb Hi.
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

Theorem lap_add_nil_l : ∀ α (r : ring α) la,
  lap_eq (lap_add [] la) la.
Proof. intros α r la; destruct la; reflexivity. Qed.

Theorem lap_add_nil_r : ∀ α (r : ring α) la,
  lap_eq (lap_add la []) la.
Proof. intros α r la; destruct la; reflexivity. Qed.

Theorem lap_mul_nil_l : ∀ α (r : ring α) la, lap_eq (lap_mul [] la) [].
Proof. intros α r la; apply lap_convol_mul_nil_l. Qed.

Theorem lap_mul_nil_r : ∀ α (r : ring α) la, lap_eq (lap_mul la []) [].
Proof. intros α r la; apply lap_convol_mul_nil_r. Qed.

Theorem lap_add_compat : ∀ α (r : ring α) a b c d,
  lap_eq a c
  → lap_eq b d
    → lap_eq (lap_add a b) (lap_add c d).
Proof.
intros α r a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Theorem lap_add_compat_l {α} {r : ring α} : ∀ a b c,
  lap_eq a b
  → lap_eq (lap_add c a) (lap_add c b).
Proof.
intros a b c Hab.
rewrite Hab; reflexivity.
Qed.

Theorem lap_mul_compat : ∀ α (r : ring α) a b c d,
  lap_eq a c
  → lap_eq b d
    → lap_eq (lap_mul a b) (lap_mul c d).
Proof.
intros α r a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Global Instance lap_compose_morph α (r : ring α) :
  Proper (lap_eq ==> lap_eq ==> lap_eq) lap_compose.
Proof.
intros la lb Hlab lc ld Hlcd.
revert lb lc ld Hlab Hlcd.
induction la as [| a]; intros.
 induction lb as [| b]; [ reflexivity | simpl ].
 apply lap_eq_nil_cons_inv in Hlab.
 destruct Hlab as (Hb, Hlb).
 simpl in IHlb.
 assert (lap_eq [b] []) as H by (rewrite Hb; constructor; reflexivity).
 rewrite H; clear H.
 rewrite lap_add_nil_r.
 rewrite <- IHlb; [ rewrite lap_mul_nil_l; reflexivity | assumption ].

 simpl.
 destruct lb as [| b]; simpl.
  apply lap_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Ha, Hla).
  assert (lap_eq [a] []) as H by (rewrite Ha; constructor; reflexivity).
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

Section lap.

Variable α : Type.
Variable r : ring α.

(* addition theorems *)

Theorem lap_add_comm : ∀ al₁ al₂,
  lap_eq (lap_add al₁ al₂) (lap_add al₂ al₁).
Proof.
intros al₁ al₂.
revert al₂.
induction al₁; intros.
 destruct al₂; [ apply lap_eq_refl | simpl ].
 constructor; [ reflexivity | apply lap_eq_refl ].

 destruct al₂.
  constructor; [ reflexivity | apply lap_eq_refl ].

  constructor; [ apply rng_add_comm | apply IHal₁ ].
Qed.

Theorem lap_add_assoc : ∀ al₁ al₂ al₃,
  lap_eq (lap_add al₁ (lap_add al₂ al₃))
    (lap_add (lap_add al₁ al₂) al₃).
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

   constructor; [ apply rng_add_assoc | apply IHal₁ ].
Qed.

Theorem lap_add_add_swap : ∀ la lb lc,
  lap_eq (lap_add (lap_add la lb) lc)
     (lap_add (lap_add la lc) lb).
Proof.
intros la lb lc.
do 2 rewrite <- lap_add_assoc.
apply lap_add_compat; [ reflexivity | simpl ].
apply lap_add_comm.
Qed.

Theorem lap_app_add : ∀ la lb,
  (la ++ lb = la + list_pad (length la) 0%K lb)%lap.
Proof.
intros la lb.
induction la as [| a]; [ reflexivity | simpl ].
rewrite rng_add_0_r.
constructor; [ reflexivity | assumption ].
Qed.

Theorem lap_add_map2 : ∀ β (f g : β → α) la,
  (List.map f la + List.map g la = List.map (λ b, (f b + g b)%K) la)%lap.
Proof.
intros β f g la.
induction la as [| b]; [ reflexivity | simpl ].
constructor; auto with Arith.
Qed.

(* multiplication theorems *)

Theorem lap_mul_comm : ∀ a b, lap_eq (lap_mul a b) (lap_mul b a).
Proof.
intros a b.
unfold lap_mul.
rewrite lap_convol_mul_comm, Nat.add_comm; reflexivity.
Qed.

Theorem list_nth_lap_convol_mul_aux : ∀ la lb n i len,
  pred (List.length la + List.length lb) = (i + len)%nat
  → (List.nth n (lap_convol_mul r la lb i len) 0%K =
     Σ (j = 0, n + i),
     List.nth j la 0 * List.nth (n + i - j) lb 0)%K.
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
  rewrite rng_mul_0_l; reflexivity.

  destruct (le_dec (length lb) (n + i - j)) as [H₂| H₂].
   rewrite rng_mul_comm.
   rewrite List.nth_overflow; [ idtac | assumption ].
   rewrite rng_mul_0_l; reflexivity.

   exfalso; apply H₂; clear Hj H₂.
   apply Nat.nle_gt in H₁; subst i.
   rewrite <- Nat.add_pred_l.
    apply Nat.lt_le_pred in H₁.
    apply Nat.le_add_le_sub_l.
    rewrite Nat.add_assoc.
    apply Nat.add_le_mono_r.
    rewrite Nat.add_comm.
    eapply Nat.le_trans; eauto .
    apply Nat.le_sub_le_add_l.
    rewrite Nat.sub_diag.
    apply Nat.le_0_l.

    intros H; rewrite H in H₁.
    revert H₁; apply Nat.nlt_0_r.

 simpl.
 destruct n; [ reflexivity | idtac ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
 rewrite IHlen; [ idtac | assumption ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l; reflexivity.
Qed.

(* to be unified perhaps with list_nth_convol_mul below *)
Theorem list_nth_lap_convol_mul : ∀ la lb i len,
  len = pred (length la + length lb)
  → (List.nth i (lap_convol_mul r la lb 0 len) 0 =
     Σ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%K.
Proof.
intros la lb i len Hlen.
symmetry in Hlen.
rewrite list_nth_lap_convol_mul_aux; [ idtac | assumption ].
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul : ∀ la lb lc k,
  (Σ (i = 0, k),
     List.nth i la 0 *
     List.nth (k - i)
       (lap_convol_mul r lb lc 0 (pred (length lb + length lc)))
       0 =
   Σ (i = 0, k),
     List.nth i la 0 *
     Σ (j = 0, k - i),
       List.nth j lb 0 * List.nth (k - i - j) lc 0)%K.
Proof.
intros la lb lc k.
apply summation_compat; intros i (_, Hi).
apply rng_mul_compat_l.
rewrite list_nth_lap_convol_mul; reflexivity.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul_2 : ∀ la lb lc k,
   (Σ (i = 0, k),
      List.nth i lc 0 *
      List.nth (k - i)
        (lap_convol_mul r la lb 0 (pred (length la + length lb)))  0 =
    Σ (i = 0, k),
      List.nth (k - i) lc 0 *
      Σ (j = 0, i),
        List.nth j la 0 * List.nth (i - j) lb 0)%K.
Proof.
intros la lb lc k.
rewrite summation_rtl.
apply summation_compat; intros i (_, Hi).
rewrite Nat.add_0_r.
apply rng_mul_compat_l.
rewrite Nat_sub_sub_distr; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub.
apply list_nth_lap_convol_mul; reflexivity.
Qed.

(* inspired from series_mul_assoc *)
Theorem lap_mul_assoc : ∀ la lb lc,
  lap_eq (lap_mul la (lap_mul lb lc))
    (lap_mul (lap_mul la lb) lc).
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
rewrite rng_mul_comm, rng_mul_assoc.
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm, Nat.sub_add_distr.
reflexivity.
Qed.

Theorem lap_mul_mul_swap : ∀ la lb lc,
  lap_eq (lap_mul (lap_mul la lb) lc) (lap_mul (lap_mul la lc) lb).
Proof.
intros la lb lc.
do 2 rewrite <- lap_mul_assoc.
apply lap_mul_compat; [ reflexivity | apply lap_mul_comm ].
Qed.

Theorem lap_eq_skipn_succ : ∀ cl i,
  lap_eq [List.nth i cl 0%K … List.skipn (S i) cl] (List.skipn i cl).
Proof.
intros cl i.
revert i.
induction cl as [| c]; intros; simpl.
 destruct i; constructor; reflexivity.

 destruct i; [ reflexivity | apply IHcl ].
Qed.

Theorem lap_convol_mul_1_l : ∀ cl i len,
  length cl = (i + len)%nat
  → lap_eq (lap_convol_mul r [1%K] cl i len) (List.skipn i cl).
Proof.
intros cl i len Hlen.
revert cl i Hlen.
induction len; intros.
 simpl.
 rewrite Nat.add_0_r in Hlen.
 rewrite list_skipn_overflow; subst; reflexivity.

 simpl.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite rng_mul_1_l, Nat.sub_0_r.
 rewrite all_0_summation_0.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
  rewrite rng_add_0_r, IHlen; [ clear | assumption ].
  apply lap_eq_skipn_succ.

  intros j (Hj, Hji).
  destruct j; [ exfalso; revert Hj; apply Nat.nle_succ_0 | idtac ].
  destruct j; rewrite rng_mul_0_l; reflexivity.
Qed.

Fixpoint lap_convol_mul_add al₁ al₂ al₃ i len :=
  match len with
  | O => []
  | S len₁ =>
      [Σ (j = 0, i),
       (List.nth j al₁ 0 *
        (List.nth (i - j) al₂ 0 + List.nth (i - j) al₃ 0))%K …
        lap_convol_mul_add al₁ al₂ al₃ (S i) len₁]
  end.

(* *)

Theorem list_nth_add : ∀ k la lb,
  (List.nth k (lap_add la lb) 0 =
   List.nth k la 0 + List.nth k lb 0)%K.
Proof.
intros k la lb.
revert la lb.
induction k; intros.
 destruct la as [| a]; simpl; [ rewrite rng_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite rng_add_0_r; reflexivity | idtac ].
 reflexivity.

 destruct la as [| a]; simpl; [ rewrite rng_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite rng_add_0_r; reflexivity | idtac ].
 apply IHk.
Qed.

Theorem lap_convol_mul_lap_add : ∀ la lb lc i len,
  lap_eq
    (lap_convol_mul r la (lap_add lb lc) i len)
    (lap_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
apply summation_compat; intros j (_, Hj).
apply rng_mul_compat_l.
rewrite list_nth_add; reflexivity.
Qed.

Theorem lap_add_lap_convol_mul : ∀ la lb lc i len,
   lap_eq
     (lap_add
        (lap_convol_mul r la lb i len)
        (lap_convol_mul r la lc i len))
     (lap_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite <- summation_add_distr.
apply summation_compat; intros j (_, Hj).
rewrite rng_mul_add_distr_l; reflexivity.
Qed.

Theorem lap_mul_add_distr_l : ∀ la lb lc,
  lap_eq (lap_mul la (lap_add lb lc))
    (lap_add (lap_mul la lb) (lap_mul la lc)).
Proof.
intros la lb lc.
unfold lap_mul.
remember (pred (length la + length (lap_add lb lc))) as labc.
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

Theorem lap_mul_add_distr_r : ∀ la lb lc,
  lap_eq (lap_mul (lap_add la lb) lc)
    (lap_add (lap_mul la lc) (lap_mul lb lc)).
Proof.
intros la lb lc.
rewrite lap_mul_comm, lap_mul_add_distr_l, lap_mul_comm.
apply lap_add_compat; [ reflexivity | apply lap_mul_comm ].
Qed.

Theorem lap_convol_mul_1_r : ∀ la i len,
  (i + len = length la)%nat
  → lap_eq (lap_convol_mul r la [1%K] i len) (List.skipn i la).
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
 rewrite rng_mul_1_r.
 rewrite all_0_summation_0.
  rewrite rng_add_0_r.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
  rewrite IHlen; [ idtac | assumption ].
  apply lap_eq_skipn_succ.

  intros j (Hj, Hji).
  rewrite Nat_sub_sub_distr; [ idtac | assumption ].
  rewrite Nat.add_comm, Nat.add_sub.
  destruct j; [ exfalso; revert Hj; apply Nat.nle_succ_0 | idtac ].
  destruct j; rewrite rng_mul_0_r; reflexivity.
Qed.

Theorem lap_mul_1_l : ∀ la, lap_eq (lap_mul [1%K] la) la.
Proof.
intros la.
unfold lap_mul.
apply lap_convol_mul_1_l; simpl.
reflexivity.
Qed.

Theorem lap_mul_1_r : ∀ la, lap_eq (lap_mul la [1%K]) la.
Proof.
intros la.
unfold lap_mul.
apply lap_convol_mul_1_r; simpl.
rewrite Nat.add_comm; reflexivity.
Qed.

(* to be unified perhaps with list_nth_lap_convol_mul above *)
Theorem list_nth_convol_mul : ∀ la lb i k len,
  (i + len)%nat = pred (length la + length lb)
  → (List.nth k (lap_convol_mul r la lb i len) 0 =
     Σ (j = 0, i + k),
     List.nth j la 0 * List.nth (i + k - j) lb 0)%K.
Proof.
intros la lb i k len Hilen.
revert la lb i k Hilen.
induction len; intros; simpl.
 rewrite match_id; simpl.
 rewrite all_0_summation_0; [ reflexivity | simpl ].
 intros j (_, Hj).
 destruct (lt_dec j (length la)) as [Hja| Hja].
  destruct (lt_dec (i + k - j) (length lb)) as [Hjb| Hjb].
   exfalso; fast_omega Hilen Hja Hjb.

   apply rng_mul_eq_0; right.
   apply Nat.nlt_ge in Hjb.
   rewrite List.nth_overflow; [ reflexivity | assumption ].

  apply rng_mul_eq_0; left.
  apply Nat.nlt_ge in Hja.
  rewrite List.nth_overflow; [ reflexivity | assumption ].

 destruct k; [ rewrite Nat.add_0_r; reflexivity | idtac ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hilen.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 apply IHlen; assumption.
Qed.

Theorem list_nth_lap_mul : ∀ la lb k,
  (List.nth k (lap_mul la lb) 0 =
   Σ (i = 0, k), List.nth i la 0 * List.nth (k - i) lb 0)%K.
Proof.
intros la lb k.
apply list_nth_convol_mul; reflexivity.
Qed.

(* compose theorems *)

Theorem lap_mul_fold_add_distr : ∀ β la li (g : β → list α) x,
  lap_eq
    (lap_mul x (List.fold_right (λ i accu, lap_add accu (g i)) la li))
    (List.fold_right (λ i accu, lap_add accu (lap_mul x (g i)))
       (lap_mul x la) li).
Proof.
intros uβ la li g x.
revert la x.
induction li as [| j]; intros; [ reflexivity | simpl ].
rewrite lap_mul_add_distr_l.
rewrite IHli; reflexivity.
Qed.

Theorem list_fold_right_seq : ∀ g h la lb s t len,
  lap_eq la lb
  → (∀ x y z, lap_eq y z → lap_eq (g x y) (g x z))
    → (∀ i accu, lap_eq (g (s + i)%nat accu) (h (t + i)%nat accu))
      → lap_eq
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

Theorem lap_compose_compose2 : ∀ la lb,
  lap_eq (lap_compose la lb) (lap_compose2 la lb).
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

Theorem lap_compose_compat : ∀ la lb lc ld,
  lap_eq la lc
  → lap_eq lb ld
    → lap_eq (lap_compose la lb) (lap_compose lc ld).
Proof.
intros la lb lc ld Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

(* power *)

Theorem lap_power_add : ∀ la i j,
  lap_eq (lap_power la (i + j))
    (lap_mul (lap_power la i) (lap_power la j)).
Proof.
intros la i j.
revert j.
induction i; intros; simpl.
 rewrite lap_mul_1_l; reflexivity.

 rewrite IHi, lap_mul_assoc; reflexivity.
Qed.

Theorem lap_power_mul : ∀ la lb n,
  lap_eq
    (lap_power (lap_mul la lb) n)
    (lap_mul (lap_power la n) (lap_power lb n)).
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

Theorem lap_power_1 : ∀ la, (la ^ 1 = la)%lap.
Proof.
intros la; simpl.
rewrite lap_mul_1_r; reflexivity.
Qed.

Theorem list_nth_pad_lt : ∀ i s (v : α) cl d,
  (i < s)%nat
  → List.nth i (list_pad s v cl) d = v.
Proof.
intros i s v cl d His.
revert i His.
induction s; intros; [ easy | ].
simpl.
destruct i; [ reflexivity | idtac ].
apply Nat.succ_lt_mono in His.
now apply IHs.
Qed.

Theorem list_nth_pad_sub : ∀ i s (v : α) cl d,
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

Theorem lap_mul_cons_l : ∀ a la lb,
  lap_eq (lap_mul [a … la] lb)
    (lap_add (lap_mul [a] lb) [0%K … lap_mul la lb]).
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
 rewrite rng_add_0_r; reflexivity.

 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite Nat.sub_0_r.
 symmetry.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite all_0_summation_0.
  rewrite Nat.sub_0_r.
  simpl.
  rewrite rng_add_0_r.
  apply rng_add_compat_l.
  rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
  rewrite summation_succ_succ; reflexivity.

  intros i (Hi, Hik); simpl.
  destruct i; [ exfalso; fast_omega Hi | simpl ].
  destruct i; rewrite rng_mul_0_l; reflexivity.
Qed.

Theorem lap_mul_cons_r : ∀ la b lb,
  lap_eq (lap_mul la [b … lb])
    (lap_add (lap_mul la [b]) [0%K … lap_mul la lb]).
Proof.
intros la b lb.
rewrite lap_mul_comm.
rewrite lap_mul_cons_l.
rewrite lap_mul_comm.
apply lap_add_compat; [ reflexivity | idtac ].
rewrite lap_mul_comm; reflexivity.
Qed.

Theorem lap_eq_0 : lap_eq [0%K] [].
Proof. constructor; reflexivity. Qed.

Theorem lap_convol_mul_cons_succ : ∀ a b lb i len,
  lap_eq (lap_convol_mul r [a] [b … lb] (S i) len)
    (lap_convol_mul r [a] lb i len).
Proof.
intros a b lb i len.
revert a b lb i.
induction len; intros; [ reflexivity | idtac ].
constructor; [ idtac | apply IHlen ].
rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
rewrite List.nth_overflow; [ idtac | simpl; fast_omega  ].
rewrite rng_mul_0_l, rng_add_0_r.
apply summation_compat; intros j (_, Hj).
apply rng_mul_compat_l.
rewrite Nat.sub_succ_l; [ reflexivity | assumption ].
Qed.

Theorem lap_mul_cons : ∀ a b la lb,
  lap_eq (lap_mul [a … la] [b … lb])
    [(a * b)%K
    … lap_add (lap_add (lap_mul la [b]) (lap_mul [a] lb))
        [0%K … lap_mul la lb]].
Proof.
intros a b la lb.
rewrite lap_mul_cons_l; simpl.
rewrite summation_only_one.
rewrite rng_add_0_r.
constructor; [ reflexivity | idtac ].
rewrite lap_mul_cons_r.
unfold lap_mul; simpl.
rewrite lap_add_assoc.
apply lap_add_compat; [ idtac | reflexivity ].
rewrite lap_add_comm.
apply lap_add_compat; [ reflexivity | idtac ].
apply lap_convol_mul_cons_succ.
Qed.

(* *)

Theorem lap_fold_compat_l : ∀ A (g h : A → _) la lb l,
  lap_eq la lb
  → lap_eq
      (List.fold_right (λ v accu, lap_add accu (lap_mul (g v) (h v)))
         la l)
      (List.fold_right (λ v accu, lap_add accu (lap_mul (g v) (h v)))
         lb l).
Proof.
intros A g h la lb l Heq.
induction l; [ assumption | simpl; rewrite IHl; reflexivity ].
Qed.

Theorem lap_compose_single : ∀ a lb lc,
  (lap_compose ([a] * lb) lc = [a] * lap_compose lb lc)%lap.
Proof.
intros a lb lc.
induction lb as [| b].
 simpl; rewrite lap_mul_nil_r; reflexivity.

 rewrite lap_mul_cons_r; simpl.
 rewrite summation_only_one, rng_add_0_r, IHlb.
 rewrite lap_mul_add_distr_l, lap_mul_assoc.
 apply lap_add_compat; [ reflexivity | idtac ].
 rewrite lap_mul_cons; simpl.
 rewrite lap_mul_nil_r.
 constructor; [ reflexivity | idtac ].
 rewrite lap_eq_0; reflexivity.
Qed.

Theorem lap_compose_add : ∀ la lb lc,
  (lap_compose (la + lb) lc = lap_compose la lc + lap_compose lb lc)%lap.
Proof.
intros la lb lc.
revert lb lc.
induction la as [| a]; intros; [ reflexivity | simpl ].
destruct lb as [| b]; simpl.
 rewrite lap_add_nil_r; reflexivity.

 rewrite IHla.
 rewrite lap_mul_add_distr_r.
 do 2 rewrite <- lap_add_assoc.
 apply lap_add_compat_l.
 symmetry.
 rewrite lap_add_comm.
 rewrite <- lap_add_assoc.
 apply lap_add_compat_l.
 rewrite lap_add_comm; reflexivity.
Qed.

Theorem lap_compose_mul : ∀ la lb lc,
  (lap_compose (la * lb) lc = lap_compose la lc * lap_compose lb lc)%lap.
Proof.
(* inspiré de apply_lap_mul *)
intros la lb lc.
revert lb lc.
induction la as [| a]; intros; simpl.
 do 2 rewrite lap_mul_nil_l; reflexivity.

 destruct lb as [| b]; simpl.
  do 2 rewrite lap_mul_nil_r; reflexivity.

  rewrite lap_mul_cons; simpl.
  do 2 rewrite lap_compose_add; simpl.
  do 2 rewrite IHla; simpl.
  rewrite lap_mul_nil_l, lap_add_nil_l.
  do 3 rewrite lap_mul_add_distr_r; simpl.
  rewrite lap_mul_add_distr_l; simpl.
  rewrite lap_mul_add_distr_r; simpl.
  rewrite lap_mul_add_distr_r; simpl.
  do 2 rewrite lap_mul_assoc.
  do 2 rewrite lap_add_assoc; simpl.
  apply lap_add_compat.
   rewrite lap_eq_0, lap_mul_nil_l, lap_add_nil_r.
   rewrite lap_add_comm, lap_add_assoc.
   rewrite <- lap_add_assoc.
   rewrite <- lap_add_assoc.
   apply lap_add_compat.
    apply lap_mul_compat; [ idtac | reflexivity ].
    rewrite lap_mul_mul_swap; reflexivity.

    symmetry; rewrite lap_add_comm.
    apply lap_add_compat.
     rewrite lap_mul_mul_swap; reflexivity.

     apply lap_mul_compat; [ idtac | reflexivity ].
     symmetry.
     apply lap_compose_single.

   rewrite lap_mul_cons; simpl.
   rewrite lap_mul_nil_r.
   constructor; [ reflexivity | idtac ].
   rewrite lap_eq_0; reflexivity.
Qed.

End lap.

Theorem lap_add_opp_l : ∀ α (r : ring α) la, (- la + la = 0)%lap.
Proof.
intros α r la.
induction la as [| a]; [ reflexivity | simpl ].
rewrite IHla, rng_add_opp_l.
constructor; reflexivity.
Qed.

Theorem lap_mul_compat_l : ∀ α (r : ring α) a b c,
  lap_eq a b
  → lap_eq (lap_mul c a) (lap_mul c b).
Proof.
intros α r a b c Hab.
rewrite Hab; reflexivity.
Qed.

Definition lap_ring α (R : ring α) : ring (list α) :=
  {| rng_zero := lap_zero;
     rng_one := lap_one;
     rng_add := lap_add;
     rng_mul := lap_mul;
     rng_opp := lap_opp;
     rng_eq := lap_eq;
     rng_eq_refl := lap_eq_refl;
     rng_eq_sym := lap_eq_sym;
     rng_eq_trans := lap_eq_trans;
     rng_add_comm := lap_add_comm R;
     rng_add_assoc := lap_add_assoc R;
     rng_add_0_l := lap_add_nil_l R;
     rng_add_opp_l := lap_add_opp_l R;
     rng_add_compat_l := lap_add_compat_l;
     rng_mul_comm := lap_mul_comm R;
     rng_mul_assoc := lap_mul_assoc R;
     rng_mul_1_l := lap_mul_1_l R;
     rng_mul_compat_l := @lap_mul_compat_l _ R;
     rng_mul_add_distr_l := lap_mul_add_distr_l R |}.

Canonical Structure lap_ring.

(* polynomial type *)

Record polynomial α := mkpol { al : list α }.

Declare Scope poly_scope.
Delimit Scope poly_scope with pol.
Notation "'POL' l" := {| al := l |} (at level 1) : poly_scope.

Definition eq_poly {α} {r : ring α} x y := lap_eq (al x) (al y).

Notation "a = b" := (eq_poly a b) : poly_scope.
Notation "a ≠ b" := (¬eq_poly a b) : poly_scope.

Definition poly_one {α} {r : ring α} := POL [1%K]%pol.
Notation "1" := poly_one : poly_scope.

Theorem eq_poly_refl α (r : ring α) : reflexive _ eq_poly.
Proof.
intros pol.
unfold eq_poly; reflexivity.
Qed.

Theorem eq_poly_sym α (r : ring α) : symmetric _ eq_poly.
Proof.
intros pol₁ pol₂ Heq.
unfold eq_poly; symmetry; assumption.
Qed.

Theorem eq_poly_trans α (r : ring α) : transitive _ eq_poly.
Proof.
intros pol₁ pol₂ pol₃ H₁ H₂.
unfold eq_poly; etransitivity; eassumption.
Qed.

Add Parametric Relation α (r : ring α) : (polynomial α) eq_poly
 reflexivity proved by (eq_poly_refl r)
 symmetry proved by (eq_poly_sym (r := r))
 transitivity proved by (eq_poly_trans (r := r))
 as eq_poly_rel.

Definition poly_add {α} {r : ring α} pol₁ pol₂ :=
  {| al := lap_add (al pol₁) (al pol₂) |}.

Definition poly_mul {α} {r : ring α} pol₁ pol₂ :=
  {| al := lap_mul (al pol₁) (al pol₂) |}.

Definition poly_power {α} {r : ring α} pol n :=
  (POL (lap_power (al pol) n))%pol.

Definition poly_compose {α} {r : ring α} a b :=
  POL (lap_compose (al a) (al b))%pol.

Definition poly_compose2 {α} {r : ring α} a b :=
  POL (lap_compose2 (al a) (al b))%pol.

Notation "a + b" := (poly_add a b) : poly_scope.
Notation "a * b" := (poly_mul a b) : poly_scope.
Notation "a ^ b" := (poly_power a b) : poly_scope.
Notation "a ∘ b" := (poly_compose a b) : poly_scope.

Global Instance al_morph α (r : ring α) :
  Proper (eq_poly ==> lap_eq) (@al α).
Proof. intros; easy. Qed.

Global Instance poly_add_morph α (r : ring α) :
  Proper (eq_poly ==> eq_poly ==> eq_poly) poly_add.
Proof.
intros a c Hac b d Hbd.
unfold eq_poly, poly_add; simpl.
unfold eq_poly in Hac, Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Global Instance poly_mul_morph α (r : ring α) :
  Proper (eq_poly ==> eq_poly ==> eq_poly) poly_mul.
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

Global Instance poly_compose_morph α (K : ring α) :
  Proper (eq_poly ==> eq_poly ==> eq_poly) poly_compose.
Proof.
intros A C HAC B D HBD.
unfold eq_poly; simpl.
rewrite HAC, HBD; reflexivity.
Qed.

Section poly.

Variable α : Type.
Variable r : ring α.

Theorem poly_add_compat : ∀ a b c d,
  (a = c)%pol
  → (b = d)%pol
    → (a + b = c + d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Theorem poly_add_assoc : ∀ pol₁ pol₂ pol₃,
  (pol₁ + (pol₂ + pol₃) = (pol₁ + pol₂) + pol₃)%pol.
Proof.
intros pol₁ pol₂ pol₃.
unfold eq_poly.
eapply lap_add_assoc; reflexivity.
Qed.

Theorem poly_mul_compat : ∀ a b c d,
  (a = c)%pol
  → (b = d)%pol
    → (a * b = c * d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Theorem poly_mul_comm : ∀ a b, (a * b = b * a)%pol.
Proof.
intros a b.
unfold eq_poly; simpl.
unfold lap_mul; simpl.
rewrite Nat.add_comm.
rewrite lap_convol_mul_comm; reflexivity.
Qed.

Theorem poly_mul_assoc : ∀ P Q R,
  (P * (Q * R) = (P * Q) * R)%pol.
Proof.
intros P Q R.
apply lap_mul_assoc.
Qed.

Theorem poly_mul_1_l : ∀ a, (1 * a = a)%pol.
Proof.
intros a.
unfold eq_poly; simpl.
unfold lap_mul; simpl.
rewrite lap_convol_mul_1_l; reflexivity.
Qed.

Theorem poly_mul_add_distr_l : ∀ P Q R,
  (P * (Q + R) = P * Q + P * R)%pol.
Proof.
intros P Q R.
apply lap_mul_add_distr_l.
Qed.

End poly.

(* *)

Definition apply_lap α {R : ring α} la x :=
  (List.fold_right (λ c accu, accu * x + c) 0 la)%K.

Definition apply_poly α {R : ring α} pol :=
  apply_lap (al pol).

Theorem lap_add_map : ∀ α β (Rα : ring α) (Rβ : ring β) (f : α → β) la lb,
  (∀ a b, (f (a + b) = f a + f b)%K)
  → (List.map f (la + lb) = List.map f la + List.map f lb)%lap.
Proof.
clear.
intros α β Rα Rβ f la lb Hab.
revert lb.
induction la as [| a]; intros; [ reflexivity | simpl ].
destruct lb as [| b]; [ reflexivity | simpl ].
rewrite Hab, IHla; reflexivity.
Qed.
