(* SplitList.v *)

Require Import Utf8.
Require Import Arith.
Require Import NPeano.
Require Import Sorted.

Require Import Misc.

Set Implicit Arguments.

Inductive split_list α : list α → list α → list α → Prop :=
  | sl_nil : split_list [] [] []
  | sl_cons_l : ∀ x l l₁ l₂,
      split_list l l₁ l₂ → split_list [x … l] [x … l₁] l₂
  | sl_cons_r : ∀ x l l₁ l₂,
      split_list l l₁ l₂ → split_list [x … l] l₁ [x … l₂].

Lemma split_list_comm : ∀ α (l la lb : list α),
  split_list l la lb
  → split_list l lb la.
Proof.
intros A l la lb H.
revert la lb H.
induction l as [| x]; intros.
 inversion H; subst; constructor.

 inversion H; subst; constructor; apply IHl; assumption.
Qed.

Lemma split_list_length : ∀ α (l la lb : list α),
  split_list l la lb → length l = (length la + length lb)%nat.
Proof.
intros A l la lb H.
revert la lb H.
induction l as [| x]; intros; [ inversion H; reflexivity | simpl ].
inversion H; subst; simpl.
 apply eq_S, IHl; assumption.

 rewrite Nat.add_succ_r.
 apply eq_S, IHl; assumption.
Qed.

Lemma split_list_nil_l : ∀ α (l la : list α),
  split_list l [] la → la = l.
Proof.
intros A l la H.
revert la H.
induction l as [| x]; intros.
 inversion H; reflexivity.

 inversion H; subst; f_equal.
 apply IHl; assumption.
Qed.

Lemma split_sorted_cons_r : ∀ l la lb b,
  split_list l la [b … lb]
  → Sorted Nat.lt [b … l]
    → False.
Proof.
intros l la lb b Hs Hsort.
revert b lb l Hs Hsort.
induction la as [| a]; intros.
 inversion Hs; subst.
 apply Sorted_inv in Hsort.
 destruct Hsort as (_, Hrel).
 apply HdRel_inv in Hrel.
 revert Hrel; apply Nat.lt_irrefl.

 destruct l as [| c]; inversion Hs; subst.
  eapply IHla; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

  apply Sorted_inv in Hsort.
  destruct Hsort as (_, Hrel).
  apply HdRel_inv in Hrel.
  revert Hrel; apply Nat.lt_irrefl.
Qed.

Lemma split_list_sorted_cons_cons : ∀ l la lb a b,
  split_list l la [b … lb]
  → Sorted Nat.lt [a … l]
    → a ∉ lb.
Proof.
intros l la lb a b Hs Hsort Hlb.
revert la lb a b Hs Hsort Hlb.
induction l as [| c]; intros; [ inversion Hs | idtac ].
destruct (eq_nat_dec c b) as [Hcb| Hcb].
 subst c.
 inversion Hs; subst.
  eapply IHl; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

  clear Hs.
  destruct lb as [| c]; [ contradiction | idtac ].
  destruct Hlb as [Hlb| Hlb].
   subst c.
   eapply split_sorted_cons_r; [ eassumption | idtac ].
   eapply Sorted_minus_2nd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

   eapply IHl; try eassumption.
   eapply Sorted_minus_2nd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

 inversion Hs; subst.
  clear Hs.
  eapply IHl; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

  apply Hcb; reflexivity.
Qed.

Lemma split_list_sorted_cons_not_in : ∀ l la lb a,
  split_list l la lb
  → Sorted Nat.lt [a … l]
    → a ∉ lb.
Proof.
intros l la lb a Hs Hsort Hlb.
destruct lb as [| b]; intros; [ contradiction | idtac ].
destruct Hlb as [Hlb| Hlb].
 subst a.
 eapply split_sorted_cons_r; eassumption.

 eapply split_list_sorted_cons_cons; eassumption.
Qed.

Lemma sorted_split_cons_not_in : ∀ l la lb a,
  Sorted Nat.lt l
  → split_list l [a … la] lb
    → a ∉ lb.
Proof.
intros l la lb a Hsort Hs Hlb.
revert la lb a Hsort Hs Hlb.
induction l as [| b]; intros; [ inversion Hs | idtac ].
destruct (eq_nat_dec a b) as [Hab| Hab].
 subst b.
 inversion Hs; subst.
  clear Hs.
  eapply split_list_sorted_cons_not_in; eassumption.

  clear Hlb.
  clear Hs.
  apply split_list_comm in H3.
  eapply split_sorted_cons_r; eassumption.

 inversion Hs; subst.
  apply Hab; reflexivity.

  apply not_eq_sym in Hab.
  destruct Hlb as [| Hlb]; [ contradiction | idtac ].
  eapply IHl; try eassumption.
  eapply Sorted_inv; eassumption.
Qed.

Lemma sorted_split_in_not_in : ∀ l la lb x,
  Sorted Nat.lt l
  → split_list l la lb
    → x ∈ la
      → x ∉ lb.
Proof.
intros l la lb x Hsort Hs Hla Hlb.
revert la lb x Hsort Hs Hla Hlb.
induction l as [| a]; intros.
 inversion Hs; subst; contradiction.

 rename a into y.
 destruct la as [| a]; [ contradiction | idtac ].
 destruct Hla as [Hla| Hla].
  subst x.
  destruct (eq_nat_dec y a) as [Hya| Hya].
   subst y.
   inversion Hs; subst.
    revert Hlb.
    eapply split_list_sorted_cons_not_in; eassumption.

    rename l₂ into lb.
    eapply split_list_comm in H3.
    clear Hs.
    eapply split_sorted_cons_r; eassumption.

   destruct lb as [| b]; [ contradiction | idtac ].
   destruct Hlb as [Hlb| Hlb].
    subst b.
    inversion Hs; subst.
     apply Hya; reflexivity.

     apply Hya; reflexivity.

    destruct (eq_nat_dec y b) as [Hyb| Hyb].
     subst y.
     inversion Hs; subst.
      apply Hya; reflexivity.

      clear Hs.
      apply Sorted_inv_1 in Hsort.
      eapply sorted_split_cons_not_in; eassumption.

     inversion Hs; subst.
      apply Hya; reflexivity.

      apply Hyb; reflexivity.

  destruct (eq_nat_dec y a) as [Hya| Hya].
   subst y.
   inversion Hs; subst.
    apply Sorted_inv_1 in Hsort.
    eapply IHl; eassumption.

    rename l₂ into lb.
    eapply split_list_comm in H3.
    clear Hs.
    eapply split_sorted_cons_r; eassumption.

   destruct lb as [| b]; [ contradiction | idtac ].
   destruct Hlb as [Hlb| Hlb].
    subst b.
    inversion Hs; subst.
     apply Hya; reflexivity.

     clear Hs.
     apply split_list_comm in H2.
     revert Hla.
     eapply split_list_sorted_cons_cons; eassumption.

    destruct (eq_nat_dec y b) as [Hyb| Hyb].
     subst y.
     inversion Hs; subst.
      apply Hya; reflexivity.

      clear Hs.
      apply Sorted_inv_1 in Hsort.
      eapply IHl; try eassumption.
      right; assumption.

     inversion Hs; subst.
      apply Hya; reflexivity.

      apply Hyb; reflexivity.
Qed.
