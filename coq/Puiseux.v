(* $Id: Puiseux.v,v 1.653 2013-06-14 02:17:08 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Sorted.
Require Import NPeano.

Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Puiseux_base.
Require Import Misc.
Require Import Series.

Set Implicit Arguments.

Definition degree α (pol : polynomial α) := List.length (al pol).

(* Horner's algorithm *)
Definition apply_poly α β γ
    (zero_plus_v : β → α) (add_v_coeff : α → β → α) (mul_v_x : α → γ → α)
    (pol : polynomial β) (x : γ) :=
  List.fold_right (λ c accu, add_v_coeff (mul_v_x accu x) c)
    (zero_plus_v (an pol)) (al pol).

Definition pol_add α (add_coeff : α → α → α) pol₁ pol₂ :=
  let fix loop al₁ al₂ :=
    match (al₁, al₂) with
    | ([], []) => mkpol [] (add_coeff (an pol₁) (an pol₂))
    | ([], [a₂ … bl₂]) =>
        mkpol [add_coeff (an pol₁) a₂ … bl₂] (an pol₂)
    | ([a₁ … bl₁], []) =>
        mkpol [add_coeff a₁ (an pol₂) … bl₁] (an pol₁)
    | ([a₁ … bl₁], [a₂ … bl₂]) =>
        let r := loop bl₁ bl₂ in
        mkpol [add_coeff a₁ a₂ … al r] (an r)
    end
  in
  loop (al pol₁) (al pol₂).

CoFixpoint ps_add_loop α (add_coeff : α → α → α) ms₁ ms₂ :=
  match ms₁ with
  | Term c₁ s₁ =>
      match ms₂ with
      | Term c₂ s₂ =>
          match Qcompare (power c₁) (power c₂) with
          | Eq =>
              let c := add_coeff (coeff c₁) (coeff c₂) in
              let m := {| coeff := c; power := power c₁ |} in
              Term m (ps_add_loop add_coeff s₁ s₂)
          | Lt =>
              Term c₁ (ps_add_loop add_coeff s₁ ms₂)
          | Gt =>
              Term c₂ (ps_add_loop add_coeff ms₁ s₂)
          end
      | End => ms₁
      end
  | End => ms₂
  end.

Lemma series_forall_div_mul : ∀ α (s : series (term α)) cd x,
  series_forall (pow_den_div_com_den cd) s
  → series_forall (pow_den_div_com_den (cd * x)) s.
Proof.
cofix IHs.
intros α s cd x H.
destruct s.
 eapply TermAndFurther; [ reflexivity | idtac | idtac ].
  apply series_forall_inv in H.
  destruct H as (H, _).
  unfold pow_den_div_com_den in H |- *.
  destruct H as (k₁, H).
  rewrite mult_comm.
  rewrite H.
  exists (x * k₁)%nat.
  rewrite <- mult_assoc.
  reflexivity.

  apply series_forall_inv in H.
  destruct H as (_, H).
  eapply IHs; eassumption.

 constructor; reflexivity.
Qed.

Lemma series_forall_add : ∀ α (add_coeff : α → α → α) s₁ s₂ cd₁ cd₂,
  series_forall (pow_den_div_com_den cd₁) s₁
  → series_forall (pow_den_div_com_den cd₂) s₂
    → series_forall (pow_den_div_com_den (Nat.lcm cd₁ cd₂))
        (ps_add_loop add_coeff s₁ s₂).
Proof.
cofix IHs.
intros α add_coeff s₁ s₂ cd₁ cd₂ Hps₁ Hps₂.
rewrite series_eta; simpl.
destruct s₁.
 rename t into t₁.
 destruct s₂.
  rename t into t₂.
  remember (power t₁ ?= power t₂) as c.
  symmetry in Heqc.
  destruct c.
   apply Qeq_alt in Heqc.
   eapply TermAndFurther; [ reflexivity | idtac | idtac ].
    apply series_forall_inv in Hps₁.
    destruct Hps₁ as (Hpd₁, Hsf₁).
    unfold pow_den_div_com_den in Hpd₁ |- *; simpl.
    destruct Hpd₁ as (k₁, Hpd₁).
    rewrite Hpd₁.
    unfold den_divides_comden.
    remember (Pos.to_nat (Qden (power t₁))) as x.
    remember (Z.abs_nat (Qnum (power t₁))) as y.
    remember (x / gcd y x)%nat as z.
    exists (cd₂ / gcd (k₁ * z) cd₂ * k₁)%nat.
    unfold Nat.lcm.
    rewrite mult_comm, mult_assoc.
    reflexivity.

    apply IHs.
     apply series_forall_inv in Hps₁.
     destruct Hps₁; assumption.

     apply series_forall_inv in Hps₂.
     destruct Hps₂; assumption.

   eapply TermAndFurther; [ reflexivity | idtac | idtac ].
    apply series_forall_inv in Hps₁.
    destruct Hps₁ as (Hpd₁, Hsf₁).
    unfold pow_den_div_com_den in Hpd₁ |- *.
    destruct Hpd₁ as (k₁, Hpd₁).
    rewrite Hpd₁.
    unfold den_divides_comden.
    remember (Pos.to_nat (Qden (power t₁))) as x.
    remember (Z.abs_nat (Qnum (power t₁))) as y.
    remember (x / gcd y x)%nat as z.
    exists (cd₂ / gcd (k₁ * z) cd₂ * k₁)%nat.
    unfold Nat.lcm.
    rewrite mult_comm, mult_assoc.
    reflexivity.

    apply IHs; [ idtac | assumption ].
    apply series_forall_inv in Hps₁.
    destruct Hps₁; assumption.

   apply Qgt_alt in Heqc.
   eapply TermAndFurther; [ reflexivity | idtac | idtac ].
    apply series_forall_inv in Hps₂.
    destruct Hps₂ as (Hpd₂, Hsf₂).
    unfold pow_den_div_com_den in Hpd₂ |- *.
    destruct Hpd₂ as (k₂, Hpd₂).
    rewrite Hpd₂.
    unfold den_divides_comden.
    remember (Pos.to_nat (Qden (power t₂))) as x.
    remember (Z.abs_nat (Qnum (power t₂))) as y.
    remember (x / gcd y x)%nat as z.
    exists (cd₁ / gcd (k₂ * z) cd₁ * k₂)%nat.
    rewrite Nat.lcm_comm.
    unfold Nat.lcm.
    rewrite mult_comm, mult_assoc.
    reflexivity.

    apply IHs; [ assumption | idtac ].
    apply series_forall_inv in Hps₂.
    destruct Hps₂; assumption.

  eapply TermAndFurther; [ reflexivity | idtac | idtac ].
   apply series_forall_inv in Hps₁.
   destruct Hps₁ as (Hpd₁, Hsf₁).
   unfold pow_den_div_com_den in Hpd₁ |- *.
   destruct Hpd₁ as (k₁, Hpd₁).
   rewrite Hpd₁.
   unfold den_divides_comden.
   remember (Pos.to_nat (Qden (power t₁))) as x.
   remember (Z.abs_nat (Qnum (power t₁))) as y.
   remember (x / gcd y x)%nat as z.
   exists (cd₂ / gcd (k₁ * z) cd₂ * k₁)%nat.
   unfold Nat.lcm.
   rewrite mult_comm, mult_assoc.
   reflexivity.

   apply series_forall_inv in Hps₁.
   destruct Hps₁ as (Hpd₁, Hsf₁).
   unfold pow_den_div_com_den in Hpd₁.
   destruct Hpd₁ as (k₁, Hpd₁).
   unfold Nat.lcm.
   apply series_forall_div_mul; assumption.

 rewrite Nat.lcm_comm.
 destruct s₂.
  rename t into t₂.
  eapply TermAndFurther; [ reflexivity | idtac | idtac ].
   apply series_forall_inv in Hps₂.
   destruct Hps₂ as (Hpd₂, Hsf₂).
   unfold pow_den_div_com_den in Hpd₂ |- *.
   destruct Hpd₂ as (k₂, Hpd₂).
   rewrite Hpd₂.
   unfold den_divides_comden.
   remember (Pos.to_nat (Qden (power t₂))) as x.
   remember (Z.abs_nat (Qnum (power t₂))) as y.
   remember (x / gcd y x)%nat as z.
   exists (cd₁ / gcd (k₂ * z) cd₁ * k₂)%nat.
   unfold Nat.lcm.
   rewrite mult_comm, mult_assoc.
   reflexivity.

   apply series_forall_inv in Hps₂.
   destruct Hps₂ as (Hpd₂, Hsf₂).
   unfold pow_den_div_com_den in Hpd₂.
   destruct Hpd₂ as (k₂, Hpd₂).
   unfold Nat.lcm.
   apply series_forall_div_mul; assumption.

  constructor; reflexivity.
Qed.

Theorem ps_prop_add : ∀ α (add_coeff : α → α → α) ps₁ ps₂,
  series_forall
    (pow_den_div_com_den (Nat.lcm (ps_comden ps₁) (ps_comden ps₂)))
    (ps_add_loop add_coeff (ps_terms ps₁) (ps_terms ps₂)).
Proof.
intros α add_coeff ps₁ ps₂.
apply series_forall_add; [ apply (ps_prop ps₁) | apply (ps_prop ps₂) ].
Qed.

Definition ps_add α (add_coeff : α → α → α) (ps₁ : puiseux_series α)
    (ps₂ : puiseux_series α) :=
  {| ps_terms := ps_add_loop add_coeff (ps_terms ps₁) (ps_terms ps₂);
     ps_comden := Nat.lcm (ps_comden ps₁) (ps_comden ps₂);
     ps_prop := ps_prop_add add_coeff ps₁ ps₂ |}.

(* ps_mul *)

Record fifo_elem α :=
  { fe_t₁ : term α; fe_t₂ : term α;
    fe_s₁ : series (term α); fe_s₂ : series (term α) }.

Fixpoint add_coeff_list α (add_coeff : α → α → α) (mul_coeff : α → α → α)
    c₁ fel₁ :=
  match fel₁ with
  | [] =>
      c₁
  | [fe … fel] =>
      let c := mul_coeff (coeff (fe_t₁ fe)) (coeff (fe_t₂ fe)) in
      add_coeff c₁ (add_coeff_list add_coeff mul_coeff c fel)
  end.

Fixpoint insert_elem α (fe : fifo_elem α) fel :=
  match fel with
  | [] => [fe]
  | [fe₁ … fel₁] =>
      match Qcompare (power (fe_t₁ fe)) (power (fe_t₁ fe₁)) with
      | Eq =>
          match Qcompare (power (fe_t₂ fe)) (power (fe_t₂ fe₁)) with
          | Eq => fel
          | Lt => [fe … fel]
          | Gt => [fe₁ … insert_elem fe fel₁]
          end
      | Lt => [fe … fel]
      | Gt => [fe₁ … insert_elem fe fel₁]
      end
  end.

Fixpoint insert_sum α sum (fe : fifo_elem α) sl :=
  match sl with
  | [] => [(sum, [fe])]
  | [(sum₁, fel₁) … l] =>
      match Qcompare sum sum₁ with
      | Eq => [(sum₁, insert_elem fe fel₁) … l]
      | Lt => [(sum, [fe]) … sl]
      | Gt => [(sum₁, fel₁) … insert_sum sum fe l]
      end
  end.

Definition add_below α (mul_coeff : α → α → α) sl fel :=
  List.fold_left
    (λ sl₁ fe,
       match (fe_s₁ fe : series (term α)) with
       | Term t₁ s₁ =>
            insert_sum (Qplus (power t₁) (power (fe_t₂ fe)))
              {| fe_t₁ := t₁; fe_t₂ := fe_t₂ fe;
                 fe_s₁ := s₁; fe_s₂ := fe_s₂ fe |}
              sl₁
       | End => sl₁
       end)
    fel sl.

Definition add_right α (mul_coeff : α → α → α) sl fel :=
  List.fold_left
    (λ sl₂ fe,
       match (fe_s₂ fe : series (term α)) with
       | Term t₂ s₂ =>
            insert_sum (Qplus (power (fe_t₁ fe)) (power t₂))
              {| fe_t₁ := fe_t₁ fe; fe_t₂ := t₂;
                 fe_s₁ := fe_s₁ fe; fe_s₂ := s₂ |}
              sl₂
       | End => sl₂
       end)
    fel sl.

CoFixpoint ps_mul_loop α add_coeff mul_coeff sum_fifo :
    series (term α) :=
  match sum_fifo with
  | [] => End _
  | [(sum, []) … sl] => End _
  | [(sum, [fe₁ … fel₁]) … sl] =>
      let m :=
        let c₁ := mul_coeff (coeff (fe_t₁ fe₁)) (coeff (fe_t₂ fe₁)) in
        let c := add_coeff_list add_coeff mul_coeff c₁ fel₁ in
        {| coeff := c; power := sum |}
      in
      let sl₁ := add_below mul_coeff sl [fe₁ … fel₁] in
      let sl₂ := add_right mul_coeff sl₁ [fe₁ … fel₁] in
      Term m (ps_mul_loop α add_coeff mul_coeff sl₂)
  end.

Definition ps_mul_term α add_coeff (mul_coeff : α → α → α) s₁ s₂ :=
  match s₁ with
  | Term t₁ ns₁ =>
      match s₂ with
      | Term t₂ ns₂ =>
          let fe :=
            {| fe_t₁ := t₁; fe_t₂ := t₂; fe_s₁ := ns₁; fe_s₂ := ns₂ |}
          in
          ps_mul_loop add_coeff mul_coeff
            [(Qplus (power t₁) (power t₂), [fe])]
      | End => End _
      end
  | End => End _
  end.

Definition fifo_sum_prop α (cfel : (Q * list (fifo_elem α))) :=
  List.Forall (λ fe, fst cfel == power (fe_t₁ fe) + power (fe_t₂ fe))
    (snd cfel).

Definition fifo_exists_k α comden (cfel : (Q * list (fifo_elem α))) :=
  ∃ k : nat,
  (k * Pos.to_nat (Qden (fst cfel)) /
     gcd (Z.abs_nat (Qnum (fst cfel))) (Pos.to_nat (Qden (fst cfel))) =
   comden)%nat.

Lemma insert_same_sum : ∀ α sum fe₁ (fel : list (fifo_elem α)),
  List.Forall (λ fe, sum == power (fe_t₁ fe) + power (fe_t₂ fe)) fel
  → power (fe_t₁ fe₁) + power (fe_t₂ fe₁) == sum
    → List.Forall (λ fe, sum == power (fe_t₁ fe) + power (fe_t₂ fe))
       (insert_elem fe₁ fel).
Proof.
intros α sum fe₁ fel Hf Hp.
symmetry in Hp.
revert sum fe₁ Hf Hp.
induction fel as [| fe₂]; intros.
 constructor; assumption.

 apply list_Forall_inv in Hf.
 destruct Hf as (Hs, Hf).
 simpl.
 remember (power (fe_t₁ fe₁) ?= power (fe_t₁ fe₂)) as c₁.
 destruct c₁.
  remember (power (fe_t₂ fe₁) ?= power (fe_t₂ fe₂)) as c₂.
  destruct c₂; [ constructor; assumption | idtac | idtac ].
   constructor; [ assumption | constructor; assumption ].

   constructor; [ assumption | apply IHfel; assumption ].

  constructor; [ assumption | constructor; assumption ].

  constructor; [ assumption | apply IHfel; assumption ].
Qed.

Lemma fifo_insert_same : ∀ α sum fe fel (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) [(sum, fel) … sf]
  → power (fe_t₁ fe) + power (fe_t₂ fe) == sum
    → List.Forall (λ cfel, fifo_sum_prop cfel)
        [(sum, insert_elem fe fel) … sf].
Proof.
intros α sum fe fel sf H Hp.
apply list_Forall_inv in H.
destruct H as (Hf, H).
destruct fel as [| fe₁]; simpl.
 constructor; [ idtac | assumption ].
 unfold fifo_sum_prop; simpl.
 constructor; [ symmetry; assumption | constructor ].

 remember (power (fe_t₁ fe) ?= power (fe_t₁ fe₁)) as c.
 symmetry in Heqc.
 destruct c.
  remember (power (fe_t₂ fe) ?= power (fe_t₂ fe₁)) as c₂.
  symmetry in Heqc₂.
  destruct c₂; [ constructor; assumption | idtac | idtac ].
   constructor; [ idtac | assumption ].
   unfold fifo_sum_prop; simpl.
   constructor; [ symmetry; assumption | assumption ].

   constructor; [ idtac | assumption ].
   unfold fifo_sum_prop in Hf; simpl in Hf.
   apply list_Forall_inv in Hf.
   destruct Hf.
   constructor; [ assumption | idtac ].
   apply insert_same_sum; assumption.

  constructor; [ idtac | assumption ].
  unfold fifo_sum_prop; simpl.
  constructor; [ symmetry; assumption | assumption ].

  constructor; [ idtac | assumption ].
  unfold fifo_sum_prop in Hf; simpl in Hf.
  apply list_Forall_inv in Hf.
  destruct Hf.
  constructor; [ assumption | idtac ].
  apply insert_same_sum; assumption.
Qed.

(*
Lemma uuu : ∀ α fe P (sf : list (_ * list (fifo_elem α))),
  List.Forall P sf
  → List.Forall P (insert_sum (power (fe_t₁ fe) + power (fe_t₂ fe)) fe sf).
Proof.
intros α fe P sf H.
induction sf as [| (sum₁, fel₁)].
 constructor; [ idtac | constructor ].
bbb.
*)

Lemma fifo_insert : ∀ α fe (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) sf
  → List.Forall (λ cfel, fifo_sum_prop cfel)
      (insert_sum (power (fe_t₁ fe) + power (fe_t₂ fe)) fe sf).
Proof.
intros α fe sf H.
induction sf as [| (sum₁, fel₁)].
 constructor; [ idtac | constructor ].
 unfold fifo_sum_prop; simpl.
 constructor; [ reflexivity | constructor ].

 simpl.
 remember (power (fe_t₁ fe) + power (fe_t₂ fe) ?= sum₁) as c.
 symmetry in Heqc.
 destruct c.
  apply Qeq_alt in Heqc.
  apply fifo_insert_same; assumption.

  constructor; [ idtac | assumption ].
  constructor; [ reflexivity | constructor ].

  apply list_Forall_inv in H.
  destruct H as (Hf, H).
  constructor; [ assumption | apply IHsf; assumption ].
Qed.

Lemma fifo_insert_var : ∀ α fe t₁ t₂ (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) sf
  → t₁ = fe_t₁ fe
    → t₂ = fe_t₂ fe
      → List.Forall (λ cfel, fifo_sum_prop cfel)
          (insert_sum (power t₁ + power t₂) fe sf).
Proof.
intros α fe t₁ t₂ sf H H₁ H₂.
subst t₁ t₂.
apply fifo_insert; assumption.
Qed.

(*
Lemma www : ∀ α fe t₁ t₂ cd₁ cd₂ (sf : list (_ * list (fifo_elem α))),
  List.Forall (fifo_exists_k cd₁ cd₂) sf
  → t₁ = fe_t₁ fe
    → t₂ = fe_t₂ fe
      → List.Forall (fifo_exists_k cd₁ cd₂)
            (insert_sum (power t₁ + power t₂) fe sf).
Proof.
intros α fe t₁ t₂ cd₁ cd₂ sf H H₁ H₂.
subst t₁ t₂.
induction sf as [| (sum₁, fel₁)].
 constructor; [ idtac | constructor ].
 unfold fifo_exists_k; simpl.
bbb.
*)

(*
Lemma vvv : ∀ α fe t₁ t₂ P (sf : list (_ * list (fifo_elem α))),
  List.Forall P sf
  → t₁ = fe_t₁ fe
    → t₂ = fe_t₂ fe
      → List.Forall P (insert_sum (power t₁ + power t₂) fe sf).
Proof.
intros α fe t₁ t₂ P sf H H₁ H₂.
subst t₁ t₂.
bbb.

Lemma www : ∀ α mul_coeff t₁ t₂ fe fel P
    (sf : list (_ * list (fifo_elem α))),
  List.Forall P sf
  → t₁ = fe_t₁ fe
    → t₂ = fe_t₂ fe
      → List.Forall P
          (add_right mul_coeff (insert_sum (power t₁ + power t₂) fe sf) fel).
Proof.
intros α mul_coeff t₁ t₂ fe fel P sf H H₁ H₂.
revert t₁ t₂ fe sf H H₁ H₂.
induction fel as [| fe₁]; intros; simpl.
bbb.
*)

Lemma fifo_add_sum_right : ∀ α mul_coeff t₁ t₂ fe fel
    (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) sf
  → t₁ = fe_t₁ fe
    → t₂ = fe_t₂ fe
      → List.Forall (λ cfel, fifo_sum_prop cfel)
          (add_right mul_coeff (insert_sum (power t₁ + power t₂) fe sf) fel).
Proof.
intros α mul_coeff t₁ t₂ fe fel sf H H₁ H₂.
revert t₁ t₂ fe sf H H₁ H₂.
induction fel as [| fe₁]; intros; simpl.
 apply fifo_insert_var; assumption.

 remember (fe_s₂ fe₁) as s₂.
 destruct s₂.
  rename t into tt₂.
  apply IHfel; [ idtac | reflexivity | reflexivity ].
  apply fifo_insert_var; assumption.

  apply IHfel; assumption.
Qed.

(*
Lemma xxx : ∀ α mul_coeff t₁ t₂ cd₁ cd₂ fe fel
    (sf : list (_ * list (fifo_elem α))),
  List.Forall (fifo_exists_k cd₁ cd₂) sf
  → List.Forall (fifo_exists_k cd₁ cd₂) (add_right mul_coeff sf fel)
    → t₁ = fe_t₁ fe
      → t₂ = fe_t₂ fe
        → List.Forall (fifo_exists_k cd₁ cd₂)
            (add_right mul_coeff (insert_sum (power t₁ + power t₂) fe sf)
               fel).
Proof.
intros α mul_coeff t₁ t₂ cd₁ cd₂ fe fel sf Hf Hrf H₁ H₂.
revert t₁ t₂ cd₁ cd₂ fe sf Hf Hrf H₁ H₂.
induction fel as [| fe₁]; intros; simpl.
 Focus 2.
 remember (fe_s₂ fe₁) as s₂.
 destruct s₂.
  rename t into tt₂.
  apply IHfel; [ idtac | reflexivity | reflexivity ].
  Focus 2.
  apply IHfel; assumption.

  Unfocus.
bbb.
*)

Lemma fifo_add_sum_below : ∀ α mul_coeff t₁ t₂ fe fel
    (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) sf
  → t₁ = fe_t₁ fe
    → t₂ = fe_t₂ fe
      → List.Forall (λ cfel, fifo_sum_prop cfel)
          (add_below mul_coeff (insert_sum (power t₁ + power t₂) fe sf) fel).
Proof.
intros α mul_coeff t₁ t₂ fe fel sf H H₁ H₂.
revert t₁ t₂ fe sf H H₁ H₂.
induction fel as [| fe₁]; intros; simpl.
 apply fifo_insert_var; assumption.

 remember (fe_s₁ fe₁) as s₁.
 destruct s₁.
  rename t into tt₁.
  apply IHfel; [ idtac | reflexivity | reflexivity ].
  apply fifo_insert_var; assumption.

  apply IHfel; assumption.
Qed.

Lemma fifo_add_below : ∀ α mul_coeff fel (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) sf
  → List.Forall (λ cfel, fifo_sum_prop cfel) (add_below mul_coeff sf fel).
Proof.
intros α mul_coeff fel sf H.
induction fel as [| fe]; intros; [ assumption | simpl ].
remember (fe_s₁ fe) as ss₁.
destruct ss₁.
 apply fifo_add_sum_below; [ assumption | reflexivity | reflexivity ].

 apply IHfel; assumption.
Qed.

Lemma fifo_add_right : ∀ α mul_coeff fel (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) sf
  → List.Forall (λ cfel, fifo_sum_prop cfel) (add_right mul_coeff sf fel).
Proof.
intros α mul_coeff fel sf H.
induction fel as [| fe]; intros; [ assumption | simpl ].
remember (fe_s₂ fe) as ss₂.
destruct ss₂.
 apply fifo_add_sum_right; [ assumption | reflexivity | reflexivity ].

 apply IHfel; assumption.
Qed.

(*
Lemma yyy : ∀ α mul_coeff cd₁ cd₂ fel (sf : list (_ * list (fifo_elem α))),
  List.Forall (fifo_exists_k cd₁ cd₂) sf
  → List.Forall (fifo_exists_k cd₁ cd₂) (add_right mul_coeff sf fel).
Proof.
intros α mul_coeff cd₁ cd₂ fel sf H.
induction fel as [| fe]; intros; [ assumption | simpl ].
remember (fe_s₂ fe) as ss₂.
destruct ss₂.
bbb.

 Focus 2.
 apply IHfel; assumption.
bbb.
*)

Open Scope nat_scope.

(*
Lemma xxx : ∀ s a b c k₁,
  s == a + b
  → k₁ * Pos.to_nat (Qden s) = c
    → ∃ k : nat, k * Pos.to_nat (Qden a * Qden b) = c.
Proof.
intros s a b c k₁ Hs Hc.
bbb.
*)

Close Scope nat_scope.

(*
Lemma yyy : ∀ α mul_coeff t₁ t₂ cd₁ cd₂ sum fe fel
     (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) [(sum, [fe … fel]) … sf]
  → List.Forall (fifo_exists_k cd₁ cd₂) [(sum, [fe … fel]) … sf]
    → t₁ = fe_t₁ fe
      → t₂ = fe_t₂ fe
        → List.Forall (fifo_exists_k cd₁ cd₂)
            (add_right mul_coeff (insert_sum (power t₁ + power t₂) fe sf)
               fel).
Proof.
intros α mul_coeff t₁ t₂ cd₁ cd₂ sum fe fel sf Hs Hk.
induction fel as [| fe₁]; intros; simpl.
 induction sf as [| (sum₁, fel₁)].
  constructor; [ idtac | constructor ].
  unfold fifo_exists_k; simpl.
  apply list_Forall_inv in Hk.
  destruct Hk as (He, _).
  unfold fifo_exists_k in He.
  destruct He as (k₁, He).
  apply list_Forall_inv in Hs.
  destruct Hs as (Hf, _).
  unfold fifo_sum_prop in Hf; simpl in Hf.
  apply list_Forall_inv in Hf.
  destruct Hf as (Hf, _).
  simpl in He.
bbb.
*)

(**)
Lemma zzz : ∀ α add_coeff mul_coeff cd (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) sf
  → List.Forall (fifo_exists_k cd) sf
    → series_forall (pow_den_div_com_den cd)
        (ps_mul_loop add_coeff mul_coeff sf).
Proof.
cofix IHs.
intros α add_coeff mul_coeff cd sf Hs Hk.
rewrite series_eta; simpl.
destruct sf as [| (sum, fel)]; [ constructor; reflexivity | idtac ].
destruct fel as [| fe]; [ constructor; reflexivity | idtac ].
eapply TermAndFurther; [ reflexivity | idtac | idtac ].
 unfold pow_den_div_com_den; simpl.
 apply List.Forall_inv in Hk.
 unfold fifo_exists_k in Hk; simpl in Hk.
 destruct Hk as (k₁, Hk).
 Focus 1.
bbb.

 assumption.

 eapply IHs; try eassumption.
  apply list_Forall_inv in Hs.
  destruct Hs as (Hf, Hs).
  remember (fe_s₂ fe) as ss₂.
  destruct ss₂.
   rename t into tt₂.
   remember (fe_s₁ fe) as ss₁.
   destruct ss₁.
    apply fifo_add_sum_right; [ idtac | reflexivity | reflexivity ].
    apply fifo_add_sum_below; [ assumption | reflexivity | reflexivity ].

    apply fifo_add_sum_right; [ idtac | reflexivity | reflexivity ].
    apply fifo_add_below; assumption.

   apply fifo_add_right, fifo_add_below.
   remember (fe_s₁ fe) as ss₁.
   destruct ss₁; [ idtac | assumption ].
   apply fifo_insert_var; [ assumption | reflexivity | reflexivity ].

  remember (fe_s₂ fe) as ss₂.
  destruct ss₂.
   rename t into tt₂.
   remember (fe_s₁ fe) as ss₁.
   destruct ss₁.
    rename t into tt₁.
bbb.
*)

Lemma series_forall_mul : ∀ α (add_coeff : α → α → α) mul_coeff s₁ s₂ cd₁ cd₂,
  series_forall (pow_den_div_com_den cd₁) s₁
  → series_forall (pow_den_div_com_den cd₂) s₂
    → series_forall (pow_den_div_com_den (cd₁ * cd₂))
        (ps_mul_term add_coeff mul_coeff s₁ s₂).
Proof.
intros α add_coeff mul_coeff s₁ s₂ cd₁ cd₂ Hps₁ Hps₂.
unfold ps_mul_term.
destruct s₁; [ idtac | constructor; reflexivity ].
rename t into t₁.
destruct s₂; [ idtac | constructor; reflexivity ].
rename t into t₂.
apply series_forall_inv in Hps₁.
apply series_forall_inv in Hps₂.
destruct Hps₁ as (Hp₁, Hs₁).
destruct Hps₂ as (Hp₂, Hs₂).
unfold pow_den_div_com_den in Hp₁; simpl in Hp₁.
unfold pow_den_div_com_den in Hp₂; simpl in Hp₂.
destruct Hp₁ as (k₁, Hp₁).
destruct Hp₂ as (k₂, Hp₂).
bbb.

eapply zzz; try eassumption.
 constructor; [ simpl | constructor ].
 constructor; [ reflexivity | constructor ].

 constructor; [ simpl | constructor ].
 apply series_forall_inv in Hps₁.
 apply series_forall_inv in Hps₂.
 destruct Hps₁ as (Hpd₁, Hsf₁).
 destruct Hps₂ as (Hpd₂, Hsf₂).
 unfold pow_den_div_com_den in Hpd₁, Hpd₂.
 destruct Hpd₁ as (k₁, Hpd₁).
 destruct Hpd₂ as (k₂, Hpd₂).
 exists (k₁ * k₂)%nat.
 subst cd₁.
 rewrite <- mult_assoc.
 destruct k₁; [ reflexivity | idtac ].
 rewrite <- mult_assoc.
 apply Nat.mul_cancel_l; [ intros H; discriminate H | idtac ].
 rewrite mult_comm.
 rewrite mult_comm in Hpd₂; subst cd₂.
 rewrite mult_assoc.
 destruct k₂; [ do 2 rewrite mult_0_r; reflexivity | idtac ].
 apply <- Nat.mul_cancel_r; [ idtac | intros H; discriminate H ].
 simpl; rewrite Pos2Nat.inj_mul.
 reflexivity.
qed.
*)

Theorem ps_prop_mul : ∀ α (add_coeff : α → α → α) mul_coeff ps₁ ps₂,
  series_forall
    (pow_den_div_com_den (ps_comden ps₁ * ps_comden ps₂))
    (ps_mul_term add_coeff mul_coeff (ps_terms ps₁) (ps_terms ps₂)).
Proof.
intros α add_coeff mul_coeff ps₁ ps₂.
apply series_forall_mul; [ apply (ps_prop ps₁) | apply (ps_prop ps₂) ].
Qed.

Definition ps_mul α add_coeff mul_coeff (ps₁ ps₂ : puiseux_series α) :=
  {| ps_terms :=
       ps_mul_term add_coeff mul_coeff (ps_terms ps₁) (ps_terms ps₂);
     ps_comden :=
       ps_comden ps₁ * ps_comden ps₂;
     ps_prop :=
       ps_prop_mul add_coeff mul_coeff ps₁ ps₂ |}.

Fixpoint insert_pol_term α (add_coeff : α → α → α) c₁ p₁ ml :=
  match ml with
  | [] => [(c₁, p₁)]
  | [(c₂, p₂) … ml₂] =>
      match nat_compare p₁ p₂ with
      | Eq => [(add_coeff c₁ c₂, p₂) … ml₂]
      | Lt => [(c₁, p₁) … ml]
      | Gt => [(c₂, p₂) … insert_pol_term add_coeff c₁ p₁ ml₂]
      end
  end.

Fixpoint combine_pol α add_coeff (mul_coeff : α → α → α) c₁ pow₁ pow₂ ml
    cn cl :=
  let p := (pow₁ + pow₂)%nat in
  match cl with
  | [] =>
      let c := mul_coeff c₁ cn in
      insert_pol_term add_coeff c p ml
  | [c₂ … cl₂] =>
      let c := mul_coeff c₁ c₂ in
      let ml := insert_pol_term add_coeff c p ml in
      combine_pol add_coeff mul_coeff c₁ pow₁ (S pow₂) ml cn cl₂
  end.

Fixpoint mul_loop α (add_coeff : α → α → α) mul_coeff ml pow₁ cn₂ cl₂
    cn₁ cl₁ :=
  match cl₁ with
  | [] => combine_pol add_coeff mul_coeff cn₁ pow₁ 0 ml cn₂ cl₂
  | [c … cl] =>
      let ml := combine_pol add_coeff mul_coeff c pow₁ 0 ml cn₂ cl₂ in
      mul_loop add_coeff mul_coeff ml (S pow₁) cn₂ cl₂ cn₁ cl
  end.

Fixpoint make_pol α (zero_coeff : α) pow ml n :=
  match n with
  | O => ([], zero_coeff)
  | S n₁ =>
      match ml with
      | [] => ([], zero_coeff)
      | [(c, p)] =>
          if eq_nat_dec p pow then ([], c)
          else
            let (cl, cn) := make_pol zero_coeff (S pow) [(c, p)] n₁ in
            ([zero_coeff … cl], cn)
      | [(c, p) … ml₁] =>
          if eq_nat_dec p pow then
            let (cl, cn) := make_pol zero_coeff (S pow) ml₁ n₁ in
            ([c … cl], cn)
          else
            let (cl, cn) := make_pol zero_coeff (S pow) ml n₁ in
            ([zero_coeff … cl], cn)
      end
  end.

Definition pol_mul α (zero_coeff : α) add_coeff mul_coeff pol₁ pol₂ :=
  let ml :=
    mul_loop add_coeff mul_coeff [] 0 (an pol₂) (al pol₂) (an pol₁) (al pol₁)
  in
  let (cl, cn) := make_pol zero_coeff 0 ml (List.length ml) in
  {| al := cl; an := cn |}.

Definition apply_poly_with_ps_poly α (fld : field α) pol :=
  apply_poly
    (λ ps, {| al := []; an := ps |})
    (λ pol ps, pol_add (ps_add (add fld)) pol {| al := []; an := ps |})
    (pol_mul
       {| ps_terms := End _; ps_comden := 1 |}
       (ps_add (add fld))
       (ps_mul (add fld) (mul fld)))
    pol.

Definition mul_x_power_minus α p (ps : puiseux_series α) :=
  let t :=
    series_map
      (λ m, {| coeff := coeff m; power := Qred (Qminus (power m) p) |})
      (ps_terms ps)
  in
  {| ps_terms := t; ps_comden := ps_comden ps |}.

Definition pol_mul_x_power_minus α p (pol : polynomial (puiseux_series α)) :=
  let cl := List.map (mul_x_power_minus p) (al pol) in
  let cn := mul_x_power_minus p (an pol) in
  {| al := cl; an := cn |}.

Definition pos_to_nat := Pos.to_nat.

Definition f₁ α (fld : field α) (f : polynomial (puiseux_series α)) β γ c :=
  let y :=
    {| al :=
         [{| ps_terms := Term {| coeff := c; power := γ |} (End _);
             ps_comden := pos_to_nat (Qden γ) |}];
       an :=
         {| ps_terms := Term {| coeff := one fld; power := γ |} (End _);
            ps_comden := pos_to_nat (Qden γ) |} |}
  in
  let pol := apply_poly_with_ps_poly fld f y in
  pol_mul_x_power_minus β pol.

(* *)

Definition apply_polynomial α (fld : field α) :=
  apply_poly (λ x, x) (add fld) (mul fld).

Record algeb_closed_field α :=
  { ac_field : field α;
    ac_root : polynomial α → (α * nat);
    ac_prop : ∀ pol, degree pol ≥ 1
      → apply_polynomial ac_field pol (fst (ac_root pol)) = zero ac_field }.

Definition nofq q := Z.to_nat (Qnum q).

Fixpoint make_char_pol α (fld : field α) cdeg dcl n :=
  match n with
  | O => []
  | S n₁ =>
      match dcl with
      | [] =>
          [zero fld … make_char_pol fld (S cdeg) [] n₁]
      | [(deg, coeff) … dcl₁] =>
          if eq_nat_dec deg cdeg then
            [coeff … make_char_pol fld (S cdeg) dcl₁ n₁]
          else
            [zero fld … make_char_pol fld (S cdeg) dcl n₁]
      end
    end.

Definition deg_coeff_of_point α (fld : field α) pol (pt : (Q * Q)) :=
  let h := nofq (fst pt) in
  let ps := List.nth h (al pol) (an pol) in
  let c := valuation_coeff fld ps in
  (h, c).

Definition characteristic_polynomial α (fld : field α) pol ns :=
  let dcl := List.map (deg_coeff_of_point fld pol) [ini_pt ns … oth_pts ns] in
  let j := nofq (fst (ini_pt ns)) in
  let k := nofq (fst (fin_pt ns)) in
  let cl := make_char_pol fld j dcl (k - j) in
  let kps := List.nth k (al pol) (an pol) in
  {| al := cl; an := valuation_coeff fld kps |}.

Definition zero_is_root α (pol : polynomial (puiseux_series α)) :=
  match al pol with
  | [] => false
  | [ps … _] =>
      match series_head (ps_terms ps) with
      | Term _ _ => false
      | End => true
      end
  end.

Definition puiseux_step α psumo acf (pol : polynomial (puiseux_series α)) :=
  let nsl₁ := newton_segments pol in
  let (nsl, psum) :=
    match psumo with
    | Some psum => (List.filter (λ ns, negb (Qle_bool (γ ns) 0)) nsl₁, psum)
    | None => (nsl₁, 0)
    end
  in
  match nsl with
  | [] => None
  | [ns … _] =>
      let fld := ac_field acf in
      let cpol := characteristic_polynomial fld pol ns in
      let (c, r) := ac_root acf cpol in
      let pol₁ := f₁ fld pol (β ns) (γ ns) c in
      let p := Qplus psum (γ ns) in
      Some ({| coeff := c; power := p |}, pol₁)
  end.

CoFixpoint puiseux_loop α psumo acf (pol : polynomial (puiseux_series α)) :=
  match puiseux_step psumo acf pol with
  | Some (t, pol₁) =>
      Term t
        (if zero_is_root pol₁ then End _
         else puiseux_loop (Some (power t)) acf pol₁)
  | None =>
      End _
  end.

Definition puiseux_root α acf (pol : polynomial (puiseux_series α)) :=
  {| ps_terms := puiseux_loop None acf pol; ps_comden := 1 |}.

(*
Definition ps_inv α (add_coeff : α → α → α) mul_coeff x :=
  ...

Definition ps_div α (add_coeff : α → α → α) mul_coeff x y :=
  ps_mul add_coeff mul_coeff x (ps_inv y).
*)

Definition ps_zero α := {| ps_terms := End (term α); ps_comden := 1 |}.
Definition ps_one α fld :=
  {| ps_terms := Term {| coeff := one fld; power := 0 |} (End (term α));
     ps_comden := 1 |}.
Definition ps_add_fld α (fld : field α) x y := ps_add (add fld) x y.
Definition ps_mul_fld α (fld : field α) x y := ps_mul (add fld) (mul fld) x y.

Definition ps_fld α (fld : field α) :=
  {| zero := ps_zero _;
     one := ps_one fld;
     add := ps_add_fld fld;
     mul := ps_mul_fld fld |}.

(* *)

CoFixpoint series_series_take α n (s : series α) :=
  match n with
  | O => End _
  | S n₁ =>
      match s with
      | Term a t => Term a (series_series_take n₁ t)
      | End => End _
      end
  end.

(*
Theorem zzz : ∀ α acf (pol : polynomial (puiseux_series α)) r,
  degree pol ≥ 1
  → r = puiseux_root acf pol
    → apply_polynomial (ps_fld (ac_field acf)) pol r =
      zero (ps_fld (ac_field acf)).
Proof.
intros α acf pol r Hdeg Hr.
subst r.
remember (puiseux_root acf pol) as pr.
remember (ps_terms pr) as sr.
remember (series_hd sr) as shd.
remember (series_tl sr) as stl.
unfold puiseux_root in Heqpr.
rewrite Heqpr in Heqsr.
subst sr; simpl in Heqshd, Heqstl.
remember (puiseux_step None acf pol) as pso.
unfold puiseux_step in Heqpso.
remember (newton_segments pol) as nsl.
destruct nsl.
 subst pso; simpl in Heqshd, Heqstl.
 unfold newton_segments in Heqnsl.
 symmetry in Heqnsl.
 apply list_map_pairs_length in Heqnsl.
 simpl in Heqnsl.
 unfold lower_convex_hull_points in Heqnsl.
bbb.

 Focus 2.
 remember (ac_field acf) as fld.
 remember (characteristic_polynomial fld pol n) as cpol.
 remember (ac_root acf cpol) as cr.
 destruct cr as (c, r).
 subst pso; simpl in Heqshd, Heqstl.
 rewrite surjective_pairing in Heqcr.
 injection Heqcr; clear Heqcr; intros Heqr Heqc.
 destruct r.
  Focus 2.
  subst fld.
  revert pol pr shd stl n nsl cpol c Hdeg Heqpr Heqnsl Heqshd Heqr Heqc
   Heqcpol Heqstl.
  induction r; intros.
   Focus 2.
bbb.
*)

Section field.

Variable α : Type.
Variable fld : field (puiseux_series α).

(* *)

Lemma pt_absc_is_nat : ∀ (pol : puis_ser_pol α) pts pt,
  points_of_ps_polynom pol = pts
  → pt ∈ pts
    → ∃ n, fst pt = Qnat n.
Proof.
intros pol pts pt Hpts Hαh.
unfold points_of_ps_polynom in Hpts.
remember (al pol) as cl; clear Heqcl.
remember (an pol) as cn; clear Heqcn.
remember 0%nat as n in Hpts; clear Heqn.
unfold points_of_ps_polynom_gen in Hpts.
revert n pts Hpts Hαh.
induction cl as [| c]; intros.
 simpl in Hpts.
 destruct (valuation cn) as [v| ].
  subst pts.
  destruct Hαh as [Hαh| ]; [ subst pt; simpl | contradiction ].
  exists n; reflexivity.

  subst pts; contradiction.

 simpl in Hpts.
 destruct (valuation c) as [v| ].
  subst pts.
  destruct Hαh as [Hαh| Hαh]; [ subst pt; simpl | idtac ].
   exists n; reflexivity.

   eapply IHcl in Hαh; [ assumption | reflexivity ].

  eapply IHcl; eassumption.
Qed.

Lemma hull_seg_vert_in_init_pts : ∀ n pts hs hsl,
  next_ch_points n pts = hsl
  → hs ∈ hsl
    → pt hs ∈ pts.
Proof.
intros n pts hs hsl Hnp Hhs.
revert n pts hs Hnp Hhs.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct Hhs as [Hhs| Hhs].
 subst hs₁.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂].
  injection Hnp; intros; subst hs; left; reflexivity.

  injection Hnp; clear Hnp; intros Hnp Hhs.
  subst hs; left; reflexivity.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂].
  injection Hnp; intros; subst hsl; contradiction.

  injection Hnp; clear Hnp; intros Hnp Hs₁; subst hs₁.
  eapply IHhsl in Hhs; [ idtac | eassumption ].
  remember (minimise_slope pt₁ pt₂ pts) as ms₁.
  symmetry in Heqms₁.
  destruct Hhs as [Hhs| Hhs].
   rewrite <- Hhs.
   right; eapply end_pt_in; eassumption.

   right; right; eapply rem_pts_in; eassumption.
Qed.

Lemma ini_fin_ns_in_init_pts : ∀ pts ns,
  ns ∈ list_map_pairs newton_segment_of_pair (lower_convex_hull_points pts)
  → ini_pt ns ∈ pts ∧ fin_pt ns ∈ pts.
Proof.
intros pts ns Hns.
remember (lower_convex_hull_points pts) as hsl.
unfold lower_convex_hull_points in Heqhsl.
remember (length pts) as n; clear Heqn.
rename Heqhsl into Hnp; symmetry in Hnp.
revert pts ns n Hnp Hns.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct hsl as [| hs₂]; [ contradiction | idtac ].
destruct Hns as [Hns| Hns].
 subst ns; simpl.
 split.
  eapply hull_seg_vert_in_init_pts; [ eassumption | idtac ].
  left; reflexivity.

  eapply hull_seg_vert_in_init_pts; [ eassumption | idtac ].
  right; left; reflexivity.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
 eapply IHhsl in Hnp; [ idtac | eassumption ].
 remember (minimise_slope pt₁ pt₂ pts) as ms₁.
 symmetry in Heqms₁.
 destruct Hnp as (Hini, Hfin).
 split.
  destruct Hini as [Hini| Hini].
   rewrite <- Hini.
   right; eapply end_pt_in; eassumption.

   right; right; eapply rem_pts_in; eassumption.

  destruct Hfin as [Hfin| Hfin].
   rewrite <- Hfin.
   right; eapply end_pt_in; eassumption.

   right; right; eapply rem_pts_in; eassumption.
Qed.

Lemma j_lt_k : ∀ (pol : puis_ser_pol α) j k ns,
  ns ∈ newton_segments pol
  → j = nofq (fst (ini_pt ns))
    → k = nofq (fst (fin_pt ns))
      → (j < k)%nat.
Proof.
intros pol j k ns Hns Hj Hk.
unfold newton_segments in Hns.
remember (points_of_ps_polynom pol) as pts.
remember Heqpts as Hj₁; clear HeqHj₁; symmetry in Hj₁.
eapply pt_absc_is_nat with (pt := ini_pt ns) in Hj₁.
 remember Heqpts as Hk₁; clear HeqHk₁; symmetry in Hk₁.
 eapply pt_absc_is_nat with (pt := fin_pt ns) in Hk₁.
  apply points_of_polyn_sorted in Heqpts.
  rename Heqpts into Hsort.
  remember (lower_convex_hull_points pts) as hsl.
  unfold lower_convex_hull_points in Heqhsl.
  rename Heqhsl into Hnp.
  symmetry in Hnp.
  remember (length pts) as n; clear Heqn.
  remember (list_map_pairs newton_segment_of_pair hsl) as nsl.
  symmetry in Heqnsl.
  revert n pts ns nsl j k Hsort Hnp Hns Hj Hk Hj₁ Hk₁ Heqnsl.
  induction hsl as [| hs₁]; intros; [ subst nsl; contradiction | idtac ].
  destruct nsl as [| ns₁]; [ contradiction | idtac ].
  destruct Hns as [Hns| Hns].
   subst ns₁.
   simpl in Heqnsl.
   destruct hsl as [| hs₂]; [ discriminate Heqnsl | idtac ].
   injection Heqnsl; clear Heqnsl; intros Hnsl Hns.
   unfold newton_segment_of_pair in Hns.
   subst ns.
   simpl in Hj, Hk, Hj₁, Hk₁.
   apply next_points_sorted in Hnp; [ idtac | assumption ].
   apply Sorted_inv_2 in Hnp; destruct Hnp as (Hlt, Hnp).
   unfold hs_x_lt in Hlt; simpl in Hlt.
   unfold Qlt in Hlt.
   destruct Hj₁ as (jn, Hjn).
   destruct Hk₁ as (kn, Hkn).
   rewrite Hjn in Hj, Hlt.
   rewrite Hkn in Hk, Hlt.
   unfold nofq, Qnat in Hj, Hk.
   simpl in Hj, Hk.
   rewrite Nat2Z.id in Hj, Hk.
   subst jn kn.
   unfold Qnat in Hlt; simpl in Hlt.
   do 2 rewrite Zmult_1_r in Hlt.
   apply Nat2Z.inj_lt; assumption.

   destruct n; [ discriminate Hnp | simpl in Hnp ].
   destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
   destruct pts as [| pt₂].
    injection Hnp; clear Hnp; intros; subst hs₁ hsl.
    discriminate Heqnsl.

    injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
    simpl in Heqnsl.
    destruct hsl as [| hs₁]; [ discriminate Heqnsl | idtac ].
    remember [hs₁ … hsl] as x.
    injection Heqnsl; clear Heqnsl; intros Hnsl Hns₁; subst x.
    remember (minimise_slope pt₁ pt₂ pts) as ms.
    symmetry in Heqms.
    eapply IHhsl with (pts := [end_pt ms … rem_pts ms]); try eassumption.
    eapply minimise_slope_sorted; eassumption.

  apply ini_fin_ns_in_init_pts; eassumption.

 apply ini_fin_ns_in_init_pts; eassumption.
Qed.

Lemma cpol_degree : ∀ acf (pol : puis_ser_pol α) cpol ns,
  ns ∈ newton_segments pol
  → cpol = characteristic_polynomial (ac_field acf) pol ns
    → degree cpol ≥ 1.
Proof.
intros acf pol cpol ns Hns Hpol.
subst cpol.
unfold characteristic_polynomial, degree; simpl.
remember (nofq (fst (ini_pt ns))) as j.
remember (nofq (fst (fin_pt ns))) as k.
remember (k - j)%nat as kj.
destruct kj; simpl.
 eapply j_lt_k with (j := j) in Hns; try eassumption.
 apply NPeano.Nat.sub_gt in Hns.
 symmetry in Heqkj; contradiction.

 rewrite <- Heqj.
 destruct (eq_nat_dec j j) as [| H]; [ apply le_n_S, le_0_n | idtac ].
 exfalso; apply H; reflexivity.
Qed.

Lemma exists_root : ∀ acf (pol : puis_ser_pol α) cpol ns,
  ns ∈ newton_segments pol
  → cpol = characteristic_polynomial (ac_field acf) pol ns
    → ∃ c, apply_polynomial (ac_field acf) cpol c = zero (ac_field acf).
Proof.
intros acf pol cpol ns Hdeg Hpol.
eapply cpol_degree in Hdeg; [ idtac | eassumption ].
remember (ac_root acf cpol) as r.
destruct r as (c, r).
exists c.
rewrite surjective_pairing in Heqr.
injection Heqr; clear Heqr; intros; subst c.
apply (ac_prop acf cpol Hdeg).
Qed.

(* *)

Fixpoint val_den_prod (psl : list (puiseux_series α)) :=
  match psl with
  | [] => 1%nat
  | [ps₁ … psl₁] =>
      match valuation ps₁ with
      | Some v => (pos_to_nat (Qden v) * val_den_prod psl₁)%nat
      | None => val_den_prod psl₁
      end
  end.

(* common_denominator_in_polynomial *)
Lemma zzz : ∀ (psl : list (puiseux_series α)),
  ∃ m, ∀ ps αi mi, ps ∈ psl
  → valuation ps = Some αi → ps_comden ps = mi
    → αi == Qnat mi / Qnat m.
Proof.
intros psl.
remember (val_den_prod psl) as m.
exists m.
intros ps αi mi Hps Hval Hcd.
bbb.
revert ps αi mi m Hps Hval Hcd Heqm.
induction psl as [| ps₁]; [ contradiction | intros ].
destruct Hps as [Hps| Hps].
 subst ps₁.
 simpl in Heqm.
 rewrite Hval in Heqm.
bbb.

Theorem has_neg_slope : ∀ acf pol ns cpol (c : α) r pol₁,
  ns ∈ newton_segments pol
  → cpol = characteristic_polynomial (ac_field acf) pol ns
    → (c, r) = ac_root acf cpol
      → pol₁ = f₁ (ac_field acf) pol (β ns) (γ ns) c
        → ∃ ns₁, ns₁ ∈ newton_segments pol₁ → γ ns₁ > 0.
Proof.
bbb.

End field.
