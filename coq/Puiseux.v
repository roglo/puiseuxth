(* $Id: Puiseux.v,v 1.720 2013-06-19 19:52:50 deraugla Exp $ *)

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

Fixpoint ps_add_loop α (add_coeff : α → α → α) ms₁ ms₂ :=
  match ms₁ with
  | Term c₁ s₁ =>
      let fix loop₂ ms₂ :=
        match ms₂ with
        | Term c₂ s₂ =>
            match Qcompare (power c₁) (power c₂) with
            | Eq =>
                let c := add_coeff (coeff c₁) (coeff c₂) in
                let m := {| coeff := c; power := power c₁ |} in
                Term m (λ tt, ps_add_loop add_coeff (s₁ tt) (s₂ tt))
            | Lt =>
                Term c₁ (λ tt, ps_add_loop add_coeff (s₁ tt) ms₂)
            | Gt =>
                Term c₂ (λ tt, loop₂ (s₂ tt))
            end
        | End => ms₂
        end
      in
      loop₂ ms₂
  | End => ms₂
  end.

Lemma series_forall_div_mul : ∀ α (s : series (term α)) cd x,
  series_forall (pow_den_div_com_den cd) s
  → series_forall (pow_den_div_com_den (cd * x)) s.
Proof.
intros α s cd x H.
induction s as [t s IHs| ]; [ idtac | constructor; reflexivity ].
eapply TermAndFurther; [ reflexivity | idtac | idtac ].
 apply series_forall_inv in H.
 destruct H as (H, _).
 unfold pow_den_div_com_den in H |- *.
 destruct H as (k₁, H).
 rewrite Pmult_comm.
 unfold den_divides_comden.
 exists (Zpos x * k₁)%Z.
 rewrite Pos2Z.inj_mul.
 rewrite <- Zmult_assoc, H, Zmult_assoc.
 reflexivity.

 apply series_forall_inv in H.
 destruct H as (_, H).
 eapply IHs; eassumption.
Qed.

Definition Plcm a b := Z.to_pos (Z.lcm (Zpos a) (Zpos b)).

Lemma Zlcm_pos : ∀ a b, (0 < Z.lcm (Zpos a) (Zpos b))%Z.
Proof.
intros a b.
unfold Z.lcm.
rewrite Z.abs_mul.
remember (Z.abs (' a)) as x; simpl in Heqx; subst x.
apply Z.mul_pos_pos; [ apply Pos2Z.is_pos | idtac ].
apply Z.abs_pos; simpl.
intros H.
apply Z.div_small_iff in H.
 destruct H as [H| H].
  destruct H as (Hb, Hbg).
  pose proof (Pos.gcd_divide_r a b) as H.
  destruct H as (z, H).
  rewrite H in Hbg at 1.
  rewrite Pos2Z.inj_mul in Hbg.
  remember (Pos.gcd a b) as x.
  remember (' z * ' x)%Z as y.
  replace (' x)%Z with (1 * ' x)%Z in Hbg by reflexivity; subst y.
  apply Zmult_lt_reg_r in Hbg; [ idtac | apply Pos2Z.is_pos ].
  apply Zlt_le_succ in Hbg.
  revert Hbg.
  apply Zlt_not_le, Z.lt_pred_lt_succ; simpl.
  apply Pos2Z.is_pos.

  destruct H as (Hg, Hb).
  revert Hb.
  apply Zlt_not_le, Pos2Z.is_pos.

 pose proof (Pos2Z.is_pos (Pos.gcd a b)) as HH.
 intros HHH.
 rewrite HHH in HH; apply Zlt_irrefl in HH; assumption.
Qed.

Lemma div_div_lcm : ∀ α a b (t : term α),
  pow_den_div_com_den a t
  → pow_den_div_com_den (Plcm a b) t.
Proof.
intros α a b t H.
unfold pow_den_div_com_den in H |- *.
unfold den_divides_comden in H |- *.
destruct H as (k, H).
unfold Z.divide.
unfold Plcm.
pose proof (Z.divide_lcm_l (' a) (' b)) as Hl.
destruct Hl as (k₁, Hl).
rewrite Hl.
destruct k₁.
 pose proof (Zlcm_pos a b)%Z as HH.
 rewrite Hl in HH; apply Zlt_irrefl in HH; contradiction.

 rewrite Z2Pos.inj_mul; try apply Pos2Z.is_pos.
 do 2 rewrite Pos2Z.id.
 rewrite Pos2Z.inj_mul.
 rewrite <- Zmult_assoc, H, Zmult_assoc.
 exists (' p * k)%Z; reflexivity.

 pose proof (Zlcm_pos a b)%Z as HH.
 rewrite Hl in HH.
 simpl in HH.
 apply Zlt_not_le in HH.
 exfalso; apply HH.
 apply Zlt_le_weak, Zlt_neg_0.
Qed.

Lemma series_forall_add : ∀ α (add_coeff : α → α → α) s₁ s₂ cd₁ cd₂,
  series_forall (pow_den_div_com_den cd₁) s₁
  → series_forall (pow_den_div_com_den cd₂) s₂
    → series_forall (pow_den_div_com_den (Plcm cd₁ cd₂))
        (ps_add_loop add_coeff s₁ s₂).
Proof.
intros α add_coeff s₁ s₂ cd₁ cd₂ Hps₁ Hps₂.
revert s₂ Hps₂.
induction s₁ as [t₁ s₁ IHs| ]; intros.
 induction s₂ as [t₂ s₂ IHs₂| ].
  simpl.
  remember (power t₁ ?= power t₂) as c.
  symmetry in Heqc.
  destruct c.
   apply Qeq_alt in Heqc.
   eapply TermAndFurther; [ reflexivity | idtac | idtac ].
    apply series_forall_inv in Hps₁.
    destruct Hps₁ as (Hpd₁, Hsf₁).
    unfold pow_den_div_com_den in Hpd₁ |- *; simpl.
    destruct Hpd₁ as (k₁, Hpd₁).
    unfold den_divides_comden.
    unfold Z.divide.
    exists (Zpos (Plcm cd₁ cd₂) / Zpos cd₁ * k₁)%Z.
    rewrite <- Zmult_assoc, <- Hpd₁.
    rewrite Zmult_assoc.
    f_equal.
    rewrite Zmult_comm.
    rewrite <- Z.divide_div_mul_exact.
     rewrite Zmult_comm.
     rewrite Z.div_mul; [ reflexivity | intros H; discriminate H ].

     pose proof (Pos2Z.is_pos cd₁) as H.
     intros HH; rewrite HH in H; apply Zlt_irrefl in H; assumption.

     unfold Plcm.
     rewrite Z2Pos.id; [ apply Z.divide_lcm_l | apply Zlcm_pos ].

    apply IHs; eapply series_forall_inv; eassumption.

   eapply TermAndFurther; [ reflexivity | idtac | idtac ].
    apply series_forall_inv in Hps₁.
    destruct Hps₁ as (Hpd₁, Hps₁).
    apply div_div_lcm; assumption.

    apply IHs; [ eapply series_forall_inv; eassumption | assumption ].

   eapply TermAndFurther; [ reflexivity | idtac | idtac ].
    apply series_forall_inv in Hps₂.
    destruct Hps₂ as (Hpd₂, Hps₂).
    unfold Plcm.
    rewrite Z.lcm_comm.
    apply div_div_lcm; assumption.

    apply IHs₂; eapply series_forall_inv; eassumption.

  constructor; reflexivity.

 simpl.
 induction s₂ as [t₂ s₂ IHs₂| ].
  eapply TermAndFurther; [ reflexivity | idtac | idtac ].
   apply series_forall_inv in Hps₂.
   destruct Hps₂ as (Hpd₂, Hps₂).
   unfold Plcm.
   rewrite Z.lcm_comm.
   apply div_div_lcm; assumption.

   apply series_forall_inv in Hps₂.
   destruct Hps₂ as (Hpd₂, Hps₂).
   eapply series_forall_map in Hps₂; [ eassumption | idtac ].
   unfold Plcm.
   rewrite Z.lcm_comm.
   apply div_div_lcm.

  constructor; reflexivity.
Qed.

Theorem ps_prop_add : ∀ α (add_coeff : α → α → α) ps₁ ps₂,
  series_forall
    (pow_den_div_com_den (Plcm (ps_comden ps₁) (ps_comden ps₂)))
    (ps_add_loop add_coeff (ps_terms ps₁) (ps_terms ps₂)).
Proof.
intros α add_coeff ps₁ ps₂.
apply series_forall_add; [ apply (ps_prop ps₁) | apply (ps_prop ps₂) ].
Qed.

Definition ps_add α (add_coeff : α → α → α) (ps₁ : puiseux_series α)
    (ps₂ : puiseux_series α) :=
  {| ps_terms := ps_add_loop add_coeff (ps_terms ps₁) (ps_terms ps₂);
     ps_comden := Plcm (ps_comden ps₁) (ps_comden ps₂);
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
                 fe_s₁ := s₁ tt; fe_s₂ := fe_s₂ fe |}
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
                 fe_s₁ := fe_s₁ fe; fe_s₂ := s₂ tt |}
              sl₂
       | End => sl₂
       end)
    fel sl.

Fixpoint sum_mul_coeff α add_coeff (mul_coeff : α → α → α) i ni₁ s₁ s₂ :=
  match ni₁ with
  | O => None
  | S ni =>
      match sum_mul_coeff add_coeff mul_coeff (S i) ni s₁ s₂ with
      | Some c =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (add_coeff (mul_coeff c₁ c₂) c)
              | None => Some (add_coeff c₁ c)
              end
          | None =>
              match series_nth ni s₂ with
              | Some c₂ => Some (add_coeff c₂ c)
              | None => Some c
              end
          end
      | None =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (mul_coeff c₁ c₂)
              | None => Some c₁
              end
          | None =>
              match series_nth ni s₂ with
              | Some c₂ => Some c₂
              | None => None
              end
          end
      end
  end.

Definition ps_mul α add_coeff mul_coeff s₁ s₂ :=
  let fix mul_loop n₁ :=
    match sum_mul_coeff add_coeff mul_coeff 0 n₁ s₁ s₂ with
    | Some c => Term c (λ tt, mul_loop (S n₁))
    | None => End _
    end
  in
  mul_loop 1.

(*
Fixpoint ps_mul_loop α add_coeff mul_coeff sum_fifo : series (term α) :=
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
      Term m (λ tt, ps_mul_loop α add_coeff mul_coeff sl₂)
  end.
*)

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

Definition fifo_div_comden α comden (cfel : (Q * list (fifo_elem α))) :=
  den_divides_comden comden (fst cfel).

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
  List.Forall (fifo_div_comden cd₁ cd₂) sf
  → t₁ = fe_t₁ fe
    → t₂ = fe_t₂ fe
      → List.Forall (fifo_div_comden cd₁ cd₂)
            (insert_sum (power t₁ + power t₂) fe sf).
Proof.
intros α fe t₁ t₂ cd₁ cd₂ sf H H₁ H₂.
subst t₁ t₂.
induction sf as [| (sum₁, fel₁)].
 constructor; [ idtac | constructor ].
 unfold fifo_div_comden; simpl.
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
  List.Forall (fifo_div_comden cd₁ cd₂) sf
  → List.Forall (fifo_div_comden cd₁ cd₂) (add_right mul_coeff sf fel)
    → t₁ = fe_t₁ fe
      → t₂ = fe_t₂ fe
        → List.Forall (fifo_div_comden cd₁ cd₂)
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
  List.Forall (fifo_div_comden cd₁ cd₂) sf
  → List.Forall (fifo_div_comden cd₁ cd₂) (add_right mul_coeff sf fel).
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
Lemma yyy : ∀ α mul_coeff t₁ t₂ cd sum fe fel
     (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) [(sum, [fe … fel]) … sf]
  → List.Forall (fifo_div_comden cd) [(sum, [fe … fel]) … sf]
    → t₁ = fe_t₁ fe
      → t₂ = fe_t₂ fe
        → List.Forall (fifo_div_comden cd)
            (add_right mul_coeff (insert_sum (power t₁ + power t₂) fe sf)
               fel).
Proof.
intros α mul_coeff t₁ t₂ cd sum fe fel sf Hs Hk.
induction fel as [| fe₁]; intros; simpl.
 induction sf as [| (sum₁, fel₁)].
  constructor; [ idtac | constructor ].
  unfold fifo_div_comden; simpl.
  apply list_Forall_inv in Hk.
  destruct Hk as (He, _).
  unfold fifo_div_comden in He.
  destruct He as (k₁, He).
  apply list_Forall_inv in Hs.
  destruct Hs as (Hf, _).
  unfold fifo_sum_prop in Hf; simpl in Hf.
  apply list_Forall_inv in Hf.
  destruct Hf as (Hf, _).
  simpl in He.
bbb.
*)

Lemma Zpos_ne_0 : ∀ p n, n = Zpos p → n ≠ 0%Z.
Proof.
intros p n Hn; subst n.
pose proof (Zgt_pos_0 p) as H.
intros HH; rewrite HH in H.
apply Zgt_irrefl in H; contradiction.
Qed.

Lemma pos_nat_ne_0 : ∀ p n, n = Pos.to_nat p → n ≠ 0%nat.
Proof.
intros p n Hn; subst n.
pose proof (Pos2Nat.is_succ p) as H.
destruct H as (n, H).
rewrite H; clear H; intros H; discriminate H.
Qed.

Lemma gcd_pos_ne_0_r : ∀ a b p, b = Pos.to_nat p → gcd a b ≠ 0%nat.
Proof.
intros a b p Hb H.
apply Nat.gcd_eq_0_r in H.
rewrite Hb in H.
pose proof (Pos2Nat.is_succ p) as HH.
destruct HH as (n, HH).
rewrite H in HH; discriminate HH.
Qed.

Lemma Qeq_den_div : ∀ a b c x y,
  a == b + c
  → (' Qden b | ' x * Qnum b)%Z
    → (' Qden c | ' y * Qnum c)%Z
      → (' Qden a | ' (x * y) * Qnum a)%Z.
Proof.
intros (an, ad) (bn, bd) (cn, cd) x y Ha Hb Hc.
remember (' x)%Z as t; simpl in Hb; subst t.
remember (' y)%Z as t; simpl in Hc; subst t.
remember (' (x * y))%Z as t; simpl; subst t.
unfold Z.divide in Hb, Hc |- *.
destruct Hb as (d, Hb).
destruct Hc as (e, He).
exists (' y * d + ' x * e)%Z.
rewrite Pos2Z.inj_mul.
unfold Qeq in Ha.
simpl in Ha.
rewrite Pos2Z.inj_mul in Ha.
rewrite Z.mul_add_distr_r in Ha.
rewrite Zmult_assoc in Ha.
rewrite Z.mul_add_distr_r.
apply Z.mul_reg_r with (p := (' bd * ' cd)%Z).
 simpl.
 eapply Zpos_ne_0; reflexivity.

 rewrite <- Zmult_assoc.
 rewrite Zmult_comm.
 do 2 rewrite Zmult_assoc.
 rewrite Ha.
 rewrite <- Zmult_assoc.
 rewrite Zmult_comm, Zmult_plus_distr_r, Z.mul_shuffle1.
 do 2 rewrite Zmult_assoc.
 rewrite Hb.
 rewrite Z.add_comm, Zmult_assoc, Z.mul_shuffle2, He.
 ring.
Qed.

(*
Lemma Qeq_den_divides : ∀ a b m n,
  a == b
  → (m * Z.abs_nat (Qnum a))%nat = (n * Pos.to_nat (Qden a))%nat
    → (Pos.to_nat (Qden b) | m * Z.abs_nat (Qnum b))%nat.
Proof.
intros (an, ad) (bn, bd) m n Hab H.
simpl in H |- *.
unfold Qeq in Hab; simpl in Hab.
destruct an as [| an| an].
 symmetry in Hab.
 apply Z.eq_mul_0_l in Hab.
  subst bn.
  exists 0%nat.
  rewrite mult_comm; reflexivity.

  pose proof (Zgt_pos_0 ad) as Hp.
  intros HH; rewrite HH in Hp.
  apply Zgt_irrefl in Hp; contradiction.

 destruct bn as [| bn| bn].
  exists 0%nat.
  rewrite mult_comm; reflexivity.

  simpl in Hab, H |- *.
  apply Z2Nat.inj_iff in Hab.
   simpl in Hab.
   do 2 rewrite Pos2Nat.inj_mul in Hab.
   unfold divide.
   exists n.
   apply Nat.mul_cancel_r with (p := Pos.to_nat ad).
    eapply pos_nat_ne_0; reflexivity.

    rewrite <- mult_assoc, <- Hab, mult_assoc, H.
    rewrite Nat.mul_shuffle0; reflexivity.

   apply Zle_0_pos.

   apply Zle_0_pos.

  discriminate Hab.

 destruct bn as [| bn| bn]; [ discriminate Hab | discriminate Hab | idtac ].
 simpl in Hab, H |- *.
 apply Pos2Z.inj_neg_iff in Hab.
 unfold divide.
 exists n.
 apply Nat.mul_cancel_r with (p := Pos.to_nat ad).
  eapply pos_nat_ne_0; reflexivity.

  rewrite <- mult_assoc, <- Pos2Nat.inj_mul.
  rewrite <- mult_assoc, <- Pos2Nat.inj_mul.
  rewrite <- Hab.
  rewrite Pos2Nat.inj_mul.
  rewrite Pos2Nat.inj_mul.
  rewrite mult_assoc, H.
  rewrite mult_assoc.
  rewrite Nat.mul_shuffle0; reflexivity.
Qed.
*)

Lemma fifo_div_comden_insert : ∀ α cd sum fe fel t₁ t₂
    (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) [(sum, [fe … fel]) … sf]
  → List.Forall (fifo_div_comden cd) [(sum, [fe … fel]) … sf]
    → t₁ = fe_t₁ fe
      → t₂ = fe_t₂ fe
(*
den_divides_comden cd₁ (power t₁)
den_divides_comden cd₂ (power t₂)
*)
        → List.Forall (fifo_div_comden cd)
            (insert_sum (power t₁ + power t₂) fe sf).
Proof.
intros α cd sum fe fel t₁ t₂ sf Hfs Hfe H₁ H₂.
Abort. (*
induction sf as [| (sum₁, fel₁)].
 constructor; [ idtac | constructor ].
 apply list_Forall_inv in Hfe.
 destruct Hfe as (Hfe, _).
 destruct Hfe as (k₁, Hfe); simpl in Hfe.
 apply list_Forall_inv in Hfs.
 destruct Hfs as (Hfs, _).
 unfold fifo_sum_prop in Hfs; simpl in Hfs.
 apply list_Forall_inv in Hfs.
 destruct Hfs as (Hfs, _).
 rewrite <- H₁, <- H₂ in Hfs.
 remember (power t₁ + power t₂) as pp.
 unfold fifo_div_comden, den_divides_comden; simpl.
 eapply Qeq_den_divides; eassumption.

 simpl.
 apply list_Forall_inv in Hfe.
 destruct Hfe as (Hfd₁, Hfe).
 apply list_Forall_inv in Hfe.
 destruct Hfe as (Hfd₂, Hfe).
 remember (power t₁ + power t₂ ?= sum₁) as c.
 symmetry in Heqc.
 destruct c.
  constructor; assumption.

  Focus 2.
  apply list_Forall_inv in Hfs.
  destruct Hfs as (Hfsp₁, Hfs).
  apply list_Forall_inv in Hfs.
  destruct Hfs as (Hfsp₂, Hfs).
  constructor; [ assumption | idtac ].
  apply IHsf; constructor; assumption.

  constructor; [ idtac | constructor; assumption ].
  unfold fifo_div_comden; simpl.
bbb.
*)

(**)
Lemma fifo_div_comden_sum_right : ∀ α mul_coeff cd t₁ t₂ sum fe fel
    (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) [(sum, [fe … fel]) … sf]
  → List.Forall (fifo_div_comden cd) [(sum, [fe … fel]) … sf]
    → t₁ = fe_t₁ fe
      → t₂ = fe_t₂ fe
(*
den_divides_comden cd₁ (power t₁)
den_divides_comden cd₂ (power t₂)
*)
        → List.Forall (fifo_div_comden cd)
            (add_right mul_coeff (insert_sum (power t₁ + power t₂) fe sf)
               fel).
Proof.
intros α mul_coeff cd t₁ t₂ sum fe fel sf Hsp Hfe H₁ H₂.
revert cd t₁ t₂ sum fe sf Hsp Hfe H₁ H₂.
induction fel as [| fe₁]; intros; simpl.
Abort. (*
 eapply fifo_div_comden_insert; eassumption.
bbb.
*)

Lemma zzz : ∀ α add_coeff mul_coeff cd₁ cd₂
    (sf : list (_ * list (fifo_elem α))),
  List.Forall (λ cfel, fifo_sum_prop cfel) sf
  → List.Forall
      (λ sum_fel,
         List.Forall (λ fe, den_divides_comden cd₁ (power (fe_t₁ fe)))
           (snd sum_fel))
      sf
    → List.Forall
        (λ sum_fel,
           List.Forall (λ fe, den_divides_comden cd₂ (power (fe_t₂ fe)))
             (snd sum_fel))
        sf
      → series_forall (pow_den_div_com_den (cd₁ * cd₂)%positive)
          (ps_mul_loop add_coeff mul_coeff sf).
Proof.
cofix IHs.
intros α add_coeff mul_coeff cd₁ cd₂ sf Hs Hd₁ Hd₂.
rewrite series_eta; simpl.
destruct sf as [| (sum, fel)]; [ constructor; reflexivity | idtac ].
destruct fel as [| fe]; [ constructor; reflexivity | idtac ].
eapply TermAndFurther; [ reflexivity | idtac | idtac ].
 unfold pow_den_div_com_den; simpl.
 apply List.Forall_inv in Hd₁.
 simpl in Hd₁.
 apply List.Forall_inv in Hd₂; simpl in Hd₂.
 apply List.Forall_inv in Hd₁.
 apply List.Forall_inv in Hd₂.
 apply List.Forall_inv in Hs.
 unfold fifo_sum_prop in Hs.
 simpl in Hs.
 apply List.Forall_inv in Hs.
 unfold den_divides_comden in Hd₁, Hd₂ |- *.
 eapply Qeq_den_div; eassumption.

 eapply IHs; try eassumption.

bbb.


  simpl.
  rewrite Pos2Nat.inj_mul.
  rewrite mult_plus_distr_r.
  rewrite Nat.mul_shuffle1.
  rewrite <- Hd₁.
  rewrite <- mult_assoc.
  rewrite <- mult_assoc.
  rewrite <- mult_assoc.
  rewrite <- mult_plus_distr_l.
  f_equal.
  rewrite mult_assoc.
  rewrite mult_assoc.
  rewrite plus_comm.
  rewrite Nat.mul_shuffle0.
  rewrite <- Hd₂.
  rewrite plus_comm.
  symmetry.
  rewrite <- mult_assoc, mult_comm.
  rewrite <- mult_assoc.
  rewrite <- mult_assoc.
  rewrite <- mult_plus_distr_l.
  f_equal.
  destruct (Qnum (power (fe_t₁ fe))) as [| pn₁| pn₁].
   rewrite mult_0_r; simpl.
   rewrite Zabs2Nat.inj_mul.
   reflexivity.

   simpl.
   destruct (Qnum (power (fe_t₂ fe))) as [| pn₂| pn₂].
    simpl.
    rewrite plus_0_r.
    rewrite mult_comm.
    rewrite Pos2Nat.inj_mul; reflexivity.

    simpl.
    rewrite Pos2Nat.inj_add.
    rewrite Pos2Nat.inj_mul.
    rewrite Pos2Nat.inj_mul.
    rewrite mult_comm.
    reflexivity.

    simpl.
  Focus 1.
bbb.

cofix IHs.
intros α add_coeff mul_coeff cd₁ cd₂ sf Hs Hd₁ Hd₂.
rewrite series_eta; simpl.
destruct sf as [| (sum, fel)]; [ constructor; reflexivity | idtac ].
destruct fel as [| fe]; [ constructor; reflexivity | idtac ].
eapply TermAndFurther; [ reflexivity | idtac | idtac ].
 unfold pow_den_div_com_den; simpl.
 apply List.Forall_inv in Hk.
 unfold fifo_div_comden in Hk; simpl in Hk.
 destruct Hk as (k₁, Hk).
 unfold den_divides_comden.
 exists k₁.
 rewrite <- Hk.
 reflexivity.

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
    apply fifo_div_comden_sum_right; try reflexivity.
    apply yyy with (power (fe_t₁ fe) + power tt₂).
     constructor.
      unfold fifo_sum_prop; simpl.
      constructor; [ reflexivity | idtac ].
     Focus 1.
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
bbb.

destruct Hp₁ as (k₁, Hp₁).
destruct Hp₂ as (k₂, Hp₂).
bbb.
eapply zzz; try eassumption.
 constructor; [ simpl | constructor ].
 constructor; [ reflexivity | constructor ].

 constructor; [ simpl | constructor ].
 remember (power t₁ + power t₂) as pp.
 unfold fifo_div_comden; simpl.
 subst cd₁ cd₂.
 remember (Z.abs_nat (Qnum (power t₁))) as x₁.
 remember (Pos.to_nat (Qden (power t₁))) as y₁.
 remember (Z.abs_nat (Qnum (power t₂))) as x₂.
 remember (Pos.to_nat (Qden (power t₂))) as y₂.
 subst pp; simpl.
 rewrite Pos2Nat.inj_mul.
 rewrite <- Heqy₁, <- Heqy₂.
 exists (k₁ * k₂)%nat.
 destruct (Z_zerop (Qnum (power t₁))) as [Hp₁| Hp₁].
  rewrite Hp₁ in Heqx₁ |- *; subst x₁; simpl.
  rewrite Nat.div_same; [ idtac | eapply pos_nat_ne_0; eassumption ].
  rewrite mult_1_r.
  destruct (Z_zerop (Qnum (power t₂))) as [Hp₂| Hp₂].
   rewrite Hp₂ in Heqx₂ |- *; subst x₂; simpl.
   rewrite Nat.div_same; [ idtac | eapply pos_nat_ne_0; eassumption ].
   rewrite mult_1_r.
   rewrite Nat.div_mul; [ reflexivity | idtac ].
   apply Nat.neq_mul_0.
   split; eapply pos_nat_ne_0; eassumption.

   rewrite Zabs2Nat.inj_mul; simpl.
   rewrite <- Heqx₂, <- Heqy₁.
   symmetry.
   rewrite mult_assoc.
   remember (k₁ * k₂)%nat as k.
   destruct k; simpl.
    rewrite Nat.div_0_l; [ reflexivity | idtac ].
    rewrite mult_comm, Nat.gcd_mul_mono_l.
    apply Nat.neq_mul_0.
    split; [ eapply pos_nat_ne_0 | eapply gcd_pos_ne_0_r ]; eassumption.

    symmetry.
    rewrite mult_comm, Nat.gcd_mul_mono_r.
    rewrite mult_assoc, <- mult_plus_distr_r.
    rewrite Nat.div_mul_cancel_r.
     rewrite <- Nat.divide_div_mul_exact.
      pose proof (gcd_divide_r x₂ y₂) as Hgd.
      destruct Hgd as (v, Hgd).
      remember (gcd x₂ y₂) as g.
      rewrite Hgd, mult_assoc, <- mult_plus_distr_r.
      destruct g; [ reflexivity | idtac ].
      rewrite Nat.div_mul; [ idtac | intros H; discriminate H ].
      rewrite Nat.div_mul; [ idtac | intros H; discriminate H ].
      rewrite Nat.div_mul; [ idtac | intros H; discriminate H ].
      reflexivity.

      eapply gcd_pos_ne_0_r; eassumption.

      apply gcd_divide_r.

     eapply gcd_pos_ne_0_r; eassumption.

     eapply pos_nat_ne_0; eassumption.

  destruct (Z_zerop (Qnum (power t₂))) as [Hp₂| Hp₂].
   rewrite Hp₂ in Heqx₂ |- *; subst x₂; simpl.
   rewrite Zplus_0_r.
   rewrite Zabs2Nat.inj_mul; simpl.
   rewrite <- Heqx₁, <- Heqy₂.
   symmetry.
   rewrite Nat.mul_shuffle0, mult_assoc.
   remember (k₁ * k₂)%nat as k.
   destruct k; simpl.
    rewrite Nat.div_0_l; [ reflexivity | idtac ].
    rewrite Nat.gcd_mul_mono_r.
    apply Nat.neq_mul_0.
    split; [ eapply gcd_pos_ne_0_r | eapply pos_nat_ne_0 ]; eassumption.

    rewrite Nat.div_same; [ idtac | eapply pos_nat_ne_0; eassumption ].
    rewrite mult_1_r.
    rewrite Nat.gcd_mul_mono_r.
    rewrite mult_assoc, <- mult_plus_distr_r.
    rewrite Nat.div_mul_cancel_r.
     rewrite <- Nat.divide_div_mul_exact.
      reflexivity.

      eapply gcd_pos_ne_0_r; eassumption.

      apply gcd_divide_r.

     eapply gcd_pos_ne_0_r; eassumption.

     eapply pos_nat_ne_0; eassumption.

   rewrite Zabs2Nat.inj_add.
    do 2 rewrite Zabs2Nat.inj_mul; simpl.
    rewrite <- Heqx₁, <- Heqy₁, <- Heqx₂, <- Heqy₂.
    symmetry.
    rewrite Nat.mul_shuffle0, mult_assoc.
    remember (k₁ * k₂)%nat as k.
    destruct k; simpl.
     rewrite Nat.div_0_l; [ reflexivity | idtac ].
     subst y₁ y₂.
     rewrite <- Pos2Nat.inj_mul.
     eapply gcd_pos_ne_0_r; reflexivity.
bbb.
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
