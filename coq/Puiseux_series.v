(* $Id: Puiseux_series.v,v 1.6 2013-06-24 12:57:27 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

Require Import Field.
Require Import Series.

Set Implicit Arguments.

Record term α := { coeff : α; power : Q }.

Definition den_divides_comden comden p :=
  (' Qden p | (Zpos comden * Qnum p))%Z.

Definition pow_den_div_com_den α comden (t : term α) :=
  den_divides_comden comden (power t).

Record puiseux_series α :=
  { ps_terms : series (term α);
    ps_comden : positive;
    ps_prop : series_forall (pow_den_div_com_den ps_comden) ps_terms }.

Record math_puiseux_series α :=
  { ms_terms : series α;
    ms_valnum : option Z;
    ms_comden : positive }.

(* [series_head] skip the possible terms with null coefficients and return
   the sub-series of the initial series whose coefficient of the first term
   is not null. E.g.: applied to
       0+0x³+5x⁵+0x⁷+3x⁸+...
   would return
       5x⁵+0x⁷+3x⁸+... *)
Definition series_head : ∀ α, (α → bool) → series (term α) → series (term α).
Proof. Admitted.

Definition valuation α fld (ps : puiseux_series α) :=
  match series_head (is_zero fld) (ps_terms ps) with
  | Term mx _ => Some (power mx)
  | End => None
  end.

Definition valuation_coeff α fld (ps : puiseux_series α) :=
  match series_head (is_zero fld) (ps_terms ps) with
  | Term mx _ => coeff mx
  | End => zero fld
  end.

(* puiseux_series ↔ math_puiseux_series *)

CoFixpoint term_of_ms α cd p (s : series α) :=
  match s with
  | Term c ns =>
      Term {| coeff := c; power := Qmake p cd |} (term_of_ms cd (Z.succ p) ns)
  | End =>
      End _
  end.

Definition ps_terms_of_ms α (ms : math_puiseux_series α) : series (term α) :=
  match ms_valnum ms with
  | Some v => term_of_ms (ms_comden ms) v (ms_terms ms)
  | None => End _
  end.

Lemma term_of_ms_power : ∀ α cd (s : series α) p t ns,
  term_of_ms cd p s = Term t ns
  → power t = p # cd.
Proof.
intros α cd s v t ns Ht.
symmetry in Ht.
unfold term_of_ms in Ht.
rewrite series_eta in Ht.
destruct s; [ idtac | discriminate Ht ].
injection Ht; clear Ht; intros _ H.
subst t; reflexivity.
Qed.

Lemma term_of_ms_comden : ∀ α cd (s : series α) p t ns,
  term_of_ms cd p s = Term t ns
  → den_divides_comden cd (power t).
Proof.
intros α cd s v t ns Ht.
apply term_of_ms_power in Ht.
rewrite Ht.
exists v.
remember Z.mul as f; simpl; subst f.
apply Z.mul_comm.
Qed.

Lemma term_of_ms_succ : ∀ α cd p (s : series α) s₁ t t₁,
  term_of_ms cd p (Term t s) = Term t₁ s₁
  → s₁ = term_of_ms cd (Z.succ p) s.
Proof.
intros α cd p s s₁ t t₁ Ht.
symmetry in Ht.
rewrite series_eta in Ht.
injection Ht; clear Ht; intros Ht H.
assumption.
Qed.

Theorem ps_prop_of_ms : ∀ α (ms : math_puiseux_series α),
  series_forall (pow_den_div_com_den (ms_comden ms)) (ps_terms_of_ms ms).
Proof.
intros α ms.
unfold ps_terms_of_ms.
remember (ms_valnum ms) as p.
destruct p as [p| ]; [ idtac | constructor; reflexivity ].
remember (ms_comden ms) as cd; clear Heqcd.
remember (ms_terms ms) as s; clear Heqs.
clear Heqp.
remember (term_of_ms cd p s) as t.
clear ms.
revert p cd s t Heqt.
cofix IHs; intros.
destruct t; [ idtac | constructor; reflexivity ].
eapply TermAndFurther; [ reflexivity | idtac | idtac ].
 symmetry in Heqt.
 eapply term_of_ms_comden; eassumption.

 destruct s.
  symmetry in Heqt.
  apply term_of_ms_succ in Heqt.
  eapply IHs; eassumption.

  rewrite series_eta in Heqt.
  discriminate Heqt.
Qed.

Definition ps_of_ms α (ms : math_puiseux_series α) :=
  {| ps_terms := ps_terms_of_ms ms;
     ps_comden := ms_comden ms;
     ps_prop := ps_prop_of_ms ms |}.

CoFixpoint complete α (zero : α) (ps : puiseux_series α) p s :=
  match s with
  | Term t ns =>
      let p₁ := Qplus p (Qmake 1 (ps_comden ps)) in
      if Qlt_le_dec p₁ (power t) then
        Term {| coeff := zero; power := p₁ |} (complete zero ps p₁ s)
      else
        Term t ns
  | End =>
      End _
  end.

Definition ms_terms_of_ps α zero is_zero (ps : puiseux_series α) :=
  let cofix loop s :=
    match s with
    | Term t ns => Term (coeff t) (loop (complete zero ps (power t) ns))
    | End => End _
    end
  in
  loop (series_head is_zero (ps_terms ps)).

Definition ms_of_ps α fld (ps : puiseux_series α) :=
  {| ms_terms :=
       ms_terms_of_ps (zero fld) (is_zero fld) ps;
     ms_valnum :=
       match valuation fld ps with
       | Some v =>
           Some (Qnum (Qred (Qmult v (inject_Z (Zpos (ps_comden ps))))))
       | None =>
           None
       end;
     ms_comden :=
       ps_comden ps |}.

(* ps_add *)

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

Lemma Pos_divide_lcm_l : ∀ a b, (a | Plcm a b)%positive.
Proof.
intros a b.
unfold Plcm.
pose proof (Zlcm_pos a b)%Z as H.
unfold Z.lcm.
rewrite Z.abs_mul.
rewrite Z2Pos.inj_mul.
 remember (' b / Z.gcd (' a) (' b))%Z as x.
 simpl.
 rewrite Pmult_comm.
 exists (Z.to_pos (Z.abs x)); reflexivity.

 simpl.
 apply Pos2Z.is_pos.

 unfold Z.lcm in H.
 rewrite Z.abs_mul in H.
 remember (' b / Z.gcd (' a) (' b))%Z as x.
 apply Z.lt_0_mul in H.
 destruct H as [H| H].
  destruct H; assumption.

  destruct H as (_, H).
  apply Zlt_not_le in H.
  exfalso; apply H.
  apply Z.abs_nonneg.
Qed.

Lemma Pos_divide_lcm_r : ∀ a b, (b | Plcm a b)%positive.
Proof.
intros a b.
unfold Plcm.
rewrite Z.lcm_comm.
apply Pos_divide_lcm_l.
Qed.

Lemma series_forall_div_mul : ∀ α (s : series (term α)) cd x,
  series_forall (pow_den_div_com_den cd) s
  → series_forall (pow_den_div_com_den (cd * x)) s.
Proof.
cofix IHs.
intros α s cd x H.
destruct s as [t s| ]; [ idtac | constructor; reflexivity ].
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

Lemma series_forall_add : ∀ α (add_coeff : α → α → α) s₁ s₂ cd₁ cd₂,
  series_forall (pow_den_div_com_den cd₁) s₁
  → series_forall (pow_den_div_com_den cd₂) s₂
    → series_forall (pow_den_div_com_den (Plcm cd₁ cd₂))
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

    apply IHs; [ assumption | idtac ].
    apply series_forall_inv in Hps₂.
    destruct Hps₂; assumption.

  eapply TermAndFurther; [ reflexivity | idtac | idtac ].
   apply series_forall_inv in Hps₁.
   destruct Hps₁ as (Hpd₁, Hsf₁).
   apply div_div_lcm; assumption.

   pose proof (Pos_divide_lcm_l cd₁ cd₂) as H.
   destruct H as (z, H).
   rewrite H, Pos.mul_comm.
   apply series_forall_div_mul.
   apply series_forall_inv in Hps₁.
   destruct Hps₁; assumption.

 destruct s₂.
  rename t into t₂.
  eapply TermAndFurther; [ reflexivity | idtac | idtac ].
   apply series_forall_inv in Hps₂.
   destruct Hps₂ as (Hpd₂, Hsf₂).
   unfold pow_den_div_com_den in Hpd₂ |- *.
   unfold Plcm.
   rewrite Z.lcm_comm.
   apply div_div_lcm; assumption.

   pose proof (Pos_divide_lcm_r cd₁ cd₂) as H.
   destruct H as (z, H).
   rewrite H, Pos.mul_comm.
   apply series_forall_div_mul.
   apply series_forall_inv in Hps₂.
   destruct Hps₂; assumption.

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

Definition ps_add α fld (ps₁ ps₂ : puiseux_series α) :=
  {| ps_terms := ps_add_loop (add fld) (ps_terms ps₁) (ps_terms ps₂);
     ps_comden := Plcm (ps_comden ps₁) (ps_comden ps₂);
     ps_prop := ps_prop_add (add fld) ps₁ ps₂ |}.

(* ps_mul *)

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
              | None => Some c
              end
          | None => Some c
          end
      | None =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (mul_coeff c₁ c₂)
              | None => None
              end
          | None => None
          end
      end
  end.

Definition ms_mul_term α add_coeff mul_coeff (s₁ s₂ : series α) :=
  let cofix mul_loop n₁ :=
    match sum_mul_coeff add_coeff mul_coeff 0 n₁ s₁ s₂ with
    | Some c => Term c (mul_loop (S n₁))
    | None => End _
    end
  in
  mul_loop 1%nat.

Definition ms_mul α add_coeff mul_coeff (ms₁ ms₂ : math_puiseux_series α) :=
  {| ms_terms :=
       ms_mul_term add_coeff mul_coeff (ms_terms ms₁) (ms_terms ms₂);
     ms_valnum :=
       match ms_valnum ms₁ with
       | Some v₁ =>
           match ms_valnum ms₂ with
           | Some v₂ =>
               Some
                 (Z.add (Z.mul v₁ (Zpos (ms_comden ms₂)))
                    (Z.mul v₂ (Zpos (ms_comden ms₁))))
           | None =>
               None
           end
       | None => None
       end;
     ms_comden :=
       Pos.mul (ms_comden ms₁) (ms_comden ms₂) |}.

Definition ps_mul α fld (ps₁ ps₂ : puiseux_series α) :=
  ps_of_ms (ms_mul (add fld) (mul fld) (ms_of_ps fld ps₁) (ms_of_ps fld ps₂)).
