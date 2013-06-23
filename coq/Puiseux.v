(* $Id: Puiseux.v,v 1.773 2013-06-23 18:11:49 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Sorted.
Require Import NPeano.

Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Field.
Require Import Misc.
Require Import Puiseux_base.
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

Definition ps_add α (add_coeff : α → α → α) (ps₁ : puiseux_series α)
    (ps₂ : puiseux_series α) :=
  {| ps_terms := ps_add_loop add_coeff (ps_terms ps₁) (ps_terms ps₂);
     ps_comden := Plcm (ps_comden ps₁) (ps_comden ps₂);
     ps_prop := ps_prop_add add_coeff ps₁ ps₂ |}.

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

Definition ms_mul_term α add_coeff mul_coeff (s₁ s₂ : series α) :=
  let cofix mul_loop n₁ :=
    match sum_mul_coeff add_coeff mul_coeff 0 n₁ s₁ s₂ with
    | Some c => Term c (mul_loop (S n₁))
    | None => End _
    end
  in
  mul_loop 1%nat.

Record math_puiseux_series α :=
  { ms_terms : series α;
    ms_valnum : option Z;
    ms_comden : positive }.

Definition ms_mul α add_coeff mul_coeff (ms₁ ms₂ : math_puiseux_series α) :=
  {| ms_terms :=
       ms_mul_term add_coeff mul_coeff (ms_terms ms₁) (ms_terms ms₂);
     ms_valnum :=
       match ms_valnum ms₁ with
       | Some v₁ =>
           match ms_valnum ms₂ with
           | Some v₂ => Some (Z.add v₁ v₂)
           | None => None
           end
       | None => None
       end;
     ms_comden :=
       Pos.mul (ms_comden ms₁) (ms_comden ms₂) |}.

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

Definition ps_mul α fld (ps₁ ps₂ : puiseux_series α) :=
  ps_of_ms (ms_mul (add fld) (mul fld) (ms_of_ps fld ps₁) (ms_of_ps fld ps₂)).

(* *)

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
       (ps_of_ms {| ms_terms := End α; ms_valnum := None; ms_comden := 1 |})
       (ps_add (add fld))
       (ps_mul fld))
    pol.

Definition mul_x_power_minus α p (ps : puiseux_series α) :=
  let t :=
    series_map
      (λ m, {| coeff := coeff m; power := Qred (Qminus (power m) p) |})
      (ps_terms ps)
  in
  {| ps_terms := t; ps_comden := ps_comden ps; ps_prop := bbb |}.

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
