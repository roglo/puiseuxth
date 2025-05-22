(* InK1m.v *)

From Stdlib Require Import Utf8 QArith ZArith.

Require Import Misc.
Require Import Field2.
Require Import Fpolynomial.
Require Import Newton.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_mul.
Require Import Ps_div.
Require Import Ps_add_compat.
Require Import PSpolynomial.
Require Import Puiseux_base.
Require Import AlgCloCharPol.
Require Import PosOrder.
Require Import CharactPolyn.
Require Import ConvexHull.
Require Import PolyConvexHull.
Require Import F1Eq.
Require Import QbarM.

Set Implicit Arguments.

Global Instance in_K_1_m_morph α (R : ring α) (K : field R) :
  Proper (eq_ps ==> eq ==> iff) (@in_K_1_m _ R K).
Proof.
intros a b Hab n c Hc.
subst c.
split; intros H. {
  inversion_clear H.
  destruct H0 as (ps₁, H).
  constructor.
  exists ps₁.
  destruct H as (H, Hpo).
  split; [ idtac | assumption ].
  transitivity a; assumption.
} {
  inversion_clear H.
  destruct H0 as (ps₁, H).
  constructor.
  exists ps₁.
  destruct H as (H, Hpo).
  split; [ idtac | assumption ].
  symmetry in Hab.
  transitivity b; assumption.
}
Qed.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Theorem in_K_1_m_add_compat : ∀ m a b,
  in_K_1_m a m
  → in_K_1_m b m
  → in_K_1_m (a + b) m.
Proof.
intros m a b Ha Hb.
inversion_clear Ha.
rename H into Ha.
inversion_clear Hb.
rename H into Hb.
destruct Ha as (psa, (Ha, Hpa)).
destruct Hb as (psb, (Hb, Hpb)).
constructor.
remember Ha as Hab; clear HeqHab.
eapply ps_add_compat_r with (ps₃ := psb) in Hab.
rewrite Hb in Hab at 2.
unfold ps_add in Hab at 1.
unfold cm in Hab.
rewrite Hpa, Hpb in Hab.
unfold ps_ordnum_add in Hab.
unfold cm_factor in Hab.
rewrite Hpa, Hpb in Hab.
rewrite Z.mul_min_distr_nonneg_r in Hab; auto with Arith.
unfold ps_terms_add in Hab.
unfold cm_factor in Hab.
rewrite Hpa, Hpb in Hab.
rewrite Z.mul_min_distr_nonneg_r in Hab; auto with Arith.
rewrite Z.mul_min_distr_nonneg_r in Hab; auto with Arith.
rewrite <- Z.mul_sub_distr_r in Hab.
rewrite <- Z.mul_sub_distr_r in Hab.
remember (ps_ordnum psa) as oa.
remember (ps_ordnum psb) as ob.
remember (ps_terms psa) as sa.
remember (ps_terms psb) as sb.
remember (oa - Z.min oa ob)%Z as omab.
remember (ob - Z.min ob oa)%Z as omba.
exists
 (mkps
    (adjust_series (Z.to_nat omab) 1 sa + adjust_series (Z.to_nat omba) 1 sb)
    (Z.min oa ob) m).
split; auto with Arith.
rewrite <- Hab.
rewrite ps_adjust_eq with (n := O) (k := m).
unfold adjust_ps; simpl.
rewrite Z.sub_0_r.
rewrite series_shift_0.
apply mkps_morphism; auto with Arith.
unfold adjust_series; simpl.
rewrite Z2Nat.inj_mul; simpl; auto with Arith.
 rewrite Z2Nat.inj_mul; simpl; auto with Arith.
  rewrite <- stretch_shift_series_distr.
  rewrite <- stretch_shift_series_distr.
  rewrite <- series_stretch_add_distr.
  do 2 rewrite series_stretch_1.
  reflexivity.

  subst omba.
  rewrite <- Z.sub_max_distr_l, Z.sub_diag.
  apply Z.le_max_l.

 subst omab.
 rewrite <- Z.sub_max_distr_l, Z.sub_diag.
 apply Z.le_max_l.
Qed.

Theorem in_K_1_m_mul_compat : ∀ m a b,
  in_K_1_m a m
  → in_K_1_m b m
  → in_K_1_m (a * b) m.
Proof.
intros m a b Ha Hb.
inversion_clear Ha.
rename H into Ha.
inversion_clear Hb.
rename H into Hb.
destruct Ha as (psa, (Ha, Hpa)).
destruct Hb as (psb, (Hb, Hpb)).
constructor.
remember Ha as Hab; clear HeqHab.
eapply ps_mul_compat_r with (ps₃ := psb) in Hab.
rewrite Hb in Hab at 2.
unfold ps_mul in Hab at 1.
unfold cm, cm_factor in Hab.
rewrite Hpa, Hpb in Hab.
rewrite <- Z.mul_add_distr_r in Hab.
rewrite <- series_stretch_mul in Hab.
exists (mkps (ps_terms psa * ps_terms psb) (ps_ordnum psa + ps_ordnum psb) m).
split; auto with Arith.
rewrite <- Hab.
rewrite ps_adjust_eq with (n := O) (k := m).
unfold adjust_ps; simpl.
rewrite Z.sub_0_r.
rewrite series_shift_0.
reflexivity.
Qed.

Theorem ps_zero_in_K_1_m : ∀ m, in_K_1_m 0 m.
Proof.
intros m.
constructor.
exists (mkps 0 0 m).
split; [ idtac | reflexivity ].
symmetry.
rewrite ps_adjust_eq with (n := O) (k := m).
unfold adjust_ps; simpl.
rewrite series_shift_0; simpl.
rewrite series_stretch_series_0.
reflexivity.
Qed.

Theorem ps_lap_forall_forall : ∀ la (P : puiseux_series α → Prop),
  (∀ a b, (a = b)%ps → P a → P b)
  → ps_lap_forall P la ↔ (∀ a, ps_lap_in a la → P a).
Proof.
intros la P Hmorph.
split; [ intros Hfa a Hin | intros Hfa ].
 revert a Hin.
 induction la as [| b]; intros; [ contradiction | idtac ].
 simpl in Hin.
 destruct Hin as [(Hbla, Hba)| Hin].
  inversion_clear Hfa; [ contradiction | idtac ].
  eapply Hmorph; eassumption.

  inversion_clear Hfa.
   inversion_clear H.
   rewrite H1 in Hin; contradiction.

   apply IHla; assumption.

 induction la as [| b]; [ constructor; reflexivity | idtac ].
 destruct (ps_lap_nilp _ [b … la]) as [Hba| Hba].
  constructor 1; assumption.

  constructor 2; [ assumption | idtac | idtac ].
   apply Hfa; left.
   split; [ assumption | reflexivity ].

   apply IHla; intros a Ha.
   apply Hfa; right; assumption.
Qed.

Theorem hd_in_K_1_m : ∀ a la m,
  ps_lap_forall (λ b, in_K_1_m b m) [a … la]
  → in_K_1_m a m.
Proof.
intros a la m Hla.
destruct (ps_zerop K a) as [Ha| Ha].
 rewrite Ha; apply ps_zero_in_K_1_m.

 eapply ps_lap_forall_forall in Hla; eauto with Arith.
  intros b c Hbc Hb.
  rewrite <- Hbc; assumption.

  left.
  split; [ idtac | reflexivity ].
  intros H1; apply Ha; clear Ha.
  apply lap_eq_cons_nil_inv in H1.
  destruct H1; assumption.
Qed.

Theorem in_K_1_m_lap_add_compat : ∀ m la lb c,
  (∀ a, ps_lap_in a la → in_K_1_m a m)
  → (∀ b, ps_lap_in b lb → in_K_1_m b m)
  → ps_lap_in c (la + lb)
  → in_K_1_m c m.
Proof.
intros m la lb c Hla Hlb Hc.
rewrite <- fold_ps_lap_add in Hc.
revert lb Hlb Hc.
induction la as [| a]; intros.
 simpl in Hc.
 apply Hlb; assumption.

 destruct lb as [| b].
  simpl in Hc.
  destruct Hc as [(Ha, Hac)| Hc].
   rewrite <- Hac.
   apply Hla; left.
   split; [ assumption | reflexivity ].

   apply Hla; right; assumption.

  simpl in Hc.
  destruct Hc as [(Hab, Hac)| Hc].
   rewrite <- Hac.
   apply in_K_1_m_add_compat.
    eapply hd_in_K_1_m.
    apply ps_lap_forall_forall; eauto .
    intros d e Hde Hd.
    rewrite <- Hde; assumption.

    eapply hd_in_K_1_m.
    apply ps_lap_forall_forall; eauto .
    intros d e Hde Hd.
    rewrite <- Hde; assumption.

   apply IHla with (lb := lb).
    intros d Hd.
    apply Hla; right; assumption.

    intros d Hd.
    apply Hlb; right; assumption.

    assumption.
Qed.

Theorem in_K_1_m_lap_mul_compat : ∀ m la lb c,
  (∀ a, ps_lap_in a la → in_K_1_m a m)
  → (∀ b, ps_lap_in b lb → in_K_1_m b m)
  → ps_lap_in c (la * lb)
  → in_K_1_m c m.
Proof.
intros m la lb c Hla Hlb Hc.
rewrite <- fold_ps_lap_mul in Hc.
revert lb c Hlb Hc.
induction la as [| a]; intros.
 rewrite lap_mul_nil_l in Hc.
 contradiction.

 destruct lb as [| b].
  rewrite lap_mul_nil_r in Hc.
  contradiction.

  rewrite lap_mul_cons in Hc.
  simpl in Hc.
  destruct Hc as [(Hab, Hc)| Hc].
   rewrite <- Hc.
   apply in_K_1_m_mul_compat.
    eapply hd_in_K_1_m.
    apply ps_lap_forall_forall; eauto .
    intros d e Hde Hd.
    rewrite <- Hde; assumption.

    eapply hd_in_K_1_m.
    apply ps_lap_forall_forall; eauto .
    intros d e Hde Hd.
    rewrite <- Hde; assumption.

   apply in_K_1_m_lap_add_compat with (m := m) in Hc; auto with Arith.
    intros d Hd.
    apply in_K_1_m_lap_add_compat with (m := m) in Hd; auto with Arith.
     intros e He.
     apply IHla with (lb := [b]); auto with Arith.
      intros f Hf.
      apply Hla; right; assumption.

      intros f Hf.
      simpl in Hf.
      destruct Hf as [(Hb, Hbf)| ]; [ idtac | contradiction ].
      rewrite <- Hbf.
      apply Hlb; left.
      split; [ idtac | reflexivity ].
      intros H; apply Hb.
      apply lap_eq_cons_nil_inv in H.
      destruct H as (H, _); rewrite H.
      apply lap_eq_0.

     intros f Hf.
     clear Hc Hd.
     induction lb as [| b']; [ contradiction | idtac ].
     rewrite lap_mul_cons in Hf.
     simpl in Hf.
     destruct Hf as [(Hab, Habf)| Hf].
      rewrite <- Habf.
      apply in_K_1_m_mul_compat.
       eapply hd_in_K_1_m.
       apply ps_lap_forall_forall; eauto .
       intros g h Hgh Hg.
       rewrite <- Hgh; assumption.

       destruct (ps_zerop K b') as [Hb| Hb].
        rewrite Hb; apply ps_zero_in_K_1_m.

        apply Hlb; right; left.
        split; [ idtac | reflexivity ].
        intros H; apply Hb; clear Hb.
        apply lap_eq_cons_nil_inv in H.
        destruct H; assumption.

      rewrite lap_mul_nil_l in Hf.
      rewrite lap_eq_0, lap_add_nil_r in Hf.
      apply IHlb; auto with Arith.
      intros e He.
      apply Hlb.
      simpl in He; simpl.
      destruct He as [(Hbb, He)| He].
       left.
       split; [ idtac | assumption ].
       intros H; apply Hbb.
       apply lap_eq_cons_nil_inv in H.
       destruct H as (Hb, H).
       rewrite Hb.
       apply lap_eq_cons_nil_inv in H.
       destruct H as (_, H); rewrite H.
       apply lap_eq_0.

       right; right; assumption.

    intros d Hd.
    simpl in Hd.
    destruct Hd as [(Hab, Hd)| Hd].
     rewrite <- Hd; apply ps_zero_in_K_1_m.

     apply IHla with (lb := lb); auto with Arith.
      intros e He.
      destruct (ps_zerop K e) as [Hf| Hf].
       rewrite Hf; apply ps_zero_in_K_1_m.

       apply Hla; right; assumption.

      intros e He.
      destruct (ps_zerop K e) as [Hf| Hf].
       rewrite Hf; apply ps_zero_in_K_1_m.

       apply Hlb; right; assumption.
Qed.

Theorem in_K_1_m_lap_comp_compat : ∀ m la lb c,
  (∀ a, ps_lap_in a la → in_K_1_m a m)
  → (∀ b, ps_lap_in b lb → in_K_1_m b m)
  → ps_lap_in c (la ∘ lb)
  → in_K_1_m c m.
Proof.
intros m la lb c Hla Hlb Hc.
rewrite <- fold_ps_lap_comp in Hc.
revert lb c Hlb Hc.
induction la as [| a]; intros; [ contradiction | idtac ].
destruct lb as [| b].
 simpl in Hc.
 rewrite lap_mul_nil_r, lap_add_nil_l in Hc; simpl in Hc.
 destruct Hc as [(Ha, Hac)| ]; [ idtac | contradiction ].
 apply Hla; left.
 split; [ idtac | assumption ].
 intros H; apply Ha.
 inversion_clear H.
 rewrite H0.
 apply lap_eq_0.

 simpl in Hc.
 eapply in_K_1_m_lap_add_compat; [ idtac | idtac | eauto  ].
  intros d Hd.
  eapply in_K_1_m_lap_mul_compat; [ idtac | idtac | eauto  ].
   intros e He.
   apply IHla with (lb := [b … lb]).
    intros f Hf.
    apply Hla; right; assumption.

    intros f Hf.
    simpl in Hf.
    destruct Hf as [Hf| Hf].
     apply Hlb; left; assumption.

     apply Hlb; right; assumption.

    assumption.

   intros e He.
   simpl in He.
   destruct He as [He| He].
    apply Hlb; left; assumption.

    apply Hlb; right; assumption.

  intros d Hd.
  simpl in Hd.
  destruct Hd as [(Ha, Had)| ]; [ idtac | contradiction ].
  apply Hla; left.
  split; [ idtac | assumption ].
  intros H; apply Ha.
  inversion_clear H.
  rewrite H0.
  apply lap_eq_0.
Qed.

Theorem minus_beta_in_K_1_mq : ∀ f L m a c q,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q = q_of_m m (γ L)
  → a = ps_monom c (- β L)
  → in_K_1_m a (m * q).
Proof.
intros f L m a c q HL Hm Hq Ha.
constructor; subst a.
remember (p_of_m m (γ L)) as p eqn:Hp .
pose proof (any_is_p_mq (γ L) m Hp Hq) as Hgp.
destruct Hgp as (Hgp, Hg).
remember (ini_pt L) as j eqn:Hini.
destruct j as (j, αj).
generalize Hini; intros Him.
eapply pol_ord_of_ini_pt in Him; eauto .
symmetry in Hini.
remember HL as Hbm; clear HeqHbm.
apply points_in_any_newton_segment with (h := j) (αh := αj) in Hbm. {
  rewrite Him, Hgp in Hbm.
  remember (mh_of_m m αj (ps_poly_nth j f)) as mj.
  remember (mj * Zpos q + Z.of_nat j * p # m * q) as v.
  exists (ps_monom c (- v)); subst v; simpl.
  split; [ idtac | reflexivity ].
  rewrite Hbm.
  unfold ps_monom; simpl.
  rewrite ps_adjust_eq with (n := O) (k := m).
  unfold adjust_ps; simpl.
  rewrite Z.sub_0_r.
  rewrite fold_series_const.
  rewrite series_stretch_const, series_shift_0.
  apply mkps_morphism; try reflexivity. {
    rewrite Z.mul_opp_l; f_equal.
    rewrite Z.mul_add_distr_r; f_equal.
    rewrite <- Z.mul_assoc; f_equal.
    apply Z.mul_comm.
  }
  apply Pos.mul_comm.
}
left; eassumption.
Qed.

Theorem gamma_in_K_1_mq : ∀ L m a c q,
  q = q_of_m m (γ L)
  → (a = ps_monom c (γ L))%ps
  → in_K_1_m a (m * q).
Proof.
intros L m a c q Hq Ha.
constructor.
remember (p_of_m m (γ L)) as p eqn:Hp .
pose proof (any_is_p_mq (γ L) m Hp Hq) as Hgp.
destruct Hgp as (Hgp, Hg).
exists (ps_monom c (p # m * q)); simpl.
split; [ idtac | reflexivity ].
rewrite Ha, Hgp.
reflexivity.
Qed.

Theorem in_K_1_m_lap_mul_r_compat : ∀ a m n,
  in_K_1_m a m
  → in_K_1_m a (m * n).
Proof.
intros a m n Ha.
constructor.
inversion_clear Ha.
destruct H as (ps, (Hps, Hm)).
exists (adjust_ps 0 n ps).
split; [ idtac | simpl; rewrite Hm; reflexivity ].
rewrite ps_adjust_eq with (n := O) (k := n) in Hps.
assumption.
Qed.

Theorem next_pol_in_K_1_mq : ∀ f f₁ L m c q,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → c = ac_root (Φq f L)
  → q = q_of_m m (γ L)
  → f₁ = next_pol f (β L) (γ L) c
  → pol_in_K_1_m f₁ (m * q).
Proof.
intros f f₁ L m c q HL Hm Hc Hq Hf₁.
subst f₁.
unfold next_pol, next_lap; simpl.
apply ps_lap_forall_forall.
 intros a b Hab Hamq.
 rewrite <- Hab; assumption.

 intros b Hin.
 eapply in_K_1_m_lap_mul_compat; eauto .
  intros a Ha.
  destruct Ha as [Ha| ]; [ idtac | contradiction ].
  destruct Ha as (_, Ha).
  rewrite <- Ha.
  eapply minus_beta_in_K_1_mq; eauto .

  intros ps Hps.
  eapply in_K_1_m_lap_comp_compat; eauto .
   intros a Ha.
   apply in_K_1_m_lap_mul_r_compat.
   revert a Ha.
   apply ps_lap_forall_forall.
    intros a d Hab Hamq.
    rewrite <- Hab; assumption.

    assumption.

   intros a Ha; simpl in Ha.
   destruct Ha as [Ha| [Ha| ]]; [ idtac | idtac | contradiction ].
    destruct Ha as (Hla, Ha).
    symmetry in Ha.
    eapply gamma_in_K_1_mq; eassumption.

    destruct Ha as (Hla, Ha).
    symmetry in Ha.
    eapply gamma_in_K_1_mq; eassumption.
Qed.

End theorems.
