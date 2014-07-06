(* InK1m.v *)

Require Import Utf8 QArith.

Require Import Misc.
Require Import Field.
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
Require Import PolyConvexHull.
Require Import F1Eq.

Set Implicit Arguments.

(* express that some puiseux series ∈ K(1/m)* *)
Inductive in_K_1_m {α} {R : ring α} ps m :=
  InK1m : (∃ ps₁, (ps₁ = ps)%ps ∧ ps_polord ps₁ = m) → in_K_1_m ps m.

Arguments in_K_1_m _ _ ps%ps m%positive.

Inductive ps_lap_forall {α} {R : ring α} P : list (puiseux_series α) → Prop :=
  | PLForall_nil : ∀ l, (l = [])%pslap → ps_lap_forall P l
  | PLForall_cons : ∀ x l,
      ([x … l] ≠ [])%pslap
      → P x
      → ps_lap_forall P l
      → ps_lap_forall P [x … l].

Arguments ps_lap_forall α%type_scope _ _ l%pslap.

Add Parametric Morphism α (R : ring α) : (@in_K_1_m _ R)
  with signature eq_ps ==> eq ==> iff
  as in_K_1_m_morph.
Proof.
intros a b Hab n.
split; intros H.
 inversion_clear H.
 destruct H0 as (ps₁, H).
 constructor.
 exists ps₁.
 destruct H as (H, Hpo).
 split; [ idtac | assumption ].
 transitivity a; assumption.

 inversion_clear H.
 destruct H0 as (ps₁, H).
 constructor.
 exists ps₁.
 destruct H as (H, Hpo).
 split; [ idtac | assumption ].
 symmetry in Hab.
 transitivity b; assumption.
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
rewrite Z.mul_min_distr_nonneg_r in Hab; auto.
unfold ps_terms_add in Hab.
unfold cm_factor in Hab.
rewrite Hpa, Hpb in Hab.
rewrite Z.mul_min_distr_nonneg_r in Hab; auto.
rewrite Z.mul_min_distr_nonneg_r in Hab; auto.
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
split; auto.
rewrite <- Hab.
rewrite ps_adjust_eq with (n := O) (k := m).
unfold adjust_ps; simpl.
rewrite Z.sub_0_r.
rewrite series_shift_0.
apply mkps_morphism; auto.
unfold adjust_series; simpl.
rewrite Z2Nat.inj_mul; simpl; auto.
 rewrite Z2Nat.inj_mul; simpl; auto.
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
split; auto.
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

Lemma hd_in_K_1_m : ∀ a la m,
  (∀ b, ps_lap_in b [a … la] → in_K_1_m b m)
  → in_K_1_m a m.
Proof.
intros a la m Hla.
destruct (ps_zerop R a) as [Ha| Ha].
 rewrite Ha; apply ps_zero_in_K_1_m.

 apply Hla; left.
 split; [ idtac | reflexivity ].
 intros H; apply Ha; clear Ha.
 apply lap_eq_cons_nil_inv in H.
 destruct H; assumption.
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
    eapply hd_in_K_1_m; eauto .

    eapply hd_in_K_1_m; eauto .

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
    eapply hd_in_K_1_m; eauto .

    eapply hd_in_K_1_m; eauto .

   apply in_K_1_m_lap_add_compat with (m := m) in Hc; auto.
    intros d Hd.
    apply in_K_1_m_lap_add_compat with (m := m) in Hd; auto.
     intros e He.
     apply IHla with (lb := [b]); auto.
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
       eapply hd_in_K_1_m; eauto .

       destruct (ps_zerop R b') as [Hb| Hb].
        rewrite Hb; apply ps_zero_in_K_1_m.

        apply Hlb; right; left.
        split; [ idtac | reflexivity ].
        intros H; apply Hb; clear Hb.
        apply lap_eq_cons_nil_inv in H.
        destruct H; assumption.

      rewrite lap_mul_nil_l in Hf.
      rewrite lap_eq_0, lap_add_nil_r in Hf.
      apply IHlb; auto.
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

     apply IHla with (lb := lb); auto.
      intros e He.
      destruct (ps_zerop R e) as [Hf| Hf].
       rewrite Hf; apply ps_zero_in_K_1_m.

       apply Hla; right; assumption.

      intros e He.
      destruct (ps_zerop R e) as [Hf| Hf].
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

Theorem minus_beta_in_K_1_mq : ∀ pol ns m a c q,
  ns ∈ newton_segments pol
  → m = ps_list_com_polord (al pol)
  → q = q_of_ns pol ns
  → a = ps_monom c (- β ns)
  → in_K_1_m a (m * q).
Proof.
intros pol ns m a c q Hns Hm Hq Ha.
constructor; subst a.
remember (p_of_ns pol ns) as p eqn:Hp .
remember Hns as Hgp; clear HeqHgp.
eapply gamma_eq_p_mq in Hgp; try eassumption.
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
remember Hns as Him; clear HeqHim.
symmetry in Hini.
eapply com_den_of_ini_pt in Him; eauto .
remember Hns as Hbm; clear HeqHbm.
apply points_in_any_newton_segment with (h := Qnat j) (αh := αj) in Hbm.
 rewrite Him, Hgp in Hbm.
 remember (mj_of_ns pol ns) as mj.
 remember (mj * ' q + Z.of_nat j * p # m * q) as v.
 exists (ps_monom c (- v)); subst v; simpl.
 split; [ idtac | reflexivity ].
 rewrite Hbm.
 unfold ps_monom; simpl.
 rewrite ps_adjust_eq with (n := O) (k := m).
 unfold adjust_ps; simpl.
 rewrite Z.sub_0_r.
 rewrite fold_series_const.
 rewrite stretch_series_const, series_shift_0.
 apply mkps_morphism; try reflexivity.
  rewrite Z.mul_opp_l; f_equal.
  rewrite Z.mul_add_distr_r; f_equal.
  rewrite <- Z.mul_assoc; f_equal.
  apply Z.mul_comm.

  apply Pos.mul_comm.

 left; symmetry; eassumption.
Qed.

Theorem gamma_in_K_1_mq : ∀ pol ns m a c q,
  ns ∈ newton_segments pol
  → m = ps_list_com_polord (al pol)
  → q = q_of_ns pol ns
  → (a = ps_monom c (γ ns))%ps
  → in_K_1_m a (m * q).
Proof.
intros pol ns m a c q Hns Hm Hq Ha.
constructor.
remember (p_of_ns pol ns) as p eqn:Hp .
remember Hns as Hgp; clear HeqHgp.
eapply gamma_eq_p_mq in Hgp; try eassumption.
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

Theorem com_polord_in_K_1_m : ∀ m a la,
  m = ps_list_com_polord la
  → ps_lap_in a la
  → in_K_1_m a m.
Proof.
intros m a la Hm Ha.
revert a m Hm Ha.
induction la as [| b]; intros; [ contradiction | idtac ].
simpl in Ha.
destruct Ha as [(Ha, Hb)| Ha].
 subst m; simpl.
 rewrite Pos.mul_comm.
 apply in_K_1_m_lap_mul_r_compat.
 rewrite <- Hb; constructor.
 exists b; split; reflexivity.

 subst m; simpl.
 apply in_K_1_m_lap_mul_r_compat.
 apply IHla; [ reflexivity | assumption ].
Qed.

Lemma next_pol_in_K_1_mq : ∀ pol ns m c b q,
  ns ∈ newton_segments pol
  → m = ps_list_com_polord (al pol)
  → c = ac_root (Φq pol ns)
  → q = q_of_ns pol ns
  → ps_lap_in b (al (next_pol pol (β ns) (γ ns) c))
  → in_K_1_m b (m * q).
Proof.
intros pol ns m c b q Hns Hm Hc Hq Hb.
remember (al (next_pol pol (β ns) (γ ns) c)) as la₁ eqn:Hla₁ .
unfold next_pol in Hla₁; simpl in Hla₁.
unfold next_lap in Hla₁.
subst la₁.
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
  eapply com_polord_in_K_1_m; eassumption.

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
