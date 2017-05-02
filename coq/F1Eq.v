(* F1Eq.v *)

Require Import Utf8 QArith NPeano Sorted.

Require Import ConvexHullMisc.
Require Import ConvexHull.
Require Import PolyConvexHull.
Require Import Field.
Require Import Misc.
Require Import Newton.
Require Import Nbar.
Require Import Qbar.
Require Import SplitList.
Require Import Fsummation.
Require Import Fpolynomial.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_mul.
Require Import Ps_div.
Require Import Ps_add_compat.
Require Import PSpolynomial.
Require Import Puiseux_base.
Require Import CharactPolyn.
Require Import AlgCloCharPol.

Set Implicit Arguments.

(* *)

(* pol₁(x,y₁) = x^(-β₁).pol(x,x^γ₁.(c₁ + y₁)) *)
Definition next_lap α {R : ring α} {K : field R} pol β₁ γ₁ (c₁ : α) :=
  let _ := ps_ring K in
  ([ps_monom 1%K (- β₁)] *
   lap_compose pol [ps_monom c₁ γ₁; ps_monom 1%K γ₁ … []])%lap.

Definition next_pol α {R : ring α} {K : field R} pol β₁ γ₁ c₁ :=
  (POL (next_lap (al pol) β₁ γ₁ c₁))%pol.

(* *)

Definition lap_summation α {R : ring α} {K : field R} (li : list nat) g :=
  List.fold_right (λ i accu, lap_add accu (g i)) [] li.

Definition poly_summation α {R : ring α} {K : field R} (li : list nat) g :=
  (POL (lap_summation li (λ i, al (g i))))%pol.

Definition lap_inject_K_in_Kx α {R : ring α} {K : field R} la :=
  List.map (λ c, ps_monom c 0) la.

Definition poly_inject_K_in_Kx α {R : ring α} {K : field R} pol :=
  (POL (lap_inject_K_in_Kx (al pol)))%pol.

Definition ps_lap_summ α {R : ring α} {K : field R} ln f :=
  @lap_summation (puiseux_series α) (ps_ring K) ln f.

Definition ps_pol_summ α {R : ring α} {K : field R} ln f :=
  @poly_summation (puiseux_series α) (ps_ring K) ln f.

(* *)

Add Parametric Morphism α (r : ring α) (K : field r) : ps_monom
  with signature rng_eq ==> Qeq ==> eq_ps
  as ps_monom_qeq_morph.
Proof.
intros a b Hab p q Hpq.
progress unfold ps_monom; simpl.
rewrite ps_adjust_eq with (n := O) (k := Qden q); simpl.
symmetry.
rewrite ps_adjust_eq with (n := O) (k := Qden p); simpl.
progress unfold adjust_ps; simpl.
do 2 rewrite Z.sub_0_r.
do 2 rewrite series_shift_0.
rewrite Hpq, Pos.mul_comm.
apply mkps_morphism; try reflexivity.
progress unfold series_stretch; simpl.
constructor; simpl; intros i.
destruct (zerop (i mod Pos.to_nat (Qden p))) as [H₁| H₁].
 apply Nat.mod_divides in H₁; auto.
 destruct H₁ as (c, Hc).
 destruct (zerop (i / Pos.to_nat (Qden p))) as [H₂| H₂].
  rewrite Nat.mul_comm in Hc.
  rewrite Hc, Nat.div_mul in H₂; auto.
  subst c; simpl in Hc.
  subst i; simpl.
  rewrite Nat.mod_0_l; auto; simpl.
  rewrite Nat.div_0_l; auto; simpl.
  symmetry; assumption.

  rewrite Nat.mul_comm in Hc.
  rewrite Hc, Nat.div_mul in H₂; auto.
  destruct (zerop (i mod Pos.to_nat (Qden q))) as [H₃| H₃].
   apply Nat.mod_divides in H₃; auto.
   destruct H₃ as (d, Hd).
   rewrite Nat.mul_comm in Hd.
   rewrite Hd, Nat.div_mul; auto.
   destruct d; [ idtac | reflexivity ].
   simpl in Hd.
   subst i.
   apply Nat.mul_eq_0 in Hd.
   destruct Hd as [Hd| Hd].
    subst c; exfalso; revert H₂; apply Nat.lt_irrefl.

    exfalso; revert Hd; apply Pos2Nat_ne_0.

   reflexivity.

 destruct (zerop (i mod Pos.to_nat (Qden q))) as [H₃| H₃].
  apply Nat.mod_divides in H₃; auto.
  destruct H₃ as (d, Hd).
  rewrite Nat.mul_comm in Hd.
  rewrite Hd, Nat.div_mul; auto.
  destruct d; [ idtac | reflexivity ].
  simpl in Hd.
  subst i.
  rewrite Nat.mod_0_l in H₁; auto.
  exfalso; revert H₁; apply Nat.lt_irrefl.

  reflexivity.
Qed.

Add Parametric Morphism α (R : ring α) (K : field R) :
    (@lap_inject_K_in_Kx _ R K)
  with signature @lap_eq _ R ==> @lap_eq _ (ps_ring K)
  as lap_inject_k_in_Kx_morph.
Proof.
intros la lb Hab.
revert lb Hab.
induction la as [| a]; intros; simpl.
 induction lb as [| b]; [ reflexivity | simpl ].
 apply lap_eq_nil_cons_inv in Hab.
 destruct Hab as (Hb, Hlb).
 constructor.
  rewrite Hb; simpl.
  apply ps_zero_monom_eq.

  apply IHlb; assumption.

 destruct lb as [| b]; simpl.
  apply lap_eq_cons_nil_inv in Hab.
  destruct Hab as (Ha, Hla).
  constructor.
   rewrite Ha; simpl.
   apply ps_zero_monom_eq.

   rewrite IHla; [ idtac | eassumption ].
   reflexivity.

  apply lap_eq_cons_inv in Hab.
  destruct Hab as (Hab, Hlab).
  rewrite Hab.
  constructor; [ reflexivity | idtac ].
  apply IHla; assumption.
Qed.

Add Parametric Morphism α (R : ring α) (K : field R) :
    (@poly_inject_K_in_Kx _ R K)
  with signature eq_poly ==> @eq_poly _ (ps_ring K)
  as poly_inject_k_in_Kx_morph.
Proof.
intros P Q HPQ.
progress unfold eq_poly; simpl.
rewrite HPQ; reflexivity.
Qed.

Theorem list_fold_right_compat : ∀ α β equal g h (a₀ : α) (l : list β),
  (∀ x y z, equal x y → equal (g z x) (h z y))
  → equal a₀ a₀
    → equal (List.fold_right g a₀ l) (List.fold_right h a₀ l).
Proof.
intros α β equal g h a₀ l Hcomp Heq.
induction l as [| x]; intros; [ assumption | idtac ].
apply Hcomp; assumption.
Qed.

Theorem lap_mul_summation :
  ∀ α (Rx : ring (puiseux_series α)) (Kx : field Rx) la l f,
  (la * lap_summation l f = lap_summation l (λ i, la * f i))%lap.
Proof.
intros α Rx Kx la l f.
induction l as [| j]; intros; simpl.
 rewrite lap_mul_nil_r; reflexivity.

 rewrite lap_mul_add_distr_l, IHl.
 reflexivity.
Qed.

Section on_fields.

Variable α : Type.
Variable R : ring α.
Variable K : field R.

Theorem split_summation : ∀ g l l₁ l₂,
  split_list l l₁ l₂
  → (poly_summation l₁ g + poly_summation l₂ g =
     poly_summation l g)%pol.
Proof.
intros g l l₁ l₂ Hss.
progress unfold poly_summation; simpl.
progress unfold eq_poly; simpl.
revert l₁ l₂ Hss.
induction l as [| n]; intros; simpl.
 inversion Hss; subst; reflexivity.

 inversion Hss; subst; simpl.
  rewrite lap_add_shuffle0.
  rewrite IHl; [ reflexivity | assumption ].

  rewrite lap_add_assoc.
  rewrite IHl; [ reflexivity | assumption ].
Qed.

Theorem ps_monom_split_mul : ∀ c pow,
  (ps_monom c pow = ps_monom c 0 * ps_monom 1%K pow)%ps.
Proof.
intros c pow.
rewrite <- ps_monom_add_r.
rewrite Qplus_0_l; reflexivity.
Qed.

Theorem ps_monom_mul_r_pow : ∀ c p n,
  (ps_monom c (Qnat n * p) =
   ps_monom c 0 * ps_monom 1%K p ^ n)%ps.
Proof.
intros c p n.
induction n; simpl.
 rewrite rng_mul_1_r.
 progress unfold Qnat; simpl.
 rewrite Qmult_0_l; reflexivity.

 rewrite ps_mul_assoc.
 rewrite rng_mul_shuffle0; simpl.
 rewrite <- IHn.
 assert (Qnat (S n) * p == Qnat n * p + p) as H.
  progress unfold Qnat; simpl.
  rewrite Zpos_P_of_succ_nat.
  progress unfold Qmult, Qplus; simpl.
  progress unfold Qeq.
  simpl.
  rewrite <- Z.mul_add_distr_r.
  rewrite Pos2Z.inj_mul.
  symmetry.
  rewrite <- Z.mul_assoc.
  apply Z.mul_cancel_r.
   simpl.
   apply Pos2Z_ne_0.

   progress unfold Z.succ; simpl.
   rewrite Z.mul_add_distr_r.
   rewrite Z.mul_1_l; reflexivity.

  rewrite H.
  rewrite ps_monom_add_r.
  reflexivity.
Qed.

Theorem poly_summation_add : ∀ g h l,
  (poly_summation l g + poly_summation l h =
   poly_summation l (λ i, g i + h i))%pol.
Proof.
intros g h l.
progress unfold poly_summation, eq_poly; simpl.
induction l as [| i]; intros; [ reflexivity | simpl ].
do 2 rewrite lap_add_assoc.
apply lap_add_compat; [ idtac | reflexivity ].
rewrite lap_add_shuffle0.
apply lap_add_compat; [ assumption | reflexivity ].
Qed.

Theorem rng_list_map_nth : ∀ A n f l (d : A) fd,
  (fd = f d)%K
  → (List.nth n (List.map f l) fd = f (List.nth n l d))%K.
Proof.
intros A n f l d fd Hfd.
revert n d fd Hfd.
induction l as [| x]; intros; simpl.
 destruct n; assumption.

 destruct n; [ reflexivity | idtac ].
 apply IHl; assumption.
Qed.

End on_fields.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Theorem lap_f₁_eq_x_min_β₁_comp : ∀ la β₁ γ₁ c₁,
  (next_lap la β₁ γ₁ c₁ =
   [ps_monom 1%K (- β₁)] *
   la ∘ ([ps_monom 1%K γ₁] * [ps_monom c₁ 0; 1%ps … []]))%pslap.
Proof.
intros la β₁ γ₁ c₁.
progress unfold next_lap.
apply lap_mul_compat; [ reflexivity | idtac ].
apply lap_compose_compat; [ reflexivity | idtac ].
progress unfold ps_lap_mul, lap_mul; simpl.
progress unfold summation; simpl.
rewrite rng_mul_0_l.
do 3 rewrite rng_add_0_r.
simpl.
constructor.
 rewrite ps_mul_comm; simpl.
 apply ps_monom_split_mul.

 constructor; [ idtac | reflexivity ].
 rewrite rng_mul_1_r; reflexivity.
Qed.

(* [Walker, p. 100] « f₁(x,y₁) = x^(-β₁).f(x,x^γ₁(c₁+y₁)) » *)
Theorem f₁_eq_x_min_β₁_comp : ∀ pol β₁ γ₁ c₁,
  (next_pol pol β₁ γ₁ c₁ =
   POL [ps_monom 1%K (- β₁)] *
   pol ∘ (POL [ps_monom 1%K γ₁] * POL [ps_monom c₁ 0; 1%ps … []]))%pspol.
Proof.
intros pol β₁ γ₁ c₁.
apply lap_f₁_eq_x_min_β₁_comp; reflexivity.
Qed.

Theorem f₁_eq_x_min_β₁_summation : ∀ pol β₁ γ₁ c₁,
  (next_pol pol β₁ γ₁ c₁ =
   POL [ps_monom 1%K (- β₁)] *
   ps_pol_summ ps_field (List.seq 0 (length (al pol)))
     (λ h,
      let āh := ps_poly_nth h pol in
      POL [(āh * ps_monom 1%K (Qnat h * γ₁))%ps] *
      POL [ps_monom c₁ 0; 1%ps … []] ^ h))%pspol.
Proof.
intros pol β₁ γ₁ c.
rewrite f₁_eq_x_min_β₁_comp.
progress unfold ps_pol_comp.
rewrite poly_compose_compose2.
apply poly_mul_compat; [ reflexivity | idtac ].
progress unfold poly_compose2; simpl.
progress unfold lap_compose2, poly_summation; simpl.
progress unfold eq_poly; simpl.
apply list_fold_right_compat; [ idtac | reflexivity ].
intros la lb i Heq.
apply lap_add_compat; [ assumption | idtac ].
progress unfold ps_poly_nth, ps_lap_nth.
rewrite lap_power_mul.
rewrite lap_mul_assoc.
apply lap_mul_compat; [ idtac | reflexivity ].
clear la lb Heq.
remember (al pol) as la; clear pol Heqla.
revert la.
induction i; intros; simpl.
 rewrite lap_mul_1_r.
 constructor; [ idtac | reflexivity ].
 progress unfold Qnat; simpl.
 rewrite <- ps_mul_1_r in |- * at 1.
 apply ps_mul_compat_l.
 rewrite Qmult_0_l; reflexivity.

 destruct la as [| a]; simpl.
  rewrite lap_mul_assoc; simpl.
  rewrite lap_eq_0.
  rewrite lap_mul_nil_l.
  rewrite lap_mul_nil_l.
  constructor; [ idtac | reflexivity ].
  simpl.
  rewrite ps_mul_0_l; reflexivity.

  rewrite lap_mul_assoc.
  rewrite lap_mul_shuffle0.
  rewrite IHi.
  progress unfold lap_mul; simpl.
  rewrite summation_only_one; simpl.
  constructor; [ idtac | reflexivity ].
  simpl.
  rewrite <- ps_mul_assoc.
  apply ps_mul_compat_l.
  rewrite ps_monom_mul_r_pow; symmetry.
  rewrite ps_monom_mul_r_pow; symmetry.
  rewrite rng_mul_shuffle0; simpl.
  rewrite rng_mul_assoc; simpl.
  reflexivity.
Qed.

(* [Walker, p. 100] «
    f₁(x,y₁) = x^(-β₁)Σāh.x^(h.γ₁).(c₁+y₁)^h + x^(-β₁)Σāl.x^(l.γ₁).(c₁+y₁)^l
  » *)
(* we can split the sum on 0..n into two sub lists l₁, l₂ in any way *)
Theorem f₁_eq_x_min_β₁_summation_split : ∀ pol β₁ γ₁ c₁ l₁ l₂,
  split_list (List.seq 0 (length (al pol))) l₁ l₂
  → (next_pol pol β₁ γ₁ c₁ =
      POL [ps_monom 1%K (- β₁)] *
      ps_pol_summ ps_field l₁
        (λ (h : nat) (āh:=ps_poly_nth h pol),
         POL [(āh * ps_monom 1%K (Qnat h * γ₁))%ps] *
         POL [ps_monom c₁ 0; 1%ps … []] ^ h) +
      POL [ps_monom 1%K (- β₁)] *
      ps_pol_summ ps_field l₂
        (λ (l : nat) (āl:=ps_poly_nth l pol),
         POL [(āl * ps_monom 1%K (Qnat l * γ₁))%ps] *
         POL [ps_monom c₁ 0; 1%ps … []] ^ l))%pspol.
Proof.
intros pol β₁ γ₁ c₁ l₁ l₂ Hss.
progress unfold ps_pol_add, ps_pol_mul, ps_pol_summ.
rewrite <- poly_mul_add_distr_l.
rewrite split_summation; [ idtac | eassumption ].
apply f₁_eq_x_min_β₁_summation; assumption.
Qed.

Fixpoint coeff_of_term i tl :=
  match tl with
  | [] => 0%K
  | [t₁ … tl₁] =>
      if eq_nat_dec i (power t₁) then coeff t₁ else coeff_of_term i tl₁
  end.

Fixpoint ord_of_pt i pl :=
  match pl with
  | [] => 0
  | [(x, y) … pl₁] => if Qeq_dec (Qnat i) x then y else ord_of_pt i pl₁
  end.

(* Σāh.x^(hγ₁).(c₁+y₁)^h =
   Σah.x^(αh+hγ₁).(c₁+y₁)^h + Σ(āh-ah.x^αh).x^(hγ₁).(c₁+y₁)^h *)
Theorem summation_split_val : ∀ pol ns γ₁ c₁ pl tl l,
  newton_segments pol = Some ns
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point pol) pl
      → l = List.map (λ t, power t) tl
        → (ps_pol_summ ps_field l
             (λ h,
              let āh := ps_poly_nth h pol in
              POL [(āh * ps_monom 1%K (Qnat h * γ₁))%ps] *
              POL [ps_monom c₁ 0; 1%ps … []] ^ h) =
           ps_pol_summ ps_field l
             (λ h,
              let ah := ps_monom (coeff_of_term h tl) 0 in
              let αh := ord_of_pt h pl in
              POL [(ah * ps_monom 1%K (αh + Qnat h * γ₁))%ps] *
              POL [ps_monom c₁ 0; 1%ps … []] ^ h) +
           ps_pol_summ ps_field l
             (λ h,
              let āh := ps_poly_nth h pol in
              let ah := ps_monom (coeff_of_term h tl) 0 in
              let αh := ord_of_pt h pl in
              POL [((āh - ah * ps_monom 1%K αh) *
                    ps_monom 1%K (Qnat h * γ₁))%ps] *
              POL [ps_monom c₁ 0; 1%ps … []] ^ h))%pspol.
Proof.
intros pol ns γ₁ c₁ pl tl l Hns Hpl Htl Hl.
progress unfold ps_pol_add, ps_pol_summ.
rewrite poly_summation_add; simpl.
apply lap_eq_list_fold_right; intros i a b Hi Heq.
apply lap_add_compat; [ assumption | simpl ].
rewrite <- lap_mul_add_distr_r; simpl.
apply lap_mul_compat; [ idtac | reflexivity ].
constructor; [ simpl | reflexivity ].
rewrite ps_monom_add_r.
rewrite rng_mul_assoc.
rewrite rng_mul_add_distr_r.
simpl.
rewrite rng_mul_opp_l; simpl.
rewrite rng_add_assoc; simpl.
rewrite rng_add_comm; simpl.
rewrite rng_add_assoc; simpl.
rewrite rng_add_opp_l, rng_add_0_l; reflexivity.
Qed.

(* [Walker, p. 101] « Since āh = ah.x^αh + ...,

     f₁(x,y₁) = x^(-β₁).Σah.x^(αh+h.γ₁).(c₁+y₁)^h +
                x^(-β₁).[Σ(āh-ah.x^αh).x^(h.γ₁).(c₁+y₁)^h +
                         Σāl.x^(l.γ₁).(c₁+y₁)^l]
   » *)
Theorem f₁_eq_sum_α_hγ_to_rest : ∀ pol ns β₁ γ₁ c₁ pl tl l₁ l₂,
  newton_segments pol = Some ns
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point pol) pl
      → l₁ = List.map (λ t, power t) tl
        → split_list (List.seq 0 (length (al pol))) l₁ l₂
          → (next_pol pol β₁ γ₁ c₁ =
             POL [ps_monom 1%K (- β₁)] *
             ps_pol_summ ps_field l₁
               (λ h,
                let ah := ps_monom (coeff_of_term h tl) 0 in
                let αh := ord_of_pt h pl in
                POL [(ah * ps_monom 1%K (αh + Qnat h * γ₁))%ps] *
                POL [ps_monom c₁ 0; 1%ps … []] ^ h) +
             POL [ps_monom 1%K (- β₁)] *
             (ps_pol_summ ps_field l₁
                (λ h,
                 let āh := ps_poly_nth h pol in
                 let ah := ps_monom (coeff_of_term h tl) 0 in
                 let αh := ord_of_pt h pl in
                 POL [((āh - ah * ps_monom 1%K αh) *
                       ps_monom 1%K (Qnat h * γ₁))%ps] *
                 POL [ps_monom c₁ 0; 1%ps … []] ^ h) +
              ps_pol_summ ps_field l₂
                (λ l,
                 let āl := ps_poly_nth l pol in
                 POL [(āl * ps_monom 1%K (Qnat l * γ₁))%ps] *
                 POL [ps_monom c₁ 0; 1%ps … []] ^ l)))%pspol.
Proof.
intros pol ns β₁ γ₁ c₁ pl tl l₁ l₂ Hns Hpl Htl Hl Hss.
progress unfold ps_pol_add at 2.
progress unfold ps_pol_mul at 3.
rewrite poly_mul_add_distr_l.
progress unfold ps_pol_add at 1.
rewrite poly_add_assoc.
progress unfold ps_pol_mul at 1.
rewrite <- poly_mul_add_distr_l.
rewrite fold_ps_pol_add, fold_ps_pol_mul.
rewrite fold_ps_pol_add, fold_ps_pol_mul.
rewrite <- summation_split_val; try eassumption.
apply f₁_eq_x_min_β₁_summation_split; assumption.
Qed.

Theorem ord_is_ord_of_pt : ∀ pl h,
  Sorted fst_lt pl
  → (∀ pt, pt ∈ pl → ∃ (h : nat) (αh : Q), pt = (Qnat h, αh))
    → h ∈ List.map (λ x, nat_num (fst x)) pl
      → (Qnat h, ord_of_pt h pl) ∈ pl.
Proof.
(* à nettoyer sérieusement *)
intros pl h Hsort Hnat Hin.
induction pl as [| (l, al)]; [ contradiction | simpl ].
destruct (Qeq_dec (Qnat h) l) as [H| H].
 simpl in Hin.
 destruct Hin as [Hin| Hin].
  left; subst h.
  assert ((l, al) ∈ [(l, al) … pl]) as Hpt by (left; reflexivity).
  apply Hnat in Hpt.
  destruct Hpt as (h, (ah, Hpt)).
  injection Hpt; clear Hpt; intros; subst l al.
  rewrite nat_num_Qnat; simpl.
  reflexivity.

  exfalso.
  revert Hnat Hsort Hin H; clear; intros.
  revert al h Hnat Hsort Hin H.
  induction pl as [| (m, am)]; intros; [ contradiction | simpl ].
  simpl in Hin.
  destruct Hin as [Hin| Hin].
   subst h.
   apply Sorted_inv_2 in Hsort.
   destruct Hsort as (Hrel, Hsort).
   progress unfold fst_lt in Hrel; simpl in Hrel.
   rewrite <- H in Hrel.
   progress unfold Qnat, nat_num in Hrel.
   rewrite Z2Nat.id in Hrel; simpl in Hrel.
    assert ((m, am) ∈ [(l, al); (m, am) … pl]) as Hpt
     by (right; left; reflexivity).
    apply Hnat in Hpt.
    destruct Hpt as (p, (ap, Hp)).
    injection Hp; clear Hp; intros; subst m am.
    simpl in Hrel.
    revert Hrel; apply Z.lt_irrefl.

    assert ((m, am) ∈ [(l, al); (m, am) … pl]) as Hpt
     by (right; left; reflexivity).
    apply Hnat in Hpt.
    destruct Hpt as (p, (ap, Hp)).
    injection Hp; clear Hp; intros; subst m am.
    simpl.
    apply Nat2Z.is_nonneg.

   apply Sorted_minus_2nd in Hsort.
    eapply IHpl; try eassumption.
    intros pt Hpt.
    apply Hnat.
    destruct Hpt as [Hpt| Hpt].
     rewrite Hpt; left; reflexivity.

     right; right; assumption.

    intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 right.
 apply IHpl.
  eapply Sorted_inv_1; eassumption.

  intros pt Hpt.
  apply Hnat.
  right; assumption.

  destruct Hin as [Hin| Hin]; [ idtac | assumption ].
  simpl in Hin.
  exfalso; apply H; clear H.
  subst h.
  assert ((l, al) ∈ [(l, al) … pl]) as Hpt by (left; reflexivity).
  apply Hnat in Hpt.
  destruct Hpt as (p, (ap, Hp)).
  injection Hp; clear Hp; intros; subst l al.
  rewrite nat_num_Qnat; reflexivity.
Qed.

(* Σah.x^(αh+h.γ).(c₁+y₁)^h = Σah.x^β.(c₁+y₁)^h *)
Theorem subst_αh_hγ : ∀ pol ns pl tl l₁ c₁,
  newton_segments pol = Some ns
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point pol) pl
      → l₁ = List.map (λ t, power t) tl
        → (ps_pol_summ ps_field l₁
             (λ h,
              let ah := ps_monom (coeff_of_term h tl) 0 in
              let αh := ord_of_pt h pl in
              POL [(ah * ps_monom 1%K (αh + Qnat h * γ ns))%ps] *
              POL [ps_monom c₁ 0; 1%ps … []] ^ h) =
           ps_pol_summ ps_field l₁
             (λ h,
              let ah := ps_monom (coeff_of_term h tl) 0 in
              POL [(ah * ps_monom 1%K (β ns))%ps] *
              POL [ps_monom c₁ 0; 1%ps … []] ^ h))%pspol.
Proof.
intros pol ns pl tl l₁ c₁ Hns Hpl Htl Hl.
progress unfold eq_poly; simpl.
apply lap_eq_list_fold_right.
intros h a b Hh Heq.
apply lap_add_compat; [ assumption | simpl ].
apply lap_mul_compat; [ simpl | reflexivity ].
constructor; [ idtac | reflexivity ].
apply rng_mul_compat; [ reflexivity | simpl ].
rewrite points_in_any_newton_segment; [ reflexivity | eassumption | idtac ].
apply list_in_cons_app.
remember Hns as Hsort; clear HeqHsort.
apply ini_oth_fin_pts_sorted in Hsort.
rewrite <- Hpl in Hsort; rewrite <- Hpl.
subst tl l₁.
rewrite List.map_map in Hh; simpl in Hh.
assert (∀ pt, pt ∈ pl → ∃ h αh, pt = (Qnat h, αh)) as Hnat.
 intros pt Hpt.
 eapply points_in_newton_segment_have_nat_abscissa; [ eassumption | idtac ].
 subst pl; assumption.

 apply ord_is_ord_of_pt; assumption.
Qed.

Theorem poly_summation_mul : ∀ l x g₁ g₂,
  (ps_pol_summ ps_field l (λ h, POL [(g₁ h * x)%ps] * g₂ h) =
   POL [x] * ps_pol_summ ps_field l (λ h, POL [g₁ h] * g₂ h))%pspol.
Proof.
intros l x g₁ g₂.
progress unfold ps_pol_eq, eq_poly; simpl.
progress unfold ps_pol_summ, lap_summation; simpl.
induction l as [| i]; intros; simpl.
 rewrite lap_mul_nil_r; reflexivity.

 rewrite IHl.
 rewrite lap_mul_add_distr_l.
 simpl.
 apply lap_add_compat; [ reflexivity | simpl ].
 rewrite lap_mul_assoc.
 apply lap_mul_compat; [ idtac | reflexivity ].
 progress unfold lap_mul; simpl.
 rewrite summation_only_one; simpl.
 rewrite rng_mul_comm; reflexivity.
Qed.

(* Replacing αh + h.γ₁ with β₁, and simplifying the first summation, we get:
     f₁(x,y₁) = Σah.(c₁+y₁)^h +
                x^(-β₁).[Σ(āh-ah.x^αh).x^(h.γ₁).(c₁+y₁)^h +
                         Σāl.x^(l.γ₁).(c₁+y₁)^l]
*)
Theorem f₁_eq_sum_without_x_β₁_plus_sum : ∀ pol ns c₁ pl tl l₁ l₂,
  newton_segments pol = Some ns
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point pol) pl
      → l₁ = List.map (λ t, power t) tl
        → split_list (List.seq 0 (length (al pol))) l₁ l₂
          → (next_pol pol (β ns) (γ ns) c₁ =
             ps_pol_summ ps_field l₁
               (λ h,
                let ah := ps_monom (coeff_of_term h tl) 0 in
                POL [ah] *
                POL [ps_monom c₁ 0; 1%ps … []] ^ h) +
             POL [ps_monom 1%K (- β ns)] *
             (ps_pol_summ ps_field l₁
                (λ h,
                 let āh := ps_poly_nth h pol in
                 let ah := ps_monom (coeff_of_term h tl) 0 in
                 let αh := ord_of_pt h pl in
                 POL [((āh - ah * ps_monom 1%K αh) *
                       ps_monom 1%K (Qnat h * γ ns))%ps] *
                 POL [ps_monom c₁ 0; 1%ps … []] ^ h) +
              ps_pol_summ ps_field l₂
                (λ l,
                 let āl := ps_poly_nth l pol in
                 POL [(āl * ps_monom 1%K (Qnat l * γ ns))%ps] *
                 POL [ps_monom c₁ 0; 1%ps … []] ^ l)))%pspol.
Proof.
intros pol ns c₁ pl tl l₁ l₂ Hns Hpl Htl Hl Hss.
remember Hns as H; clear HeqH.
eapply f₁_eq_sum_α_hγ_to_rest in H; try eassumption.
rewrite H.
apply poly_add_compat; [ idtac | reflexivity ].
rewrite subst_αh_hγ; try eassumption; simpl.
rewrite poly_summation_mul.
progress unfold ps_pol_mul.
rewrite poly_mul_assoc.
symmetry.
rewrite <- poly_mul_1_l in |- * at 1.
apply poly_mul_compat; [ idtac | reflexivity ].
progress unfold poly_mul; simpl.
progress unfold eq_poly; simpl.
progress unfold ps_one; simpl.
progress unfold lap_mul; simpl.
rewrite summation_only_one; simpl.
constructor; [ idtac | reflexivity ].
progress unfold ps_monom; simpl.
progress unfold ps_mul; simpl.
progress unfold cm; simpl.
rewrite Z.mul_opp_l.
rewrite Z.add_opp_diag_l.
rewrite stretch_series_1, series_mul_1_l.
remember (Qden (β ns) * Qden (β ns))%positive as k.
rewrite ps_adjust_eq with (k := k) (n := O).
progress unfold adjust_ps; simpl.
rewrite series_shift_0, stretch_series_1.
subst k; reflexivity.
Qed.

Theorem fold_nothing : ∀ A j len (f : _ → _ → A) g la,
  (∀ i, j ≤ i → (i < j + len)%nat → g i = false)
  → List.fold_right (λ i accu, if g i then f i accu else accu) la
       (List.seq j len) = la.
Proof.
intros A j len f g la Hg.
revert j la Hg.
induction len; intros; [ reflexivity | simpl ].
unfold lt in Hg; rewrite Nat.add_succ_r in Hg.
rewrite Hg; [ idtac | reflexivity | apply le_n_S, le_plus_l ].
apply IHlen.
intros i Hji Hij.
apply Hg; [ idtac | assumption ].
apply le_Sn_le; assumption.
Qed.

Theorem fold_right_eqb_or : ∀ A j k len f (g : _ → A → A) la,
  (j < k)%nat
  → List.fold_right (λ i accu, if Nat.eqb i j || f i then g i accu else accu)
      la (List.seq k len) =
    List.fold_right (λ i accu, if f i then g i accu else accu) la
       (List.seq k len).
Proof.
intros A j k len f g la Hjk.
revert j k Hjk.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen.
 remember (Nat.eqb k j) as b eqn:Hb .
 symmetry in Hb.
 destruct b; [ idtac | reflexivity ].
 apply Nat.eqb_eq in Hb.
 exfalso; subst k; revert Hjk; apply Nat.lt_irrefl.

 apply Nat.lt_lt_succ_r; assumption.
Qed.

Theorem ns_nat : ∀ pol ns pts,
  newton_segments pol = Some ns
  → pts = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → ∀ iq αi, (iq, αi) ∈ pts
      → ∃ i : nat, iq = Qnat i.
Proof.
intros pol ns pts Hns Hpts iq αi Hi.
assert (∃ h ah, (iq, αi) = (Qnat h, ah)) as Hnat.
 eapply points_in_newton_segment_have_nat_abscissa; [ eassumption | idtac ].
 subst pts; assumption.

 destruct Hnat as (h, (ah, Hh)).
 injection Hh; intros; subst iq ah.
 exists h; reflexivity.
Qed.

Theorem fold_right_exists : ∀ pol ns pts j k αj αk f la,
  newton_segments pol = Some ns
  → pts = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → ini_pt ns = (Qnat j, αj)
      → fin_pt ns = (Qnat k, αk)
        → (∀ i a b, ps_lap_eq a b → ps_lap_eq (f i a) (f i b))
          → ps_lap_eq
              (List.fold_right f la (List.map (λ pt, nat_num (fst pt)) pts))
              (List.fold_right
                 (λ i accu,
                  if List.existsb (λ pt, Nat.eqb i (nat_num (fst pt))) pts then
                    f i accu
                  else accu) la
                 (List.seq j (S (k - j)))).
Proof.
(* sûrement nettoyable ; putain, j'en ai chié *)
intros pol ns pts j k αj αk f la Hns Hpl Hini Hfin Hi.
assert (j < k)%nat as Hjk.
 eapply j_lt_k; try eassumption.
  rewrite Hini; simpl; rewrite nat_num_Qnat; reflexivity.

  rewrite Hfin; simpl; rewrite nat_num_Qnat; reflexivity.

 subst pts; simpl.
 rewrite Hini; simpl.
 rewrite nat_num_Qnat; simpl.
 rewrite Nat.eqb_refl; simpl.
 apply Hi.
 remember Hns as Hsort; clear HeqHsort.
 apply ini_oth_fin_pts_sorted in Hsort.
 remember (oth_pts ns ++ [fin_pt ns]) as pts eqn:Hpts .
 assert (∀ i αi, (Qnat i, αi) ∈ pts → (j < i)%nat) as Hjh.
  intros h αh H.
  symmetry in Hini.
  rewrite Hpts in H.
  apply List.in_app_or in H.
  destruct H as [H| H].
   eapply j_lt_h; try eassumption; reflexivity.

   destruct H as [H| H]; [ idtac | contradiction ].
   rewrite Hfin in H.
   injection H; clear H; intros _ H.
   apply Nat2Z.inj in H.
   subst h; assumption.

  assert (∀ iq αi, (iq, αi) ∈ pts → ∃ i, iq = Qnat i) as Hnat.
   intros iq αi Hip.
   eapply ns_nat; [ eassumption | reflexivity | idtac ].
   right; subst pts; eassumption.

   rewrite Hini in Hsort; clear Hini.
   rewrite Hfin in Hpts; clear Hfin.
   assert (List.last pts (0, 0) = (Qnat k, αk)) as Hlast.
    subst pts; simpl.
    clear; induction (oth_pts ns) as [| x l]; [ reflexivity | simpl ].
    destruct l as [| y]; [ reflexivity | simpl in IHl; simpl ].
    assumption.

    rewrite fold_right_eqb_or; [ idtac | apply Nat.lt_succ_r; reflexivity ].
    revert Hi Hjk Hjh Hnat Hlast Hsort; clear; intros.
    revert j k αj αk la Hjk Hjh Hlast Hsort.
    induction pts as [| (h, αh)]; intros.
     simpl in Hlast.
     injection Hlast; clear; intros; subst.
     rewrite <- Nat2Z.inj_0 in H0.
     progress unfold ps_lap_eq.
     apply Nat2Z.inj in H0; subst k; reflexivity.

     simpl.
     assert ((h, αh) ∈ [(h, αh) … pts]) as Hh by (left; reflexivity).
     apply Hnat in Hh.
     destruct Hh as (i, Hh).
     subst h; rename i into h.
     rewrite nat_num_Qnat.
     destruct (eq_nat_dec h k) as [H₁| H₁].
      subst h.
      pose proof (le_n_Sn k) as H.
      apply Nat.sub_le_mono_r with (p := S j) in H.
      rewrite list_seq_app with (dj := (k - S j)%nat); auto; clear H.
      rewrite List.fold_right_app; simpl.
      rewrite <- Nat.add_succ_r, <- Nat.sub_succ_l; auto; simpl.
      rewrite Nat.add_sub_assoc; [ idtac | apply Nat.lt_le_incl; auto ].
      rewrite Nat.add_comm, Nat.add_sub.
      rewrite Nat_sub_sub_distr; auto; rewrite Nat.add_succ_r.
      rewrite Nat.sub_add; [ idtac | apply Nat.lt_le_incl; auto ].
      rewrite Nat_sub_succ_diag; simpl.
      rewrite Nat.eqb_refl; simpl.
      simpl in Hlast.
      destruct pts as [| pt]; [ simpl | exfalso ].
       progress unfold ps_lap_eq.
       rewrite fold_nothing; [ reflexivity | idtac ].
       intros i Hji Hij.
       rewrite orb_false_r.
       apply Nat.eqb_neq.
       intros H; subst i.
       rewrite Nat.add_sub_assoc in Hij; auto.
       rewrite Nat.add_comm, Nat.add_sub in Hij.
       revert Hij; apply Nat.lt_irrefl.

       revert Hsort Hlast Hnat; clear; intros.
       apply Sorted_inv_1 in Hsort.
       revert pt Hsort Hlast Hnat.
       induction pts as [| pt₂]; intros.
        simpl in Hlast.
        subst pt.
        apply Sorted_inv in Hsort.
        destruct Hsort as (_, Hrel).
        progress unfold fst_lt in Hrel; apply HdRel_inv in Hrel.
        simpl in Hrel.
        revert Hrel; apply Qlt_irrefl.

        apply IHpts with (pt := pt₂).
         eapply Sorted_minus_2nd; [ idtac | eassumption ].
         intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

         assumption.

         intros iq αi Hpti.
         apply Hnat with (αi := αi).
         destruct Hpti as [H| H]; [ rewrite H; left; reflexivity | idtac ].
         right; right; assumption.

      assert (h < k)%nat as Hhk.
       apply Sorted_inv_1 in Hsort.
       clear Hjk.
       clear IHpts.
       revert h k αh αk Hsort Hlast Hnat Hjh H₁.
       induction pts as [| (l, al)]; intros.
        injection Hlast; clear Hlast; intros HH H.
        exfalso; apply H₁, Nat2Z.inj; assumption.

        assert ((l, al) ∈ [(Qnat h, αh); (l, al) … pts])
         as Hl by (right; left; reflexivity).
        apply Hnat in Hl.
        destruct Hl as (m, Hl); subst l; rename m into l.
        apply Nat.lt_le_trans with (m := l).
         apply Sorted_inv in Hsort.
         destruct Hsort as (_, Hrel).
         apply HdRel_inv in Hrel.
         progress unfold fst_lt in Hrel; simpl in Hrel.
         apply Qnat_lt; assumption.

         destruct (eq_nat_dec l k) as [H₂| H₂].
          subst l; reflexivity.

          apply Sorted_inv_1 in Hsort.
          remember [(Qnat l, al) … pts] as p; simpl in Hlast; subst p.
          apply Nat.lt_le_incl.
          eapply IHpts; try eassumption.
           intros; apply Hnat with (αi := αi); right; assumption.

           intros; apply Hjh with (αi := αi); right; assumption.

       remember Hhk as H; clear HeqH.
       apply Nat.lt_le_incl in H.
       apply Nat.sub_le_mono_r with (p := S j) in H.
       apply Nat.le_le_succ_r in H.
       rewrite <- Nat.sub_succ_l in H; auto; simpl in H.
       rewrite list_seq_app with (dj := (h - S j)%nat); auto.
       assert (j < h)%nat as Hjh₁.
        apply Hjh with (αi := αh); left; reflexivity.

        rewrite Nat.add_sub_assoc; auto; clear H.
        rewrite Nat.add_comm, Nat.add_sub.
        rewrite Nat_sub_sub_distr; auto; rewrite Nat.add_succ_r.
        rewrite Nat.sub_add; [ idtac | apply Nat.lt_le_incl; auto ].
        rewrite Nat.sub_succ_l; [ simpl | apply Nat.lt_le_incl; auto ].
        rewrite List.fold_right_app; simpl.
        rewrite Nat.eqb_refl; simpl.
        rewrite fold_nothing.
         apply Hi.
         rewrite fold_right_eqb_or.
          simpl in Hlast.
          destruct pts as [| (l, al)].
           injection Hlast; clear Hlast; intros HH H; subst αh.
           apply Nat2Z.inj in H; subst h.
           exfalso; apply H₁; reflexivity.

           eapply IHpts with (αj := αh); try eassumption.
            intros; apply Hnat with (αi := αi); right; assumption.

            intros i αi Hpti.
            apply Sorted_inv_1 in Hsort.
            simpl in Hpti.
            destruct Hpti as [H| H].
             injection H; clear H; intros; subst l al.
             apply Sorted_inv in Hsort.
             destruct Hsort as (_, Hrel).
             apply HdRel_inv in Hrel.
             progress unfold fst_lt in Hrel; simpl in Hrel.
             apply Qnat_lt; assumption.

             apply Sorted_minus_2nd in Hsort.
              revert Hsort H; clear; intros.
              revert h i αi Hsort H.
              induction pts as [| (l, al)]; [ contradiction | intros ].
              destruct H as [H| H].
               injection H; clear H; intros; subst l al.
               apply Sorted_inv in Hsort.
               destruct Hsort as (_, Hrel).
               apply HdRel_inv in Hrel.
               progress unfold fst_lt in Hrel; simpl in Hrel.
               apply Qnat_lt; assumption.

               eapply IHpts; [ idtac | eassumption ].
               eapply Sorted_minus_2nd; [ idtac | eassumption ].
               intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

              intros; eapply Qlt_trans; eassumption.

            eapply Sorted_inv_1; eassumption.

          apply Nat.lt_succ_r; reflexivity.

         intros i Hji Hij.
         remember Hji as H; clear HeqH.
         rewrite Nat.add_sub_assoc in Hij; auto; clear H.
         rewrite Nat.add_sub_swap, Nat.sub_diag in Hij; auto.
         remember (Nat.eqb i h) as b eqn:Hb .
         symmetry in Hb.
         destruct b.
          apply Nat.eqb_eq in Hb.
          rewrite Hb in Hij.
          exfalso; revert Hij; apply Nat.lt_irrefl.

          simpl.
          apply Sorted_inv_1 in Hsort.
          revert Hnat Hsort Hij; clear; intros.
          revert h i Hnat Hsort Hij.
          induction pts as [| (l, al)]; intros; [ reflexivity | simpl ].
          assert ((l, al) ∈ [(Qnat h, αh); (l, al) … pts]) as H.
           right; left; reflexivity.

           apply Hnat in H.
           destruct H as (m, Hm); subst l; rename m into l.
           rewrite nat_num_Qnat.
           remember (Nat.eqb i l) as b eqn:Hb .
           symmetry in Hb.
           destruct b; simpl.
            apply Nat.eqb_eq in Hb; subst l.
            apply Sorted_inv in Hsort.
            destruct Hsort as (_, Hrel).
            apply HdRel_inv in Hrel.
            progress unfold fst_lt in Hrel; simpl in Hrel.
            apply Qnat_lt in Hrel.
            apply Nat.nle_gt in Hrel.
            exfalso; apply Hrel, Nat.lt_le_incl; assumption.

            eapply IHpts; try eassumption.
             intros iq αi Hpti.
             apply Hnat with (αi := αi).
             simpl in Hpti.
             destruct Hpti as [H| H].
              injection H; intros; subst.
              left; reflexivity.

              right; right; assumption.

             eapply Sorted_minus_2nd; [ idtac | eassumption ].
             intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Fixpoint make_char_lap_of_hl la pow hl :=
  match hl with
  | [] => []
  | [h … hl₁] =>
      let ps := List.nth h la 0%ps in
      let c := order_coeff ps in
      list_pad (h - pow) 0%K [c … make_char_lap_of_hl la (S h) hl₁]
  end.

Definition make_char_pol_of_pts pol j (pts : list (Q * Q)) :=
  make_char_lap_of_hl (al pol) j (List.map (λ pt, nat_num (fst pt)) pts).

Fixpoint coeff_of_hl la i hl :=
  match hl with
  | [] => 0%K
  | [h … hl₁] =>
      if eq_nat_dec i h then order_coeff (List.nth h la 0%ps)
      else coeff_of_hl la i hl₁
  end.

Definition coeff_of_pt pol i (pts : list (Q * Q)) :=
  coeff_of_hl (al pol) i (List.map (λ pt, nat_num (fst pt)) pts).

Theorem make_char_pol_of_pts_eq : ∀ pol pts j,
  make_char_pol R j (List.map (term_of_point pol) pts) =
  make_char_pol_of_pts pol j pts.
Proof.
intros pol pts j.
revert j.
induction pts as [| (h, ah)]; intros; [ reflexivity | simpl ].
rewrite IHpts; reflexivity.
Qed.

Theorem coeff_of_term_pt_eq : ∀ pol pts i,
  coeff_of_term i (List.map (term_of_point pol) pts) =
  coeff_of_pt pol i pts.
Proof.
intros pol pts i.
progress unfold coeff_of_pt; simpl.
revert i.
induction pts as [| (h, ah)]; intros; [ reflexivity | simpl ].
rewrite IHpts; reflexivity.
Qed.

Theorem nth_char_lap_eq_coeff : ∀ i j li la,
  (j + i)%nat ∈ li
  → Sorted Nat.lt li
    → (∀ m : nat, m ∈ li → j ≤ m)
      → (List.nth i (make_char_lap_of_hl la j li) 0 =
         coeff_of_hl la (j + i) li)%K.
Proof.
(* à nettoyer *)
intros i j li la Hjil Hs Hm.
revert i j Hjil Hm.
induction li as [| n]; intros; simpl.
 rewrite match_id; reflexivity.

 destruct Hjil as [H| H].
  subst n.
  rewrite Nat.add_comm, Nat.add_sub; simpl.
  rewrite list_nth_pad_sub, Nat.sub_diag; simpl.
   remember (i + j)%nat as n eqn:Hn .
   destruct (eq_nat_dec n n) as [H| H]; [ reflexivity | idtac ].
   exfalso; apply H; reflexivity.

   reflexivity.

  destruct (eq_nat_dec (j + i) n) as [H₁| H₁].
   rewrite list_nth_pad_sub.
    rewrite <- H₁.
    rewrite Nat.add_comm, Nat.add_sub; simpl.
    rewrite Nat.sub_diag; reflexivity.

    rewrite <- H₁, Nat.add_sub_swap; auto.
    rewrite Nat.sub_diag; reflexivity.

   rewrite list_nth_pad_sub.
    remember (i - (n - j))%nat as p eqn:Hp .
    symmetry in Hp.
    destruct p; simpl.
     assert (n ≤ i + j)%nat as Hnij.
      revert Hs H; clear; intros.
      rewrite Nat.add_comm.
      remember (j + i)%nat as m; clear i j Heqm.
      revert n m Hs H.
      induction li as [| i]; intros; [ contradiction | simpl ].
      apply Sorted_inv in Hs.
      destruct Hs as (Hs, Hrel).
      destruct H as [H| H].
       subst m.
       apply HdRel_inv in Hrel.
       apply Nat.lt_le_incl; assumption.

       apply HdRel_inv in Hrel.
       apply Nat.le_trans with (m := i).
        apply Nat.lt_le_incl; assumption.

        apply IHli; assumption.

      assert (j ≤ n); [ apply Hm; left; reflexivity | exfalso ].
      apply H₁; symmetry.
      rewrite Nat.add_comm.
      apply Nat.le_antisymm; auto.
      apply Nat.sub_0_le.
      rewrite <- Nat_sub_sub_distr; auto.

     apply Nat.add_sub_eq_nz in Hp; [ idtac | intros H₂; discriminate H₂ ].
     assert (j ≤ n) by (apply Hm; left; reflexivity).
     rewrite <- Nat.add_sub_swap in Hp; auto.
     apply Nat.add_cancel_r with (p := j) in Hp.
     eapply Nat.add_le_mono in H0; [ idtac | apply Nat.le_0_l ].
     rewrite Nat.add_0_l, Nat.add_comm in H0.
     rewrite Nat.sub_add in Hp; eauto .
     rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hp.
     rewrite <- Nat.add_comm, <- Hp.
     rewrite IHli; auto.
      eapply Sorted_inv; eassumption.

      rewrite Hp, Nat.add_comm; assumption.

      intros q Hq.
      apply Sorted_inv in Hs.
      destruct Hs as (Hs, Hrel).
      revert Hs Hrel Hq; clear; intros.
      revert n q Hrel Hq.
      induction li as [| i]; intros; [ contradiction | simpl ].
      destruct Hq as [Hq| Hq].
       subst i.
       apply HdRel_inv in Hrel.
       assumption.

       apply Sorted_inv in Hs.
       destruct Hs as (Hs, Hrel2).
       eapply le_trans with (m := i).
        apply HdRel_inv in Hrel; assumption.

        apply Nat.lt_le_incl.
        apply IHli; assumption.

    assert (n ≤ i + j) as HH.
     revert Hs H; clear; intros.
     rewrite Nat.add_comm.
     remember (j + i)%nat as m; clear i j Heqm.
     revert n m Hs H.
     induction li as [| i]; intros; [ contradiction | simpl ].
     apply Sorted_inv in Hs.
     destruct Hs as (Hs, Hrel).
     destruct H as [H| H].
      subst m.
      apply HdRel_inv in Hrel.
      apply Nat.lt_le_incl; assumption.

      apply HdRel_inv in Hrel.
      apply Nat.le_trans with (m := i).
       apply Nat.lt_le_incl; assumption.

       apply IHli; assumption.

     apply Nat.sub_le_mono_r with (p := j) in HH.
     rewrite Nat.add_sub in HH; assumption.
Qed.

Theorem nth_char_lap_eq_0 : ∀ i j li la,
  (j + i)%nat ∉ [j … li]
  → Sorted Nat.lt [j … li]
    → (∀ m : nat, m ∈ li → j ≤ m)
      → List.nth i (make_char_lap_of_hl la j [j … li]) 0%K = 0%K.
Proof.
(* à nettoyer *)
intros i j li la Hjil Hs Hm; simpl.
rewrite Nat.sub_diag; simpl.
destruct i.
 simpl in Hjil.
 apply Decidable.not_or in Hjil.
 destruct Hjil as (Hjji, Hjil).
 rewrite Nat.add_0_r in Hjji.
 exfalso; apply Hjji; reflexivity.

 revert i j Hjil Hs Hm.
 induction li as [| n]; intros; simpl.
  rewrite match_id; reflexivity.

  destruct (le_dec (n - S j) i) as [H₁| H₁].
   rewrite list_nth_pad_sub; [ idtac | assumption ].
   simpl in Hjil.
   apply Decidable.not_or in Hjil.
   destruct Hjil as (Hjji, Hjil).
   remember (i - (n - S j))%nat as p eqn:Hp .
   symmetry in Hp.
   destruct p; simpl.
    assert (n ≤ i + S j)%nat as Hnij by (apply Nat.le_sub_le_add_r; auto).
    assert (S j ≤ n).
     destruct (eq_nat_dec j n) as [H| H].
      subst n.
      apply Sorted_inv in Hs.
      destruct Hs as (_, Hrel).
      apply HdRel_inv in Hrel.
      exfalso; revert Hrel; apply Nat.lt_irrefl.

      assert (j ≤ n) as Hj; [ idtac | fast_omega H Hj ].
      apply Hm; left; reflexivity.

     exfalso; revert Hjil Hp Hnij H; clear; intros.
     apply Decidable.not_or in Hjil.
     destruct Hjil as (Hnji, _).
     apply Hnji; clear Hnji.
     apply Nat.sub_0_le in Hp.
     rewrite Nat.add_comm, Nat.add_succ_l, <- Nat.add_succ_r.
     apply Nat.le_antisymm; auto.
     apply Nat.add_le_mono_r with (p := S j) in Hp.
     rewrite Nat.sub_add in Hp; auto.

    apply IHli.
     simpl.
     intros H.
     destruct H as [H| H]; [ fast_omega H | idtac ].
     apply Decidable.not_or in Hjil.
     destruct Hjil as (Hnji, Hjil).
     replace (n + S p)%nat with (j + S i)%nat in H .
      apply Hjil; assumption.

      rewrite <- Hp.
      rewrite Nat.add_sub_assoc; [ idtac | assumption ].
      rewrite Nat_sub_sub_distr.
       symmetry.
       rewrite <- Nat.add_assoc, Nat.add_comm.
       rewrite Nat.add_sub.
       do 2 rewrite Nat.add_succ_r.
       rewrite Nat.add_comm; reflexivity.

       rename H into H₂.
       destruct (eq_nat_dec j n) as [H| H].
        subst n.
        apply Sorted_inv in Hs.
        destruct Hs as (_, Hrel).
        apply HdRel_inv in Hrel.
        exfalso; revert Hrel; apply Nat.lt_irrefl.

        assert (j ≤ n) as Hj; [ apply Hm; left; reflexivity | idtac ].
        fast_omega H Hj.

     eapply Sorted_inv; eassumption.

     intros m Hml.
     apply Sorted_inv_1 in Hs.
     revert Hs Hml; clear; intros.
     revert n m Hs Hml.
     induction li as [| p]; intros; [ contradiction | simpl ].
     destruct Hml as [Hml| Hml].
      subst p.
      apply Sorted_inv in Hs.
      destruct Hs as (_, Hrel).
      apply HdRel_inv in Hrel.
      apply Nat.lt_le_incl; assumption.

      apply IHli; [ idtac | assumption ].
      eapply Sorted_minus_2nd; [ idtac | eassumption ].
      intros x y z H₁ H₂; eapply Nat.lt_trans; eassumption.

   apply Nat.nle_gt in H₁.
   revert H₁; clear; intros.
   remember (order_coeff (List.nth n la 0%ps)) as v.
   remember (make_char_lap_of_hl la (S n) li) as l.
   remember [v … l] as vl.
   revert H₁; clear; intros.
   remember (n - S j)%nat as k.
   revert H₁; clear; intros.
   revert k vl H₁.
   induction i; intros; simpl.
    destruct k; [ exfalso; revert H₁; apply Nat.lt_irrefl | reflexivity ].

    destruct k; [ exfalso; omega | idtac ].
    apply lt_S_n in H₁; simpl.
    apply IHi; assumption.
Qed.

(* [Walker, p. 101] « Since αh + h.γ₁ = β₁, the first summation reduces to
      x^β₁.(c₁+y₁)^j.Φ((c₁+y₁)^q) = ... ».

   We proof here that
      Σah.(c₁+y₁)^h = (c₁+y₁)^j.Φ((c₁+y₁)^q)
 *)
Theorem sum_ah_c₁y_h_eq : ∀ pol ns pl tl l c₁ j αj,
  newton_segments pol = Some ns
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point pol) pl
      → l = List.map (λ t, power t) tl
        → ini_pt ns = (Qnat j, αj)
          → (ps_pol_summ ps_field l
               (λ h,
                POL [ps_monom (coeff_of_term h tl) 0] *
                POL [ps_monom c₁ 0; 1%ps … []] ^ h) =
             POL [ps_monom c₁ 0; 1%ps … []] ^ j *
             ps_pol_comp (poly_inject_K_in_Kx (Φq pol ns))
               (POL [ps_monom c₁ 0; 1%ps … []]))%pspol.
Proof.
intros pol ns pl tl l c₁ j αj Hns Hpl Htl Hl Hini.
assert (∀ iq αi, (iq, αi) ∈ pl → ∃ i, iq = Qnat i) as Hnat.
 intros iq αi Hip.
 eapply ns_nat; [ eassumption | reflexivity | idtac ].
 subst pl; eassumption.

 remember (List.map (λ pt, nat_num (fst pt)) pl) as li eqn:Hli .
 assert (Sorted Nat.lt li) as Hs.
  remember Hns as Hsort; clear HeqHsort.
  apply ini_oth_fin_pts_sorted in Hsort.
  rewrite <- Hpl in Hsort.
  revert Hsort Hli Hnat; clear; intros.
  subst li.
  induction pl as [| (i, ai)]; simpl; constructor.
   apply Sorted_inv_1 in Hsort.
   apply IHpl; [ assumption | idtac ].
   intros iq αi H.
   eapply Hnat.
   right; eassumption.

   apply Sorted_inv in Hsort.
   destruct Hsort as (_, Hrel).
   revert Hrel Hnat; clear; intros.
   revert i ai Hrel Hnat.
   induction pl as [| (j, aj)]; intros; simpl; constructor.
   apply HdRel_inv in Hrel.
   progress unfold fst_lt in Hrel; simpl in Hrel.
   progress unfold Nat.lt; simpl.
   assert (∃ im : nat, i = Qnat im) as H.
    eapply Hnat; left; reflexivity.

    destruct H as (im, H); subst i; rename im into i.
    assert (∃ jm : nat, j = Qnat jm) as H.
     eapply Hnat; right; left; reflexivity.

     destruct H as (jm, H); subst j; rename jm into j.
     do 2 rewrite nat_num_Qnat.
     apply Qnat_lt; assumption.

  assert (∀ m, m ∈ li → (j ≤ m)%nat) as Hm.
   intros m Hm.
   rewrite Hpl in Hli.
   simpl in Hli.
   rewrite Hini in Hli; simpl in Hli.
   rewrite nat_num_Qnat in Hli; simpl in Hli.
   rewrite Hli in Hs, Hm.
   destruct Hm as [Hm| Hm].
    rewrite Hm; reflexivity.

    apply Sorted_inv in Hs.
    destruct Hs as (Hs, Hrel).
    remember (oth_pts ns ++ [fin_pt ns]) as pl1.
    remember (List.map (λ pt : Q * Q, nat_num (fst pt)) pl1) as jl.
    revert Hs Hrel Hm; clear; intros.
    revert j m Hrel Hm.
    induction jl as [| i]; intros; [ contradiction | simpl ].
    destruct Hm as [H| H].
     subst i.
     apply HdRel_inv in Hrel.
     progress unfold Nat.lt in Hrel.
     apply Nat.lt_le_incl; assumption.

     apply Nat.le_trans with (m := i).
      apply HdRel_inv in Hrel.
      apply Nat.lt_le_incl; assumption.

      apply Sorted_inv in Hs.
      destruct Hs as (Hs, Hrel').
      apply IHjl; assumption.

   remember Hns as Hfin; clear HeqHfin.
   apply exists_fin_pt_nat in Hfin.
   destruct Hfin as (k, (αk, Hfin)).
   progress unfold poly_inject_K_in_Kx.
   progress unfold lap_inject_K_in_Kx.
   remember List.map as lm; simpl.
   rewrite Hini; simpl.
   rewrite nat_num_Qnat; simpl.
   rewrite Nat.sub_diag; simpl.
   progress unfold ps_pol_eq, eq_poly; simpl.
   rewrite fold_char_pol with (αj := αj); rewrite <- Hini, <- Hpl.
   subst lm; simpl.
   rewrite <- Htl.
   remember [ps_monom c₁ 0; 1%ps … []] as la eqn:Hla .
   rewrite lap_compose_compose2.
   progress unfold lap_compose2.
   progress unfold lap_summation.
   rewrite lap_mul_fold_add_distr; simpl.
   rewrite List.map_length.
   subst l.
   erewrite length_char_pol; try eassumption.
   rewrite Htl, List.map_map.
   symmetry.
   rewrite lap_fold_compat_l; [ idtac | rewrite lap_mul_nil_r; reflexivity ].
   rewrite List.map_ext with (g := λ x, nat_num (fst x));
    [ idtac | reflexivity ].
   rewrite fold_right_exists; try eassumption.
    rewrite list_fold_right_seq with (t := j); try reflexivity.
     intros i a b Hab.
     rewrite Hab; reflexivity.

     intros i accu; simpl.
     remember (List.existsb (λ pt, Nat.eqb (j + i) (nat_num (fst pt))) pl) as b.
     rename Heqb into Hb.
     symmetry in Hb.
     destruct b.
      apply lap_add_compat; [ reflexivity | idtac ].
      symmetry; rewrite lap_mul_comm; symmetry.
      rewrite lap_power_add, <- lap_mul_assoc.
      apply lap_mul_compat; [ reflexivity | idtac ].
      rewrite lap_mul_comm.
      apply lap_mul_compat; [ reflexivity | idtac ].
      constructor; [ idtac | reflexivity ].
      apply List.existsb_exists in Hb.
      destruct Hb as ((hq, ah), (Hh, Hjh)); simpl in Hjh.
      remember Hpl as Hpts; clear HeqHpts.
      eapply ns_nat in Hpts; try eassumption.
      destruct Hpts as (h, H); subst hq.
      rewrite nat_num_Qnat in Hjh; simpl in Hjh.
      apply Nat.eqb_eq in Hjh.
      rewrite Hjh.
      rewrite rng_list_map_nth with (A := α) (d := 0%K).
       progress unfold ps_monom, ps_monom; simpl.
       apply mkps_morphism; try reflexivity.
       constructor; intros l; simpl.
       destruct l; [ simpl | reflexivity ].
       rewrite <- Hjh.
       rewrite make_char_pol_of_pts_eq.
       progress unfold make_char_pol_of_pts.
       rewrite coeff_of_term_pt_eq.
       progress unfold coeff_of_pt.
       remember Hns as Hsort; clear HeqHsort.
       apply ini_oth_fin_pts_sorted in Hsort.
       rewrite <- Hpl in Hsort.
       rewrite <- Hli.
       assert ((j + i)%nat ∈ li) as Hjil.
        subst li; rewrite Hjh; simpl.
        revert Hh; clear; intros.
        induction pl as [| (m, am)]; [ contradiction | simpl ].
        destruct Hh as [Hh| Hh].
         injection Hh; clear Hh; intros; subst m am.
         rewrite nat_num_Qnat; left; reflexivity.

         right; apply IHpl; assumption.

        apply nth_char_lap_eq_coeff; assumption.

       rewrite ps_zero_monom_eq; reflexivity.

      rewrite rng_list_map_nth with (A := α) (d := 0%K).
       rewrite <- Htl.
       assert (List.nth i (make_char_pol R j tl) 0%K = 0%K) as Hz.
        rewrite Htl; simpl.
        rewrite make_char_pol_of_pts_eq.
        progress unfold make_char_pol_of_pts.
        remember Hns as Hsort; clear HeqHsort.
        apply ini_oth_fin_pts_sorted in Hsort.
        rewrite <- Hpl in Hsort.
        rewrite <- Hli.
        assert ((j + i)%nat ∉ li) as Hjil.
         subst li.
         revert Hb; clear; intros.
         intros H; revert Hb.
         apply eq_true_false_abs.
         apply List.existsb_exists.
         revert i j H.
         induction pl as [| (m, am)]; intros; [ contradiction | simpl ].
         simpl in H.
         destruct H as [H| H].
          exists (m, am); split; [ left; reflexivity | simpl ].
          rewrite H, Nat.eqb_eq; reflexivity.

          apply IHpl in H.
          destruct H as (x, (Hpl, H)).
          exists x; split; [ right; assumption | assumption ].

         rewrite Hpl in Hli.
         simpl in Hli.
         rewrite Hini in Hli; simpl in Hli.
         rewrite nat_num_Qnat in Hli.
         remember (oth_pts ns ++ [fin_pt ns]) as pl'.
         remember (List.map (λ pt, nat_num (fst pt)) pl') as li'.
         subst li; rename li' into li.
         apply nth_char_lap_eq_0; try assumption.
         intros m Hm2.
         apply Hm; right; assumption.

        rewrite Hz; simpl.
        set (f' := ps_ring K).
        rewrite lap_eq_cons_nil; [ idtac | simpl | reflexivity ].
         rewrite lap_mul_nil_l, lap_mul_nil_r, lap_add_nil_r; reflexivity.

         apply ps_zero_monom_eq.

       rewrite ps_zero_monom_eq; reflexivity.

    intros i a b Hab.
    unfold ps_lap_eq in Hab; unfold ps_lap_eq.
    rewrite Hab; reflexivity.
Qed.

(* to be moved to the right file... *)
Theorem ps_monom_summation_aux : ∀ f b len,
  (ps_monom (summation_aux R b len f) 0 =
   summation_aux (ps_ring K) b len (λ i, ps_monom (f i) 0))%ps.
Proof.
intros f b len.
revert b.
induction len; intros; [ apply ps_zero_monom_eq | simpl ].
rewrite ps_monom_add_l.
apply ps_add_compat_l.
apply IHlen.
Qed.

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

Theorem lap_add_map_ps : ∀ la lb,
  (List.map (λ c, ps_monom c 0) (la + lb)%lap =
   List.map (λ c, ps_monom c 0) la + List.map (λ c, ps_monom c 0) lb)%pslap.
Proof.
intros la lb.
apply lap_add_map; intros a b.
rewrite ps_monom_add_l; reflexivity.
Qed.

Theorem lap_mul_map_ps : ∀ la lb,
  (List.map (λ c, ps_monom c 0) (la * lb)%lap =
   List.map (λ c, ps_monom c 0) la * List.map (λ c, ps_monom c 0) lb)%pslap.
Proof.
intros la lb.
progress unfold ps_lap_eq, ps_lap_mul, lap_mul; simpl.
do 2 rewrite List.map_length.
remember (pred (length la + length lb)) as len.
clear Heqlen.
remember 0%nat as n; clear Heqn.
revert n la lb.
induction len; intros; [ reflexivity | simpl ].
constructor; [ simpl | apply IHlen ].
clear len IHlen; simpl.
unfold summation.
rewrite ps_monom_summation_aux.
apply summation_compat; intros i (_, Hi); simpl.
rewrite ps_monom_mul_l.
rewrite rng_list_map_nth.
 rewrite rng_list_map_nth; [ reflexivity | idtac ].
 rewrite ps_zero_monom_eq; reflexivity.

 rewrite ps_zero_monom_eq; reflexivity.
Qed.

Theorem poly_inject_inj_mul : ∀ P Q,
  (poly_inject_K_in_Kx (P * Q)%pol =
   (poly_inject_K_in_Kx P * poly_inject_K_in_Kx Q))%pspol.
Proof.
intros P Q.
apply lap_mul_map_ps.
Qed.

Theorem Ψ_length : ∀ pol ns j k αj αk c₁ r Ψ,
  newton_segments pol = Some ns
  → ini_pt ns = (Qnat j, αj)
    → fin_pt ns = (Qnat k, αk)
      → r = root_multiplicity acf c₁ (Φq pol ns)
        → Ψ = quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r
          → length (al Ψ) = (S (k - j) - r)%nat.
Proof.
intros pol ns j k αj αk c₁ r Ψ Hns Hini Hfin Hr HΨ.
subst Ψ.
remember S as s; simpl.
rewrite Hini; simpl.
rewrite nat_num_Qnat; simpl.
rewrite Nat.sub_diag; simpl.
rewrite fold_char_pol with (αj := αj).
rewrite <- Hini.
rewrite length_list_quotient_phi_x_sub_c_pow_r.
erewrite length_char_pol; try eassumption; try reflexivity.
subst s; reflexivity.
Qed.

Theorem lap_power_map_ps : ∀ la n,
  (lap_inject_K_in_Kx la ^ n = lap_inject_K_in_Kx (la ^ n)%lap)%pslap.
Proof.
intros la n.
unfold ps_lap_eq, ps_lap_pow.
revert la.
induction n; intros; [ reflexivity | simpl ].
rewrite IHn; symmetry.
apply lap_mul_map_ps.
Qed.

Theorem ps_monom_opp : ∀ c pow,
  (ps_monom (- c)%K pow = - ps_monom c pow)%ps.
Proof.
intros c pow.
progress unfold ps_monom; simpl.
progress unfold ps_opp; simpl.
progress unfold series_opp; simpl.
apply mkps_morphism; try reflexivity.
constructor; intros i; simpl.
destruct (zerop i); [ reflexivity | idtac ].
rewrite rng_opp_0; reflexivity.
Qed.

(* [Walker, p. 101] « Since αh + h.γ₁ = β₁, the first summation reduces to
      (c₁+y₁)^j.Φ((c₁+y₁)^q) = x^β₁.y₁^r.(c₁+y₁)^j.Ψ(c₁+y₁) ».

   We proof here that
      (c₁+y₁)^j.Φ((c₁+y₁)^q) = y₁^r.(c₁+y₁)^j.Ψ(c₁+y₁)
 *)
Theorem phi_c₁y₁_psy : ∀ pol ns pl tl l c₁ r Ψ j αj,
  newton_segments pol = Some ns
  → ac_root (Φq pol ns) = c₁
    → r = root_multiplicity acf c₁ (Φq pol ns)
      → Ψ = quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r
        → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
          → tl = List.map (term_of_point pol) pl
            → l = List.map (λ t, power t) tl
              → ini_pt ns = (Qnat j, αj)
                → (POL [ps_monom c₁ 0; 1%ps … []] ^ j *
                   ps_pol_comp (poly_inject_K_in_Kx (Φq pol ns))
                     (POL [ps_monom c₁ 0; 1%ps … []]) =
                   POL [0%ps; 1%ps … []] ^ r *
                   POL [ps_monom c₁ 0; 1%ps … []] ^ j *
                   ps_pol_comp (poly_inject_K_in_Kx Ψ)
                     (POL [ps_monom c₁ 0; 1%ps … []]))%pspol.
Proof.
intros pol ns pl tl l c₁ r Ψ j αj Hns Hc₁ Hr HΨ Hpl Htl Hl Hini.
remember Hns as Hfin; clear HeqHfin.
apply exists_fin_pt_nat in Hfin.
destruct Hfin as (k, (αk, Hk)).
symmetry.
progress unfold ps_pol_mul.
rewrite poly_mul_comm, poly_mul_assoc, poly_mul_comm.
apply poly_mul_compat; [ reflexivity | idtac ].
rewrite phi_zq_eq_z_sub_c₁_psy; try eassumption.
rewrite poly_inject_inj_mul.
progress unfold eq_poly; simpl.
rewrite <- lap_power_map_ps; simpl.
rewrite lap_compose_mul.
symmetry.
rewrite lap_mul_comm.
apply lap_mul_compat_l.
clear Hr HΨ.
induction r.
 simpl; progress unfold summation; simpl.
 rewrite rng_mul_0_l, rng_add_0_l, rng_add_0_l.
 reflexivity.

 rewrite <- Nat.add_1_r.
 unfold ps_lap_pow.
 do 2 rewrite lap_power_add.
 do 2 rewrite lap_power_1.
 rewrite lap_compose_mul.
 rewrite IHr.
 apply lap_mul_compat_l; simpl.
 progress unfold summation; simpl.
 rewrite rng_mul_0_l, rng_add_0_l, rng_add_0_l.
 rewrite rng_add_0_r, rng_add_0_r, rng_mul_1_r.
 constructor; [ idtac | reflexivity ].
 rewrite ps_mul_1_l, ps_monom_opp, ps_add_opp_r.
 reflexivity.
Qed.

(*
  We therefore have:
     f₁(x,y₁) = y₁^r.(c₁+y₁)^j.Ψ(c₁+y₁) +
                x^(-β₁).[Σ(āh-ah.x^αh).x^(h.γ₁).(c₁+y₁)^h +
                         Σāl.x^(l.γ₁).(c₁+y₁)^l]
*)
Theorem f₁_eq_term_with_Ψ_plus_sum : ∀ pol ns c₁ pl tl j αj l₁ l₂ r Ψ,
  newton_segments pol = Some ns
  → ac_root (Φq pol ns) = c₁
    → r = root_multiplicity acf c₁ (Φq pol ns)
      → Ψ = quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r
        → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
          → tl = List.map (term_of_point pol) pl
            → l₁ = List.map (λ t, power t) tl
              → split_list (List.seq 0 (length (al pol))) l₁ l₂
                → ini_pt ns = (Qnat j, αj)
                  → (next_pol pol (β ns) (γ ns) c₁ =
                     POL [0%ps; 1%ps … []] ^ r *
                     POL [ps_monom c₁ 0; 1%ps … []] ^ j *
                     poly_inject_K_in_Kx Ψ ∘ POL [ps_monom c₁ 0; 1%ps … []] +
                     POL [ps_monom 1%K (- β ns)] *
                     (ps_pol_summ ps_field l₁
                        (λ h,
                         let āh := ps_poly_nth h pol in
                         let ah := ps_monom (coeff_of_term h tl) 0 in
                         let αh := ord_of_pt h pl in
                         POL [((āh - ah * ps_monom 1%K αh) *
                         ps_monom 1%K (Qnat h * γ ns))%ps] *
                         POL [ps_monom c₁ 0; 1%ps … []] ^ h) +
                      ps_pol_summ ps_field l₂
                        (λ l,
                         let āl := ps_poly_nth l pol in
                         POL [(āl * ps_monom 1%K (Qnat l * γ ns))%ps] *
                         POL [ps_monom c₁ 0; 1%ps … []] ^ l)))%pspol.
Proof.
intros pol ns c₁ pl tl j αj l₁ l₂ r Ψ Hns Hc₁ Hr HΨ Hpl Htl Hl Hss Hini.
rewrite f₁_eq_sum_without_x_β₁_plus_sum; try eassumption.
rewrite sum_ah_c₁y_h_eq; try eassumption.
rewrite phi_c₁y₁_psy; try eassumption.
reflexivity.
Qed.

End theorems.
