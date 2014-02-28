(* Puiseux.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import ConvexHullMisc.
Require Import PolyConvexHull.
Require Import Field.
Require Import Misc.
Require Import Newton.
Require Import Nbar.
Require Import Fsummation.
Require Import Fpolynomial.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_mul.
Require Import Ps_div.
Require Import Puiseux_base.
Require Import CharactPolyn.
Require Import AlgCloCharPol.

Set Implicit Arguments.

(* *)

Definition c_x_power := ps_monom.
Definition x_power α (K : field α) q := (ps_monom K .1 K q)%K.
Definition var_y α (K : field α) := [.0 K; .1 K … []]%K.

(* pol₁(x,y₁) = x^(-β₁).pol(x,x^γ₁.(c₁ + y₁)) *)
Definition lap_pol₁ α (K : field α) pol β₁ γ₁ c₁ :=
  lap_mul (ps_field K) [x_power K (- β₁)]
    (lap_compose (ps_field K) pol
       [c_x_power K c₁ γ₁; x_power K γ₁ … []]).

Definition pol₁ α (K : field α) pol β₁ γ₁ c₁ :=
  (POL (lap_pol₁ K (al pol) β₁ γ₁ c₁))%pol.

(* *)

Definition ā_lap α (K : field α) h la := (List.nth h la .0 K)%ps.
Definition ā α (K : field α) h pol := (ā_lap K h (al pol)).

Definition lap_summation α (f : field α) (li : list nat) g :=
  List.fold_right (λ i accu, lap_add f accu (g i)) [] li.

Definition poly_summation α (f : field α) (li : list nat) g :=
  (POL (lap_summation f li (λ i, al (g i))))%pol.

Inductive split_list α : list α → list α → list α → Prop :=
  | sl_nil : split_list [] [] []
  | sl_cons_l : ∀ x l l₁ l₂,
      split_list l l₁ l₂ → split_list [x … l] [x … l₁] l₂
  | sl_cons_r : ∀ x l l₁ l₂,
      split_list l l₁ l₂ → split_list [x … l] l₁ [x … l₂].

Add Parametric Morphism α (f : field α) : (ps_monom f)
  with signature fld_eq f ==> Qeq ==> eq_ps f
  as ps_monom_qeq_morph.
Proof.
intros a b Hab p q Hpq.
unfold ps_monom; simpl.
rewrite ps_adjust_eq with (n := O) (k := Qden q); simpl.
symmetry.
rewrite ps_adjust_eq with (n := O) (k := Qden p); simpl.
unfold adjust_ps; simpl.
do 2 rewrite Z.sub_0_r.
do 2 rewrite series_shift_0.
rewrite Hpq, Pos.mul_comm.
apply mkps_morphism; try reflexivity.
unfold series_stretch; simpl.
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

Lemma list_fold_right_compat : ∀ α β equal g h (a₀ : α) (l : list β),
  (∀ x y z, equal x y → equal (g z x) (h z y))
  → equal a₀ a₀
    → equal (List.fold_right g a₀ l) (List.fold_right h a₀ l).
Proof.
intros α β equal g h a₀ l Hcomp Heq.
induction l as [| x]; intros; [ assumption | idtac ].
apply Hcomp; assumption.
Qed.

Section on_fields.

Variable α : Type.
Variable K : field α.

Lemma split_summation : ∀ g l l₁ l₂,
  split_list l l₁ l₂
  → (poly_summation K l₁ g .+ K poly_summation K l₂ g .= K
     poly_summation K l g)%pol.
Proof.
intros g l l₁ l₂ Hss.
unfold poly_summation; simpl.
unfold eq_poly; simpl.
revert l₁ l₂ Hss.
induction l as [| n]; intros; simpl.
 inversion Hss; subst; reflexivity.

 inversion Hss; subst; simpl.
  rewrite lap_add_shuffle0.
  rewrite IHl; [ reflexivity | assumption ].

  rewrite <- lap_add_assoc.
  rewrite IHl; [ reflexivity | assumption ].
Qed.

Lemma ps_monom_add_r : ∀ c p q,
 (ps_monom K c (p + q) .= K
  ps_monom K c p .* K ps_monom K .1 K%K q)%ps.
Proof.
intros c p q.
unfold ps_mul; simpl.
unfold cm; simpl.
unfold ps_monom; simpl.
apply mkps_morphism; try reflexivity.
unfold ps_mul; simpl.
unfold cm; simpl.
unfold ps_monom; simpl.
constructor; intros i; simpl.
unfold series_stretch; simpl.
unfold convol_mul; simpl.
destruct i; simpl.
 rewrite summation_only_one; simpl.
 rewrite Nat.mod_0_l; auto; simpl.
 rewrite Nat.mod_0_l; auto; simpl.
 rewrite Nat.div_0_l; auto; simpl.
 rewrite Nat.div_0_l; auto; simpl.
 rewrite fld_mul_1_r; reflexivity.

 rewrite all_0_summation_0; [ reflexivity | simpl ].
 intros j (_, Hj).
 destruct j; simpl.
  rewrite Nat.mod_0_l; auto; simpl.
  rewrite Nat.div_0_l; auto; simpl.
  destruct (zerop (S i mod Pos.to_nat (Qden p))) as [H| H].
   apply Nat.mod_divides in H; auto.
   destruct H as (d, Hd).
   rewrite Nat.mul_comm in Hd; rewrite Hd.
   rewrite Nat.div_mul; auto.
   destruct d; [ discriminate Hd | simpl ].
   rewrite fld_mul_0_r; reflexivity.

   rewrite fld_mul_0_r; reflexivity.

  destruct (zerop (S j mod Pos.to_nat (Qden q))) as [H| H].
   apply Nat.mod_divides in H; auto.
   destruct H as (d, Hd).
   rewrite Nat.mul_comm in Hd; rewrite Hd.
   rewrite Nat.div_mul; auto.
   destruct d; [ discriminate Hd | simpl ].
   rewrite fld_mul_0_l; reflexivity.

   rewrite fld_mul_0_l; reflexivity.
Qed.

Lemma ps_monom_split_mul : ∀ c pow,
  (ps_monom K c pow .= K ps_monom K c 0 .* K ps_monom K .1 K%K pow)%ps.
Proof.
intros c pow.
rewrite <- ps_monom_add_r.
rewrite Qplus_0_l; reflexivity.
Qed.

Lemma lap_power_mul : ∀ la lb n,
  lap_eq K
    (lap_power K (lap_mul K la lb) n)
    (lap_mul K (lap_power K la n) (lap_power K lb n)).
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

Lemma ps_monom_mul_r_pow : ∀ c p n,
  (ps_monom K c (Qnat n * p) .= K
   ps_monom K c 0 .* K ps_monom K .1 K%K p .^ K n)%ps.
Proof.
intros c p n.
induction n; simpl.
 rewrite fld_mul_1_r.
 unfold Qnat; simpl.
 rewrite Qmult_0_l; reflexivity.

 rewrite ps_mul_assoc.
 rewrite fld_mul_shuffle0; simpl.
 rewrite <- IHn.
 assert (Qnat (S n) * p == Qnat n * p + p) as H.
  unfold Qnat; simpl.
  rewrite Zpos_P_of_succ_nat.
  unfold Qmult, Qplus; simpl.
  unfold Qeq.
  simpl.
  rewrite <- Z.mul_add_distr_r.
  rewrite Pos2Z.inj_mul.
  symmetry.
  rewrite <- Z.mul_assoc.
  apply Z.mul_cancel_r.
   simpl.
   apply Pos2Z_ne_0.

   unfold Z.succ; simpl.
   rewrite Z.mul_add_distr_r.
   rewrite Z.mul_1_l; reflexivity.

  rewrite H.
  rewrite ps_monom_add_r.
  reflexivity.
Qed.

Lemma poly_summation_add : ∀ g h l,
  (poly_summation K l g .+ K poly_summation K l h .= K
   poly_summation K l (λ i, g i .+ K h i))%pol.
Proof.
intros g h l.
unfold poly_summation, eq_poly; simpl.
induction l as [| i]; intros; [ reflexivity | simpl ].
do 2 rewrite <- lap_add_assoc.
apply lap_add_compat; [ idtac | reflexivity ].
rewrite lap_add_shuffle0.
apply lap_add_compat; [ assumption | reflexivity ].
Qed.

Lemma lap_eq_list_fold_right : ∀ β g h x (l : list β),
  (∀ i a b, i ∈ l → lap_eq K a b → lap_eq K (g i a) (h i b))
  → lap_eq K (List.fold_right g x l) (List.fold_right h x l).
Proof.
induction l as [| y]; intros; [ reflexivity | simpl ].
apply H; [ left; reflexivity | idtac ].
apply IHl; intros i a b Hi Heq.
apply H; [ right; assumption | assumption ].
Qed.

End on_fields.

Section theorems.

Variable α : Type.
Variable K : field α.
Let Kx := ps_field K.

Lemma lap_f₁_eq_x_min_β₁_comp : ∀ la β₁ γ₁ c₁,
  lap_eq Kx (lap_pol₁ K la β₁ γ₁ c₁)
    (lap_mul Kx [x_power K (- β₁)]
       (lap_compose Kx la
          (lap_mul Kx
             [x_power K γ₁]
             [c_x_power K c₁ 0; .1 K%ps … []]))).
Proof.
intros la β₁ γ₁ c₁.
unfold lap_pol₁.
apply lap_mul_compat; [ reflexivity | idtac ].
apply lap_compose_compat; [ reflexivity | idtac ].
unfold lap_mul; simpl.
unfold summation; simpl.
rewrite fld_mul_0_l.
do 3 rewrite fld_add_0_r.
subst Kx; simpl.
constructor.
 rewrite ps_mul_comm; simpl.
 apply ps_monom_split_mul.

 constructor; [ idtac | reflexivity ].
 rewrite fld_mul_1_r; reflexivity.
Qed.

(* [Walker, p. 100] « f₁(x,y₁) = x^(-β₁).f(x,x^γ₁(c₁+y₁)) » *)
Theorem f₁_eq_x_min_β₁_comp : ∀ pol β₁ γ₁ c₁,
  (pol₁ K pol β₁ γ₁ c₁ .= Kx
   POL [x_power K (- β₁)] .* Kx
   poly_compose Kx pol
     (POL [x_power K γ₁] .* Kx
      POL [c_x_power K c₁ 0; .1 K%ps … []]))%pol.
Proof.
intros pol β₁ γ₁ c₁.
apply lap_f₁_eq_x_min_β₁_comp; reflexivity.
Qed.

(* [Walker, p. 100] «
    f₁(x,y₁) = x^(-β₁).[ā₀ + ā₁x^γ₁(c₁+y₁) + ... + ān.x^(n.γ₁)(c₁+y₁)^n]
  » *)
Theorem f₁_eq_x_min_β₁_comp2 : ∀ pol β₁ γ₁ c₁,
  (pol₁ K pol β₁ γ₁ c₁ .= Kx
   POL [x_power K (- β₁)] .* Kx
   poly_compose2 Kx pol
     (POL [x_power K γ₁] .* Kx
      POL [c_x_power K c₁ 0; .1 K%ps … []]))%pol.
Proof.
intros pol β₁ γ₁ c₁.
rewrite <- poly_compose_compose2.
apply f₁_eq_x_min_β₁_comp; assumption.
Qed.

Theorem f₁_eq_x_min_β₁_summation : ∀ pol β₁ γ₁ c₁,
  (pol₁ K pol β₁ γ₁ c₁ .= Kx
   POL [x_power K (- β₁)] .* Kx
   poly_summation Kx (List.seq 0 (length (al pol)))
     (λ h,
      POL [(ā K h pol .* K x_power K (Qnat h * γ₁))%ps] .* Kx
      POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h))%pol.
Proof.
intros pol β₁ γ₁ c₁.
rewrite f₁_eq_x_min_β₁_comp2.
apply poly_mul_compat; [ reflexivity | idtac ].
unfold poly_compose2; simpl.
unfold lap_compose2, poly_summation; simpl.
unfold lap_summation; simpl.
unfold eq_poly; simpl.
apply list_fold_right_compat; [ idtac | reflexivity ].
intros la lb i Heq.
apply lap_add_compat; [ assumption | idtac ].
unfold ā, ā_lap.
rewrite lap_power_mul.
rewrite lap_mul_assoc.
apply lap_mul_compat; [ idtac | reflexivity ].
clear la lb Heq.
remember (al pol) as la; clear pol Heqla.
revert la.
induction i; intros; simpl.
 subst Kx; rewrite lap_mul_1_r.
 constructor; [ idtac | reflexivity ].
 unfold Qnat; simpl.
 rewrite <- ps_mul_1_r in |- * at 1.
 apply ps_mul_compat_l.
 unfold x_power; simpl.
 rewrite Qmult_0_l; reflexivity.

 destruct la as [| a]; simpl.
  rewrite lap_mul_assoc; simpl.
  rewrite lap_eq_0.
  rewrite lap_mul_nil_l.
  rewrite lap_mul_nil_l.
  constructor; [ idtac | reflexivity ].
  subst Kx; simpl.
  rewrite ps_mul_0_l; reflexivity.

  rewrite lap_mul_assoc.
  rewrite lap_mul_shuffle0.
  rewrite IHi.
  unfold lap_mul; simpl.
  rewrite summation_only_one; simpl.
  constructor; [ idtac | reflexivity ].
  subst Kx; simpl.
  rewrite <- ps_mul_assoc.
  apply ps_mul_compat_l.
  unfold x_power.
  rewrite ps_monom_mul_r_pow; symmetry.
  rewrite ps_monom_mul_r_pow; symmetry.
  rewrite fld_mul_shuffle0; simpl.
  rewrite fld_mul_assoc; simpl.
  reflexivity.
Qed.

(* [Walker, p. 100] «
    f₁(x,y₁) = x^(-β₁)Σāh.x^(h.γ₁).(c₁+y₁)^h + x^(-β₁)Σāl.x^(l.γ₁).(c₁+y₁)^l
  » *)
(* we can split the sum on 0..n into two sub lists l₁, l₂ in any way *)
Theorem f₁_eq_x_min_β₁_summation_split : ∀ pol β₁ γ₁ c₁ l₁ l₂,
  split_list (List.seq 0 (length (al pol))) l₁ l₂
  → (pol₁ K pol β₁ γ₁ c₁ .= Kx
     POL [x_power K (- β₁)] .* Kx
     poly_summation Kx l₁
       (λ h,
        POL [(ā K h pol .* K x_power K (Qnat h * γ₁))%ps] .* Kx
        POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .+ Kx
     POL [x_power K (- β₁)] .* Kx
     poly_summation Kx l₂
       (λ l,
        POL [(ā K l pol .* K x_power K (Qnat l * γ₁))%ps] .* Kx
        POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx l))%pol.
Proof.
intros pol β₁ γ₁ c₁ l₁ l₂ Hss.
rewrite <- poly_mul_add_distr_l.
rewrite split_summation; [ idtac | eassumption ].
apply f₁_eq_x_min_β₁_summation; assumption.
Qed.

Let pht := {| coeff := .0 K%K; power := O |}.

Fixpoint val_of_pt i pl :=
  match pl with
  | [] => 0
  | [(x, y) … pl₁] => if Qeq_dec (Qnat i) x then y else val_of_pt i pl₁
  end.

(* Σāh.x^(hγ₁).(c₁+y₁)^h =
   Σah.x^(αh+hγ₁).(c₁+y₁)^h + Σ(āh-ah.x^αh).x^(hγ₁).(c₁+y₁)^h *)
Lemma summation_split_val : ∀ pol ns γ₁ c₁ pl tl l,
  ns ∈ newton_segments K pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point K pol) pl
      → l = List.map (λ t, power t) tl
        → (poly_summation Kx l
             (λ h,
              POL [(ā K h pol .* K x_power K (Qnat h * γ₁))%ps] .* Kx
              POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .= Kx
           poly_summation Kx l
             (λ h,
              let ah := c_x_power K (coeff (List.nth 0 tl pht)) 0 in
              let αh := val_of_pt h pl in
              POL [(ah .* K x_power K (αh + Qnat h * γ₁))%ps] .* Kx
              POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .+ Kx
           poly_summation Kx l
             (λ h,
              let ah := c_x_power K (coeff (List.nth 0 tl pht)) 0 in
              let αh := val_of_pt h pl in
              POL [((ā K h pol .- K ah .* K x_power K αh) .* K
                    x_power K (Qnat h * γ₁))%ps] .* Kx
              POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h))%pol.
Proof.
intros pol ns γ₁ c₁ pl tl l Hns Hpl Htl Hl.
rewrite poly_summation_add; simpl.
unfold eq_poly; simpl.
unfold lap_summation; simpl.
apply lap_eq_list_fold_right; intros i a b Hi Heq.
apply lap_add_compat; [ assumption | simpl ].
rewrite <- lap_mul_add_distr_r; simpl.
apply lap_mul_compat; [ idtac | reflexivity ].
constructor; [ simpl | reflexivity ].
unfold x_power.
rewrite ps_monom_add_r.
rewrite fld_mul_assoc.
rewrite fld_mul_add_distr_r.
subst Kx; simpl.
rewrite fld_mul_opp_l; simpl.
rewrite fld_add_assoc; simpl.
rewrite fld_add_comm; simpl.
rewrite fld_add_assoc; simpl.
rewrite fld_add_opp_l, fld_add_0_l; reflexivity.
Qed.

(* [Walker, p. 101] « Since āh = ah.x^αh + ...,

     f₁(x,y₁) = x^(-β₁).Σah.x^(αh+h.γ₁).(c₁+y₁)^h +
                x^(-β₁).[Σ(āh-ah.x^αh).x^(h.γ₁).(c₁+y₁)^h +
                         Σāl.x^(l.γ₁).(c₁+y₁)^l]
   » *)
Theorem f₁_eq_sum_α_hγ_to_rest : ∀ pol ns β₁ γ₁ c₁ pl tl l₁ l₂,
  ns ∈ newton_segments K pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point K pol) pl
      → l₁ = List.map (λ t, power t) tl
        → split_list (List.seq 0 (length (al pol))) l₁ l₂
          → (pol₁ K pol β₁ γ₁ c₁ .= Kx
             POL [x_power K (- β₁)] .* Kx
             poly_summation Kx l₁
               (λ h,
                let ah := c_x_power K (coeff (List.nth 0 tl pht)) 0 in
                let αh := val_of_pt h pl in
                POL [(ah .* K x_power K (αh + Qnat h * γ₁))%ps] .* Kx
                POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .+ Kx
             POL [x_power K (- β₁)] .* Kx
             (poly_summation Kx l₁
                (λ h,
                 let ah := c_x_power K (coeff (List.nth 0 tl pht)) 0 in
                 let αh := val_of_pt h pl in
                 POL [((ā K h pol .- K ah .* K x_power K αh) .* K
                       x_power K (Qnat h * γ₁))%ps] .* Kx
                 POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .+ Kx
              poly_summation Kx l₂
                (λ l,
                 POL [(ā K l pol .* K x_power K (Qnat l * γ₁))%ps] .* Kx
                 POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx l)))%pol.
Proof.
intros pol ns β₁ γ₁ c₁ pl tl l₁ l₂ Hns Hpl Htl Hl Hss.
rewrite poly_mul_add_distr_l.
rewrite <- poly_add_assoc.
rewrite <- poly_mul_add_distr_l.
rewrite <- summation_split_val; try eassumption.
apply f₁_eq_x_min_β₁_summation_split; assumption.
Qed.

Lemma val_of_pt_app_comm : ∀ pol ns h,
  ns ∈ newton_segments K pol
  → val_of_pt h (oth_pts ns ++ [fin_pt ns]) =
    val_of_pt h [fin_pt ns … oth_pts ns].
Proof.
(* à nettoyer *)
intros pol ns h Hns.
apply oth_fin_pts_sorted in Hns.
remember (oth_pts ns) as pts; clear Heqpts.
induction pts as [| pt]; intros; [ reflexivity | simpl ].
destruct pt as (l, al); simpl.
destruct (Qeq_dec (Qnat h) l) as [H₁| H₁]; simpl.
 destruct (fin_pt ns) as (k, ak); simpl.
 simpl in Hns.
 destruct (Qeq_dec (Qnat h) k) as [H₂| ]; [ idtac | reflexivity ].
 rewrite H₁ in H₂.
 apply Sorted.Sorted_inv in Hns.
 destruct Hns as (Hsort, Hrel).
 remember Hsort as Hval; clear HeqHval.
 apply IHpts in Hval.
 revert Hsort Hrel Hval H₂; clear; intros; exfalso.
 revert l al k ak Hrel H₂ Hsort Hval.
 induction pts as [| (m, am)]; intros; simpl.
  simpl in Hrel.
  inversion Hrel; subst.
  unfold fst_lt in H0; simpl in H0.
  rewrite H₂ in H0.
  revert H0; apply Qlt_irrefl.

  simpl in Hrel.
  inversion Hrel; subst.
  unfold fst_lt in H0; simpl in H0.
  eapply Sorted_trans_app in Hsort; [ idtac | idtac | left; reflexivity ].
   unfold fst_lt in Hsort; simpl in Hsort.
   eapply Qlt_trans in Hsort; [ idtac | eassumption ].
   rewrite H₂ in Hsort.
   revert Hsort; apply Qlt_irrefl.

   intros; eapply Qlt_trans; eassumption.

 destruct (fin_pt ns) as (k, ak).
 destruct (Qeq_dec (Qnat h) k) as [H₂| H₂].
  rewrite IHpts.
   simpl.
   destruct (Qeq_dec (Qnat h) k) as [| H₃]; [ reflexivity | idtac ].
   exfalso; apply H₃; assumption.

   simpl in Hns.
   apply Sorted_inv_1 in Hns; assumption.

  rewrite IHpts.
   simpl.
   destruct (Qeq_dec (Qnat h) k) as [H₃| H₃].
    exfalso; apply H₂; assumption.

    reflexivity.

   eapply Sorted_inv_1; eassumption.
Qed.

(* Σah.x^(αh+h.γ).(c₁+y₁)^h = Σah.x^β.(c₁+y₁)^h *)
Lemma zzz : ∀ pol ns pl tl l₁ c₁,
  ns ∈ newton_segments K pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point K pol) pl
      → l₁ = List.map (λ t, power t) tl
        → (poly_summation Kx l₁
             (λ h,
              let ah := c_x_power K (coeff (List.nth 0 tl pht)) 0 in
              let αh := val_of_pt h pl in
              POL [(ah .* K x_power K (αh + Qnat h * γ ns))%ps] .* Kx
              POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .= Kx
           poly_summation Kx l₁
             (λ h,
              let ah := c_x_power K (coeff (List.nth 0 tl pht)) 0 in
              POL [(ah .* K x_power K (β ns))%ps] .* Kx
              POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h))%pol.
Proof.
intros pol ns pl tl l₁ c₁ Hns Hpl Htl Hl.
unfold eq_poly; simpl.
unfold lap_summation; simpl.
apply lap_eq_list_fold_right.
intros h a b Hh Heq.
apply lap_add_compat; [ assumption | simpl ].
apply lap_mul_compat; [ simpl | reflexivity ].
constructor; [ idtac | reflexivity ].
apply fld_mul_compat; [ reflexivity | simpl ].
unfold x_power; simpl.
rewrite points_in_any_newton_segment; [ reflexivity | eassumption | idtac ].
remember Hns as Hini; clear HeqHini.
remember Hns as Hfin; clear HeqHfin.
apply exists_ini_pt_nat in Hini.
apply exists_fin_pt_nat in Hfin.
destruct Hini as (j, (αj, Hini)).
destruct Hfin as (k, (αk, Hfin)).
rewrite Hl, Htl, Hpl in Hh; simpl in Hh.
destruct Hh as [Hh| Hh].
 left; subst h; simpl.
 rewrite Hini; simpl.
 unfold nofq, Qnat; simpl.
 rewrite Nat2Z.id.
 subst pl; simpl.
 rewrite Hini; simpl.
 destruct (Qeq_dec (Qnat j) (Qnat j)) as [| H]; [ reflexivity | idtac ].
 exfalso; apply H; reflexivity.

 rewrite List.map_app in Hh.
 rewrite List.map_app in Hh.
 rewrite List.map_map in Hh; simpl in Hh.
 simpl in Hh.
 apply List.in_app_or in Hh.
 destruct Hh as [Hh| Hh].
  right; right.
  apply List.in_map_iff in Hh.
  destruct Hh as (x, (Hhx, Hx)).
  subst h.
  destruct x as (xq, αx); simpl.
  remember Hns as Hhx; clear HeqHhx.
  eapply exists_oth_pt_nat in Hhx; [ idtac | eassumption ].
  destruct Hhx as (h, (αh, Hhx)).
  injection Hhx; clear Hhx; intros; subst xq αx; simpl.
  unfold nofq; simpl.
  rewrite Nat2Z.id; simpl.
  rewrite Hpl, Hini; simpl.
  destruct (Qeq_dec (Qnat h) (Qnat j)) as [H| H].
   symmetry in Hini.
   eapply jq_lt_hq in Hns; try eassumption.
   rewrite H in Hns.
   exfalso; revert Hns; apply Qlt_irrefl.

   erewrite val_of_pt_app_comm; [ idtac | eassumption ].
   simpl.
   rewrite Hfin; simpl.
   destruct (Qeq_dec (Qnat h) (Qnat k)) as [H₁| H₁].
    symmetry in Hfin.
    eapply hq_lt_kq in Hns; try eassumption.
    rewrite H₁ in Hns.
    exfalso; revert Hns; apply Qlt_irrefl.

    subst pl tl l₁.
    apply List.in_split in Hx.
    destruct Hx as (l₁, (l₂, Hx)).
    clear H H₁.
    revert Hns Hx; clear; intros.
    apply oth_fin_pts_sorted in Hns.
    apply Sorted_app in Hns.
    destruct Hns as (Hsort, _).
    rewrite Hx in Hsort.
    rewrite Hx; simpl.
    clear Hx.
    induction l₁ as [| (l, al)]; simpl.
     destruct (Qeq_dec (Qnat h) (Qnat h)) as [H₁| H₁].
      left; reflexivity.

      exfalso; apply H₁; reflexivity.

     destruct (Qeq_dec (Qnat h) l) as [H₁| H₁].
      right.
      apply List.in_or_app.
      right; left.
      simpl in Hsort.
      revert Hsort H₁; clear; intros; exfalso.
      induction l₁ as [| (m, am)].
       simpl in Hsort.
       apply Sorted_inv_2 in Hsort.
       destruct Hsort as (Hsort, _).
       unfold fst_lt in Hsort; simpl in Hsort.
       rewrite H₁ in Hsort.
       revert Hsort; apply Qlt_irrefl.

       apply IHl₁.
       simpl in Hsort.
       eapply Sorted_minus_2nd; [ idtac | eassumption ].
       intros; eapply Qlt_trans; eassumption.

      right.
      apply List.in_or_app.
      right; left.
bbb.

(* old stuff; to be used later perhaps *)

(*
Definition zero_is_root (pol : polynomial (puiseux_series α)) :=
  match al pol with
  | [] => false
  | [ps … _] =>
      match ps with
      | NonZero nz =>
          match series_head (f_eq f (zero f)) 0 (nz_terms nz) with
          | Some _ => false
          | None => true
          end
      | Zero => true
      end
  end.

Definition pol_mul_x_power_minus p pol :=
  ps_pol_mul {| al := []; an := ps_monom (one f) (Qopp p) |} pol.

Definition puiseux_step psumo (pol : polynomial (puiseux_series α)) :=
  let nsl₁ := newton_segments f pol in
  let (nsl, psum) :=
    match psumo with
    | Some psum => (List.filter (λ ns, negb (Qle_bool (γ ns) 0)) nsl₁, psum)
    | None => (nsl₁, 0)
    end
  in
  match nsl with
  | [] => None
  | [ns … _] =>
      let cpol := characteristic_polynomial f pol ns in
      let (c, r) := ac_root acf cpol in
      let pol₁ := pol₁ pol (β ns) (γ ns) c in
      let p := Qplus psum (γ ns) in
      Some ({| coeff := c; power := p |}, pol₁)
  end.

CoInductive coseries α :=
  | Cterm : α → coseries α → coseries α
  | Cend : coseries α.

CoFixpoint puiseux_loop psumo (pol : polynomial (puiseux_series α)) :=
  match puiseux_step psumo pol with
  | Some (t, pol₁) =>
      Cterm t
        (if zero_is_root pol₁ then Cend _
         else puiseux_loop (Some (power t)) pol₁)
  | None =>
      Cend _
  end.

bbb.

Lemma series_pad_left_0 : ∀ s, series_pad_left f 0 s ≃ s.
Proof.
intros s.
constructor.
 intros i.
 unfold series_pad_left; simpl.
 destruct (Nbar.lt_dec (nfin i) 0) as [Hlt| Hge].
  apply Nbar.nlt_0_r in Hlt; contradiction.

  rewrite Nat.sub_0_r; reflexivity.

 simpl; rewrite Nbar.add_0_r; reflexivity.
Qed.

Add Parametric Morphism : (series_pad_left f) with 
signature eq ==> eq_series f ==> eq_series f as series_pad_morph.
Proof.
intros n s₁ s₂ H.
constructor; simpl.
 intros i.
 destruct (lt_dec i n); [ reflexivity | idtac ].
 inversion H; apply H0.

 inversion H; rewrite H1; reflexivity.
Qed.

(* *)

Lemma cpol_degree : ∀ (pol : puis_ser_pol α) cpol ns,
  ns ∈ newton_segments f pol
  → cpol = characteristic_polynomial f pol ns
    → degree cpol ≥ 1.
Proof.
intros pol cpol ns Hns Hpol.
subst cpol.
unfold characteristic_polynomial, degree; simpl.
remember (nofq (fst (ini_pt ns))) as j.
remember (nofq (fst (fin_pt ns))) as k.
remember (k - j)%nat as kj.
destruct kj; simpl.
 eapply j_lt_k with (j := j) in Hns; try eassumption.
 apply NPeano.Nat.sub_gt in Hns.
 symmetry in Heqkj; contradiction.

 rewrite minus_diag; simpl.
 apply le_n_S, le_0_n.
Qed.

Lemma exists_root : ∀ (pol : puis_ser_pol α) cpol ns,
  ns ∈ newton_segments f pol
  → cpol = characteristic_polynomial f pol ns
    → ∃ c, apply_polynomial f cpol c = zero f.
Proof.
intros pol cpol ns Hdeg Hpol.
eapply cpol_degree in Hdeg; [ idtac | eassumption ].
remember (ac_root acf cpol) as r.
destruct r as (c, r).
exists c.
rewrite surjective_pairing in Heqr.
injection Heqr; clear Heqr; intros; subst c.
apply (ac_prop acf cpol Hdeg).
Qed.

(* *)

Lemma jh_oppsl_eq_p_nq : ∀ pol ns j αj k αk h αh m,
  ns ∈ newton_segments f pol
  → (j, αj) = ini_pt ns
    → (k, αk) = fin_pt ns
      → (h, αh) ∈ oth_pts ns
        → m = series_list_com_den (al pol ++ [an pol])
          → ∃ p q,
            (αj - αh) / (h - j) == p # (m * q) ∧
            (αj - αk) / (k - j) == p # (m * q) ∧
            Z.gcd p (' q) = 1%Z.
Proof.
intros pol ns j αj k αk h αh m Hns Hj Hk Hh Hm.
eapply gamma_eq_p_nq in Hm; [ idtac | eassumption ].
destruct Hm as (p, (q, H)).
exists p, q.
destruct H as (Hgamma, Hgcd).
split.
 setoid_rewrite  <- gamma_value_jh; eassumption.

 split; [ idtac | assumption ].
 setoid_rewrite  <- gamma_value_jk; try eassumption.
Qed.

Lemma list_pad_app : ∀ n v cl,
  lap_eq (f_eq f) (list_pad n v cl) (list_pad n v [] ++ cl).
Proof.
intros n v cl.
revert v cl.
induction n; intros; simpl.
 apply lap_eq_refl.

 constructor; [ reflexivity | apply IHn ].
Qed.

Lemma empty_padded : ∀ n v c,
  c ∈ list_pad n v []
  → f_eq f c v.
Proof.
intros n v c H.
induction n; [ contradiction | idtac ].
destruct H as [H| H].
 subst v; reflexivity.

 apply IHn, H.
Qed.

Lemma padded : ∀ n v c cl,
  list_pad n v [] = [c … cl]
  → f_eq f c v.
Proof.
intros n v c cl H.
destruct n; [ discriminate H | simpl in H ].
injection H; clear H; intros; subst c cl.
reflexivity.
Qed.

Lemma list_nth_pad_ge : ∀ i s (v : α) cl d,
  (s ≤ i)%nat
  → List.nth i (list_pad s v cl) d = List.nth (i - s) cl d.
Proof.
intros i s v cl d Hsi.
symmetry.
rewrite <- list_nth_plus_pad with (s := s) (v := v).
f_equal.
rewrite plus_comm.
symmetry.
apply le_plus_minus; assumption.
Qed.

Lemma make_char_pol_S : ∀ pow t tl k,
  (pow < power t)%nat
  → make_char_pol f pow [t … tl] k =
    [zero f … make_char_pol f (S pow) [t … tl] k].
Proof.
intros pow t tl k Hpow.
simpl.
rewrite <- Nat.sub_succ.
rewrite <- minus_Sn_m; [ reflexivity | assumption ].
Qed.

Lemma nth_S_pad_S : ∀ i n v tl (d : α),
  List.nth (S i) (list_pad (S n) v tl) d =
  List.nth i (list_pad n v tl) d.
Proof. reflexivity. Qed.

Lemma list_pad_length : ∀ n (v : α) tl,
  List.length (list_pad n v tl) = (n + List.length tl)%nat.
Proof.
intros n v tl.
induction n; [ reflexivity | simpl; rewrite IHn; reflexivity ].
Qed.

Lemma nth_minus_char_pol_plus_nil : ∀ i j s k d,
  s ≤ i
  → j + s ≤ k
    → List.nth (i - s) (make_char_pol f (j + s) [] k) d =
      List.nth i (make_char_pol f j [] k) d.
Proof.
intros i j s k d Hsi Hjsk.
revert i j k d Hsi Hjsk.
induction s; intros.
 rewrite plus_0_r, Nat.sub_0_r; reflexivity.

 symmetry.
 rewrite <- IHs.
  destruct i.
   exfalso; revert Hsi; apply le_Sn_0.

   apply le_S_n in Hsi.
   rewrite Nat.sub_succ.
   rewrite <- minus_Sn_m; [ idtac | assumption ].
   rewrite <- plus_n_Sm.
   simpl.
   remember (S (i - s)) as x.
   rewrite <- Nat.sub_succ; subst x.
   rewrite <- minus_Sn_m; [ apply nth_S_pad_S | idtac ].
   rewrite plus_n_Sm; assumption.

  apply Nat.lt_le_incl; assumption.

  rewrite <- plus_n_Sm in Hjsk.
  apply Nat.lt_le_incl; assumption.
Qed.

(* *)

Definition abar (pol : polynomial (puiseux_series α)) h :=
  List.nth h (al pol) (an pol).

Definition ps_pol_add := pol_add (add ps_f).
Definition ps_pol_mul := pol_mul (zero ps_f) (add ps_f) (mul ps_f).

Fixpoint ps_pol_power pol n :=
  match n with
  | O => {| al := []; an := one ps_f |}
  | S n₁ => ps_pol_mul pol (ps_pol_power pol n₁)
  end.

Lemma zzz : ∀ pol pts ns cpol c₁ r₁,
  pts = points_of_ps_polynom f pol
  → ns ∈ newton_segments f pol
    → cpol = characteristic_polynomial f pol ns
      → ac_root acf cpol = (c₁, r₁)
        → pol₁ f pol (β ns) (γ ns) c₁
          = pol_mul_x_power_minus f (β ns)
              (List.fold_right
                 (λ ips accu,
                    ps_pol_add
                      (ps_pol_mul
                         {| al := [];
                            an :=
                              ps_mul f (snd ips)
                                (x_power f (Qnat (fst ips) * γ ns)%Q) |}
                      (ps_pol_power
                         {| al := [ps_const c₁]; an := ps_one f |}
                         (fst ips)))
                      accu)
                 {| al := []; an := ps_zero _ |}
                 (power_list O (al pol) (an pol))).
Proof.
intros pol pts ns cpol c₁ r₁ Hpts Hns Hcpol Hcr.
unfold poly_eq; simpl.
unfold pol₁.
unfold apply_poly_with_ps_poly, apply_poly.
unfold ps_one, abar.
unfold newton_segments in Hns.
rewrite <- Hpts in Hns.
unfold points_of_ps_polynom in Hpts.
unfold characteristic_polynomial, term_of_point in Hcpol.
simpl in Hcpol.
remember (an pol) as cn; clear Heqcn.
remember (al pol) as cl; clear Heqcl.
unfold nofq in Hcpol.
clear pol cpol Hcpol Hcr r₁.
unfold ps_pol_mul, ps_f; simpl.
unfold ps_pol_add.
remember 0%nat as n; clear Heqn.
revert pts ns c₁ cn n Hpts Hns.
induction cl as [| c]; intros.
 simpl.
 unfold pol_add; simpl.
 unfold pol_mul; simpl.
 destruct n.
  simpl.
(*
  rewrite andb_true_r.
*)
  unfold x_power; simpl.
  Focus 1.
bbb.
*)

End field.
