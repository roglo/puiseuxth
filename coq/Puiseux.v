(* Puiseux.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.
Require Import Sorted.

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
Require Import Ps_add_compat.
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

Definition poly_inject_K_in_Kx α (K : field α) pol :=
  (POL (List.map (λ c, ps_monom K c 0) (al pol)))%pol.

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

Add Parametric Morphism α (K : field α) : (List.map (λ c, ps_monom K c 0))
  with signature lap_eq K ==> lap_eq (ps_field K)
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

Add Parametric Morphism α (K : field α) : (poly_inject_K_in_Kx K)
  with signature eq_poly K ==> eq_poly (ps_field K)
  as poly_inject_k_in_Kx_morph.
Proof.
intros P Q HPQ.
unfold eq_poly; simpl.
rewrite HPQ; reflexivity.
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

Lemma lap_fold_compat_l : ∀ A (f g : A → _) la lb l,
  lap_eq K la lb
  → lap_eq K
      (List.fold_right (λ v accu, lap_add K accu (lap_mul K (f v) (g v)))
         la l)
      (List.fold_right (λ v accu, lap_add K accu (lap_mul K (f v) (g v)))
         lb l).
Proof.
intros A f g la lb l Heq.
induction l; [ assumption | simpl; rewrite IHl; reflexivity ].
Qed.

Lemma lap_power_add : ∀ la i j,
  lap_eq K (lap_power K la (i + j))
    (lap_mul K (lap_power K la i) (lap_power K la j)).
Proof.
intros la i j.
revert j.
induction i; intros; simpl.
 rewrite lap_mul_1_l; reflexivity.

 rewrite IHi, lap_mul_assoc; reflexivity.
Qed.

Lemma fld_list_map_nth : ∀ A n f l (d : A) fd,
  (fd .= K f d)%K
  → (List.nth n (List.map f l) fd .= K f (List.nth n l d))%K.
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
Variable acf : algeb_closed_field α.
Let K := ac_field acf.
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

(*
Let pht := {| coeff := .0 K%K; power := O |}.
*)

Fixpoint coeff_of_term i tl :=
  match tl with
  | [] => .0 K%K
  | [t₁ … tl₁] =>
      if eq_nat_dec i (power t₁) then coeff t₁ else coeff_of_term i tl₁
  end.

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
              let ah := c_x_power K (coeff_of_term h tl) 0 in
              let αh := val_of_pt h pl in
              POL [(ah .* K x_power K (αh + Qnat h * γ₁))%ps] .* Kx
              POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .+ Kx
           poly_summation Kx l
             (λ h,
              let ah := c_x_power K (coeff_of_term h tl) 0 in
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
                let ah := c_x_power K (coeff_of_term h tl) 0 in
                let αh := val_of_pt h pl in
                POL [(ah .* K x_power K (αh + Qnat h * γ₁))%ps] .* Kx
                POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .+ Kx
             POL [x_power K (- β₁)] .* Kx
             (poly_summation Kx l₁
                (λ h,
                 let ah := c_x_power K (coeff_of_term h tl) 0 in
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

Lemma val_is_val_of_pt : ∀ pl h,
  Sorted fst_lt pl
  → (∀ pt, pt ∈ pl → ∃ (h : nat) (αh : Q), pt = (Qnat h, αh))
    → h ∈ List.map (λ x, nofq (fst x)) pl
      → (Qnat h, val_of_pt h pl) ∈ pl.
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
  unfold nofq, Qnat; simpl.
  rewrite Z2Nat.id; [ reflexivity | idtac ].
  apply Nat2Z.is_nonneg.

  exfalso.
  revert Hnat Hsort Hin H; clear; intros.
  revert al h Hnat Hsort Hin H.
  induction pl as [| (m, am)]; intros; [ contradiction | simpl ].
  simpl in Hin.
  destruct Hin as [Hin| Hin].
   subst h.
   apply Sorted_inv_2 in Hsort.
   destruct Hsort as (Hrel, Hsort).
   unfold fst_lt in Hrel; simpl in Hrel.
   rewrite <- H in Hrel.
   unfold Qnat, nofq in Hrel.
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
  unfold nofq, Qnat; simpl.
  rewrite Nat2Z.id; reflexivity.
Qed.

(* Σah.x^(αh+h.γ).(c₁+y₁)^h = Σah.x^β.(c₁+y₁)^h *)
Lemma subst_αh_hγ : ∀ pol ns pl tl l₁ c₁,
  ns ∈ newton_segments K pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point K pol) pl
      → l₁ = List.map (λ t, power t) tl
        → (poly_summation Kx l₁
             (λ h,
              let ah := c_x_power K (coeff_of_term h tl) 0 in
              let αh := val_of_pt h pl in
              POL [(ah .* K x_power K (αh + Qnat h * γ ns))%ps] .* Kx
              POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .= Kx
           poly_summation Kx l₁
             (λ h,
              let ah := c_x_power K (coeff_of_term h tl) 0 in
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

 apply val_is_val_of_pt; assumption.
Qed.

Lemma poly_summation_mul : ∀ l x g₁ g₂,
  (poly_summation Kx l (λ h, POL [(g₁ h .* K x)%ps] .* Kx g₂ h) .= Kx
   POL [x] .* Kx poly_summation Kx l (λ h, POL [g₁ h] .* Kx g₂ h))%pol.
Proof.
intros l x g₁ g₂.
unfold eq_poly; simpl.
unfold lap_summation; simpl.
induction l as [| i]; intros; simpl.
 rewrite lap_mul_nil_r; reflexivity.

 rewrite IHl.
 rewrite lap_mul_add_distr_l.
 simpl.
 apply lap_add_compat; [ reflexivity | simpl ].
 rewrite lap_mul_assoc.
 apply lap_mul_compat; [ idtac | reflexivity ].
 unfold lap_mul; simpl.
 rewrite summation_only_one; simpl.
 rewrite fld_mul_comm; reflexivity.
Qed.

(* Replacing αh + h.γ₁ with β₁, and simplifying the first summation, we get:
     f₁(x,y₁) = Σah.(c₁+y₁)^h +
                x^(-β₁).[Σ(āh-ah.x^αh).x^(h.γ₁).(c₁+y₁)^h +
                         Σāl.x^(l.γ₁).(c₁+y₁)^l]
*)
Theorem f₁_eq_sum_without_x_β₁_plus_sum : ∀ pol ns c₁ pl tl l₁ l₂,
  ns ∈ newton_segments K pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point K pol) pl
      → l₁ = List.map (λ t, power t) tl
        → split_list (List.seq 0 (length (al pol))) l₁ l₂
          → (pol₁ K pol (β ns) (γ ns) c₁ .= Kx
             poly_summation Kx l₁
               (λ h,
                let ah := c_x_power K (coeff_of_term h tl) 0 in
                POL [ah] .* Kx
                POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .+ Kx
             POL [x_power K (- β ns)] .* Kx
             (poly_summation Kx l₁
                (λ h,
                 let ah := c_x_power K (coeff_of_term h tl) 0 in
                 let αh := val_of_pt h pl in
                 POL [((ā K h pol .- K ah .* K x_power K αh) .* K
                       x_power K (Qnat h * γ ns))%ps] .* Kx
                 POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .+ Kx
              poly_summation Kx l₂
                (λ l,
                 POL [(ā K l pol .* K x_power K (Qnat l * γ ns))%ps] .* Kx
                 POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx l)))%pol.
Proof.
intros pol ns c₁ pl tl l₁ l₂ Hns Hpl Htl Hl Hss.
remember Hns as H; clear HeqH.
eapply f₁_eq_sum_α_hγ_to_rest in H; try eassumption.
rewrite H.
apply poly_add_compat; [ idtac | reflexivity ].
rewrite subst_αh_hγ; try eassumption; simpl.
rewrite poly_summation_mul.
rewrite poly_mul_assoc.
symmetry.
rewrite <- poly_mul_1_l in |- * at 1.
apply poly_mul_compat; [ idtac | reflexivity ].
unfold poly_mul; simpl.
unfold eq_poly; simpl.
unfold ps_one; simpl.
unfold lap_mul; simpl.
rewrite summation_only_one; simpl.
unfold x_power; simpl.
constructor; [ idtac | reflexivity ].
unfold ps_monom; simpl.
unfold ps_mul; simpl.
unfold cm; simpl.
rewrite Z.mul_opp_l.
rewrite Z.add_opp_diag_l.
rewrite stretch_series_1, series_mul_1_l.
remember (Qden (β ns) * Qden (β ns))%positive as k.
rewrite ps_adjust_eq with (k := k) (n := O).
unfold adjust_ps; simpl.
rewrite series_shift_0, stretch_series_1.
reflexivity.
Qed.

Lemma lap_summation_compat_r : ∀ A (f : field A) g h la,
  (∀ i, lap_eq f (g i) (h i))
  → lap_eq f (lap_summation f la g) (lap_summation f la h).
Proof.
intros A f g h la Hi.
induction la as [| a]; [ reflexivity | simpl ].
rewrite IHla.
rewrite Hi.
reflexivity.
Qed.

Lemma match_nat_eq_false : ∀ i,
  match i with
  | 0%nat => false
  | S j => Nat.eqb i j
  end = false.
Proof.
intros i.
destruct i; [ reflexivity | idtac ].
induction i; [ reflexivity | idtac ].
remember (S i) as j.
rewrite Heqj in |- * at 2.
assumption.
Qed.

Lemma list_seq_app : ∀ j dj len,
  (dj ≤ len)%nat
  → List.seq j len = List.seq j dj ++ List.seq (j + dj) (len - dj).
Proof.
intros j dj len Hjlen.
revert j dj Hjlen.
induction len; intros.
 simpl.
 apply Nat.le_0_r in Hjlen; subst dj; reflexivity.

 destruct dj; simpl.
  rewrite Nat.add_0_r.
  reflexivity.

  f_equal.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l.
  apply le_S_n in Hjlen.
  erewrite IHlen; [ reflexivity | eassumption ].
Qed.

Lemma fold_nothing : ∀ A j len (f : _ → _ → A) g la,
  (∀ i, j ≤ i → (i < j + len)%nat → g i = false)
  → List.fold_right (λ i accu, if g i then f i accu else accu) la
       (List.seq j len) = la.
Proof.
intros A j len f g la Hg.
revert j la Hg.
induction len; intros; [ reflexivity | simpl ].
rewrite Hg; [ idtac | reflexivity | fast_omega  ].
rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hg.
apply IHlen.
intros i Hji Hij.
apply Hg; [ omega | assumption ].
Qed.

Lemma fold_right_if_compat : ∀ A B f₁ f₂ (g h : A → bool) (la : B) li,
  (∀ i, i ∈ li → g i = h i)
  → List.fold_right (λ i a, if g i then f₁ i a else f₂ i a) la li =
    List.fold_right (λ i a, if h i then f₁ i a else f₂ i a) la li.
Proof.
intros A B f₁ f₂ g h la li Hi.
induction li as [| i]; [ reflexivity | simpl ].
rewrite IHli; [ idtac | intros; apply Hi; right; assumption ].
replace (h i) with (g i) ; [ idtac | apply Hi; left; reflexivity ].
reflexivity.
Qed.

Lemma fold_right_eqb_or : ∀ A j k len f (g : _ → A → A) la,
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

Lemma ns_nat : ∀ pol ns pts,
  ns ∈ newton_segments K pol
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

Lemma fold_right_exists : ∀ pol ns pts j k αj αk f la,
  ns ∈ newton_segments K pol
  → pts = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → ini_pt ns = (Qnat j, αj)
      → fin_pt ns = (Qnat k, αk)
        → (∀ i a b, lap_eq Kx a b → lap_eq Kx (f i a) (f i b))
          → lap_eq Kx
              (List.fold_right f la (List.map (λ pt, nofq (fst pt)) pts))
              (List.fold_right
                 (λ i accu,
                  if List.existsb (λ pt, Nat.eqb i (nofq (fst pt))) pts then
                    f i accu
                  else accu) la
                 (List.seq j (S (k - j)))).
Proof.
(* sûrement nettoyable ; putain, j'en ai chié *)
intros pol ns pts j k αj αk f la Hns Hpl Hini Hfin Hi.
assert (j < k)%nat as Hjk.
 eapply j_lt_k; try eassumption.
  rewrite Hini; unfold nofq, Qnat; simpl; rewrite Nat2Z.id; reflexivity.

  rewrite Hfin; unfold nofq, Qnat; simpl; rewrite Nat2Z.id; reflexivity.

 subst pts; simpl.
 rewrite Hini; simpl.
 unfold nofq, Qnat; simpl.
 rewrite Nat2Z.id; simpl.
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
     apply Nat2Z.inj in H0; subst k; reflexivity.

     simpl.
     assert ((h, αh) ∈ [(h, αh) … pts]) as Hh by (left; reflexivity).
     apply Hnat in Hh.
     destruct Hh as (i, Hh).
     subst h; rename i into h.
     unfold Qnat; simpl; rewrite Nat2Z.id.
     destruct (eq_nat_dec h k) as [H₁| H₁].
      subst h.
      rewrite list_seq_app with (dj := (k - S j)%nat); [ idtac | omega ].
      rewrite List.fold_right_app; simpl.
      replace (S (j + (k - S j)))%nat with k ; [ idtac | fast_omega Hjk ].
      replace (k - j - (k - S j))%nat with 1%nat ; [ simpl | fast_omega Hjk ].
      rewrite Nat.eqb_refl; simpl.
      simpl in Hlast.
      destruct pts as [| pt]; [ simpl | exfalso ].
       rewrite fold_nothing; [ reflexivity | idtac ].
       intros i Hji Hij.
       rewrite orb_false_r.
       apply Nat.eqb_neq.
       intros H; subst i.
       fast_omega Hjk Hij.

       revert Hsort Hlast Hnat; clear; intros.
       apply Sorted_inv_1 in Hsort.
       revert pt Hsort Hlast Hnat.
       induction pts as [| pt₂]; intros.
        simpl in Hlast.
        subst pt.
        apply Sorted_inv in Hsort.
        destruct Hsort as (_, Hrel).
        unfold fst_lt in Hrel; apply HdRel_inv in Hrel.
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
         unfold fst_lt in Hrel; simpl in Hrel.
         unfold Qlt in Hrel; simpl in Hrel.
         do 2 rewrite Z.mul_1_r in Hrel.
         apply Nat2Z.inj_lt in Hrel.
         assumption.

         destruct (eq_nat_dec l k) as [H₂| H₂].
          subst l; reflexivity.

          apply Sorted_inv_1 in Hsort.
          remember [(Qnat l, al) … pts] as p; simpl in Hlast; subst p.
          apply Nat.lt_le_incl.
          eapply IHpts; try eassumption.
           intros; apply Hnat with (αi := αi); right; assumption.

           intros; apply Hjh with (αi := αi); right; assumption.

       rewrite list_seq_app with (dj := (h - S j)%nat); [ idtac | omega ].
       assert (j < h)%nat as Hjh₁.
        apply Hjh with (αi := αh); left; reflexivity.

        replace (S j + (h - S j))%nat with h by omega.
        replace (k - j - (h - S j))%nat with (S (k - h)) by omega.
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
             apply HdRel_inv in Hrel; unfold fst_lt in Hrel; simpl in Hrel.
             unfold Qlt in Hrel; simpl in Hrel.
             do 2 rewrite Z.mul_1_r in Hrel.
             apply Nat2Z.inj_lt; assumption.

             apply Sorted_minus_2nd in Hsort.
              revert Hsort H; clear; intros.
              revert h i αi Hsort H.
              induction pts as [| (l, al)]; [ contradiction | intros ].
              destruct H as [H| H].
               injection H; clear H; intros; subst l al.
               apply Sorted_inv in Hsort.
               destruct Hsort as (_, Hrel).
               apply HdRel_inv in Hrel.
               unfold fst_lt in Hrel; simpl in Hrel.
               unfold Qlt in Hrel; simpl in Hrel.
               do 2 rewrite Z.mul_1_r in Hrel.
               apply Nat2Z.inj_lt; assumption.

               eapply IHpts; [ idtac | eassumption ].
               eapply Sorted_minus_2nd; [ idtac | eassumption ].
               intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

              intros; eapply Qlt_trans; eassumption.

            eapply Sorted_inv_1; eassumption.

          apply Nat.lt_succ_r; reflexivity.

         intros i Hji Hij.
         replace (S j + (h - S j))%nat with h in Hij by omega.
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
           simpl; rewrite Nat2Z.id.
           remember (Nat.eqb i l) as b eqn:Hb .
           symmetry in Hb.
           destruct b; simpl.
            apply Nat.eqb_eq in Hb; subst l.
            apply Sorted_inv in Hsort.
            destruct Hsort as (_, Hrel).
            apply HdRel_inv in Hrel.
            unfold fst_lt in Hrel; simpl in Hrel.
            unfold Qlt in Hrel; simpl in Hrel.
            do 2 rewrite Z.mul_1_r in Hrel.
            apply Nat2Z.inj_lt in Hrel.
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
      let ps := List.nth h la .0 K%ps in
      let c := valuation_coeff K ps in
      list_pad (h - pow) .0 K%K [c … make_char_lap_of_hl la (S h) hl₁]
  end.

Definition make_char_pol_of_pts pol j (pts : list (Q * Q)) :=
  make_char_lap_of_hl (al pol) j (List.map (λ pt, nofq (fst pt)) pts).

Fixpoint coeff_of_hl la i hl :=
  match hl with
  | [] => .0 K%K
  | [h … hl₁] =>
      if eq_nat_dec i h then valuation_coeff K (List.nth h la .0 K%ps)
      else coeff_of_hl la i hl₁
  end.

Definition coeff_of_pt pol i (pts : list (Q * Q)) :=
  coeff_of_hl (al pol) i (List.map (λ pt, nofq (fst pt)) pts).

Lemma make_char_pol_of_pts_eq : ∀ pol pts j,
  make_char_pol K j (List.map (term_of_point K pol) pts) =
  make_char_pol_of_pts pol j pts.
Proof.
intros pol pts j.
revert j.
induction pts as [| (h, ah)]; intros; [ reflexivity | simpl ].
rewrite IHpts; reflexivity.
Qed.

Lemma coeff_of_term_pt_eq : ∀ pol pts i,
  coeff_of_term i (List.map (term_of_point K pol) pts) =
  coeff_of_pt pol i pts.
Proof.
intros pol pts i.
unfold coeff_of_pt; simpl.
revert i.
induction pts as [| (h, ah)]; intros; [ reflexivity | simpl ].
rewrite IHpts; reflexivity.
Qed.

Lemma nth_char_lap_eq_coeff : ∀ i j li la,
  (j + i)%nat ∈ li
  → Sorted Nat.lt li
    → (∀ m : nat, m ∈ li → j ≤ m)
      → (List.nth i (make_char_lap_of_hl la j li) .0 K .= K
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

    fast_omega H₁.

   rewrite list_nth_pad_sub.
    remember (i - (n - j))%nat as p eqn:Hp .
    symmetry in Hp.
    destruct p; simpl.
     assert (n ≤ i + j)%nat as Hnij.
      Focus 2.
      assert (j ≤ n); [ idtac | exfalso; omega ].
      apply Hm; left; reflexivity.

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

     rewrite IHli.
      assert (j ≤ n) by (apply Hm; left; reflexivity).
      replace (S n + p)%nat with (j + i)%nat by omega.
      reflexivity.

      eapply Sorted_inv; eassumption.

      assert (j ≤ n) by (apply Hm; left; reflexivity).
      replace (S n + p)%nat with (j + i)%nat by omega.
      assumption.

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

    assert (n ≤ i + j) as HH; [ idtac | omega ].
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
Qed.

Lemma nth_char_lap_eq_0 : ∀ i j li la,
  (j + i)%nat ∉ [j … li]
  → Sorted Nat.lt [j … li]
    → (∀ m : nat, m ∈ li → j ≤ m)
      → List.nth i (make_char_lap_of_hl la j [j … li]) .0 K%K = .0 K%K.
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
    assert (n ≤ i + S j)%nat as Hnij; [ fast_omega H₁ | idtac ].
    assert (S j ≤ n); [ idtac | exfalso; omega ].
    destruct (eq_nat_dec j n) as [H| H].
     subst n.
     apply Sorted_inv in Hs.
     destruct Hs as (_, Hrel).
     apply HdRel_inv in Hrel.
     exfalso; revert Hrel; apply Nat.lt_irrefl.

     assert (j ≤ n) as Hj; [ idtac | fast_omega H Hj ].
     apply Hm; left; reflexivity.

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
       Focus 2.
       rename H into H₂.
       destruct (eq_nat_dec j n) as [H| H].
        subst n.
        apply Sorted_inv in Hs.
        destruct Hs as (_, Hrel).
        apply HdRel_inv in Hrel.
        exfalso; revert Hrel; apply Nat.lt_irrefl.

        assert (j ≤ n) as Hj; [ apply Hm; left; reflexivity | idtac ].
        fast_omega H Hj.

       symmetry.
       rewrite <- Nat.add_assoc, Nat.add_comm.
       rewrite Nat.add_sub.
       do 2 rewrite Nat.add_succ_r.
       rewrite Nat.add_comm; reflexivity.

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
   remember (valuation_coeff K (List.nth n la .0 K%ps)) as v.
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
  ns ∈ newton_segments K pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point K pol) pl
      → l = List.map (λ t, power t) tl
        → ini_pt ns = (Qnat j, αj)
          → (poly_summation Kx l
               (λ h,
                POL [c_x_power K (coeff_of_term h tl) 0] .* Kx
                POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .= Kx
             POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx j .* Kx
             poly_compose Kx (poly_inject_K_in_Kx K (Φq K pol ns))
               (POL [c_x_power K c₁ 0; .1 K%ps … []]))%pol.
Proof.
intros pol ns pl tl l c₁ j αj Hns Hpl Htl Hl Hini.
assert (∀ iq αi, (iq, αi) ∈ pl → ∃ i, iq = Qnat i) as Hnat.
 intros iq αi Hip.
 eapply ns_nat; [ eassumption | reflexivity | idtac ].
 subst pl; eassumption.

 remember (List.map (λ pt, nofq (fst pt)) pl) as li eqn:Hli .
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
   unfold fst_lt in Hrel; simpl in Hrel.
   unfold Nat.lt; simpl.
   assert (∃ im : nat, i = Qnat im) as H.
    eapply Hnat; left; reflexivity.

    destruct H as (im, H); subst i; rename im into i.
    assert (∃ jm : nat, j = Qnat jm) as H.
     eapply Hnat; right; left; reflexivity.

     destruct H as (jm, H); subst j; rename jm into j.
     do 2 rewrite nofq_Qnat.
     unfold Qlt in Hrel; simpl in Hrel.
     do 2 rewrite Z.mul_1_r in Hrel.
     apply Nat2Z.inj_lt; assumption.

  assert (∀ m, m ∈ li → (j ≤ m)%nat) as Hm.
   intros m Hm.
   rewrite Hpl in Hli.
   simpl in Hli.
   rewrite Hini in Hli; simpl in Hli.
   rewrite nofq_Qnat in Hli; simpl in Hli.
   rewrite Hli in Hs, Hm.
   destruct Hm as [Hm| Hm].
    rewrite Hm; reflexivity.

    apply Sorted_inv in Hs.
    destruct Hs as (Hs, Hrel).
    remember (oth_pts ns ++ [fin_pt ns]) as pl1.
    remember (List.map (λ pt : Q * Q, nofq (fst pt)) pl1) as jl.
    revert Hs Hrel Hm; clear; intros.
    revert j m Hrel Hm.
    induction jl as [| i]; intros; [ contradiction | simpl ].
    destruct Hm as [H| H].
     subst i.
     apply HdRel_inv in Hrel.
     unfold Nat.lt in Hrel.
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
   unfold poly_inject_K_in_Kx.
   remember List.map as lm; simpl.
   rewrite Hini; simpl.
   unfold nofq, Qnat; simpl.
   rewrite Nat2Z.id.
   rewrite Nat.sub_diag; simpl.
   rewrite skipn_pad; simpl.
   unfold eq_poly; simpl.
   rewrite fold_char_pol with (αj := αj); rewrite <- Hini, <- Hpl.
   subst lm; simpl.
   rewrite <- Htl.
   remember [c_x_power K c₁ 0; .1 K%ps … []] as la eqn:Hla .
   rewrite lap_compose_compose2.
   unfold lap_compose2.
   unfold lap_summation.
   rewrite lap_mul_fold_add_distr; simpl.
   rewrite list_length_map.
   subst l.
   erewrite length_char_pol; try eassumption.
   rewrite Htl, List.map_map.
   symmetry.
   rewrite lap_fold_compat_l; [ idtac | rewrite lap_mul_nil_r; reflexivity ].
   rewrite List.map_ext with (g := λ x, nofq (fst x));
    [ idtac | reflexivity ].
   rewrite fold_right_exists; try eassumption.
    rewrite list_fold_right_seq with (t := j); try reflexivity.
     intros i a b Hab.
     rewrite Hab; reflexivity.

     intros i accu; simpl.
     remember (List.existsb (λ pt, Nat.eqb (j + i) (nofq (fst pt))) pl) as b.
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
      unfold nofq, Qnat in Hjh; simpl in Hjh.
      rewrite Nat2Z.id in Hjh.
      apply Nat.eqb_eq in Hjh.
      rewrite Hjh.
      rewrite fld_list_map_nth with (A := α) (d := .0 K%K).
       unfold c_x_power, ps_monom; simpl.
       apply mkps_morphism; try reflexivity.
       constructor; intros l; simpl.
       destruct l; [ simpl | reflexivity ].
       rewrite <- Hjh.
       rewrite make_char_pol_of_pts_eq.
       unfold make_char_pol_of_pts.
       rewrite coeff_of_term_pt_eq.
       unfold coeff_of_pt.
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
         rewrite nofq_Qnat; left; reflexivity.

         right; apply IHpl; assumption.

        apply nth_char_lap_eq_coeff; assumption.

       rewrite ps_zero_monom_eq; reflexivity.

      rewrite fld_list_map_nth with (A := α) (d := .0 K%K).
       rewrite <- Htl.
       assert (List.nth i (make_char_pol K j tl) .0 K%K = .0 K%K) as Hz.
        Focus 2.
        rewrite Hz; simpl.
        rewrite lap_eq_cons_nil; [ idtac | simpl | reflexivity ].
         rewrite lap_mul_nil_l, lap_mul_nil_r, lap_add_nil_r; reflexivity.

         apply ps_zero_monom_eq.

        rewrite Htl; simpl.
        rewrite make_char_pol_of_pts_eq.
        unfold make_char_pol_of_pts.
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
         rewrite nofq_Qnat in Hli.
         remember (oth_pts ns ++ [fin_pt ns]) as pl'.
         remember (List.map (λ pt, nofq (fst pt)) pl') as li'.
         subst li; rename li' into li.
         apply nth_char_lap_eq_0; try assumption.
         intros m Hm2.
         apply Hm; right; assumption.

       rewrite ps_zero_monom_eq; reflexivity.

    intros i a b Hab; rewrite Hab; reflexivity.
Qed.

(* to be moved to the right file... *)
Lemma ps_monom_summation_aux : ∀ f b len,
  (ps_monom K (summation_aux K b len f) 0 .= K
   summation_aux Kx b len (λ i, ps_monom K (f i) 0))%ps.
Proof.
intros f b len.
revert b.
induction len; intros; [ apply ps_zero_monom_eq | simpl ].
rewrite ps_monom_add_l.
apply ps_add_compat_l.
apply IHlen.
Qed.

(* to be moved to the right file... *)
Lemma yyy : ∀ f n,
  (ps_monom K (Σ K (i = 0, n) _ f i) 0 .= K
   Σ Kx (i = 0, n) _ ps_monom K (f i) 0)%ps.
Proof.
intros f n.
bbb.

Lemma lap_inject_inj_mul : ∀ la lb,
   lap_eq Kx (List.map (λ c, ps_monom K c 0) (lap_mul K la lb))
     (lap_mul Kx
        (List.map (λ c, ps_monom K c 0) la)
        (List.map (λ c, ps_monom K c 0) lb)).
Proof.
intros la lb.
unfold lap_mul; simpl.
do 2 rewrite list_length_map.
remember (pred (length la + length lb)) as len.
clear Heqlen.
remember 0%nat as n; clear Heqn.
revert n la lb.
induction len; intros; [ reflexivity | simpl ].
constructor; [ simpl | apply IHlen ].
clear len IHlen.
simpl.
rewrite yyy.
apply summation_compat; intros i (_, Hi).
bbb.

intros la lb.
revert lb.
induction la as [| a]; intros; simpl.
 do 2 rewrite lap_mul_nil_l; reflexivity.
bbb.

Lemma poly_inject_inj_mul : ∀ P Q,
  (poly_inject_K_in_Kx K (P .* K Q) .= Kx
   (poly_inject_K_in_Kx K P .* Kx poly_inject_K_in_Kx K Q))%pol.
Proof.
intros P Q.
apply lap_inject_inj_mul.
Qed.

bbb.

revert lb.
induction la as [| a]; intros; simpl.
 remember (lap_mul K [] lb) as x.
 rewrite lap_mul_nil_l; subst x.
 unfold lap_mul; simpl.
 remember 0%nat as n; clear Heqn.
 remember (pred (length lb)) as len; clear Heqlen.
 revert n.
 induction len; intros; [ reflexivity | simpl ].
 constructor.
  rewrite all_0_summation_0.
   apply ps_zero_monom_eq.

   intros i (_, Hi).
   rewrite match_id, fld_mul_0_l; reflexivity.

  apply IHlen.
bbb.

(* to be moved to the right file *)
Theorem poly_compose_mul_distr_r : ∀ P Q R,
  ((P .* Kx Q) .∘ Kx R .= Kx (P .∘ Kx R) .* Kx (Q .∘ Kx R))%pol.
Proof.
bbb.

(* [Walker, p. 101] « Since αh + h.γ₁ = β₁, the first summation reduces to
      (c₁+y₁)^j.Φ((c₁+y₁)^q) = x^β₁.y₁^r.(c₁+y₁)^j.Ψ(c₁+y₁) ».

   We proof here that
      (c₁+y₁)^j.Φ((c₁+y₁)^q) = y₁^r.(c₁+y₁)^j.Ψ(c₁+y₁)
 *)
Theorem zzz : ∀ pol ns pl tl l c₁ r Ψ j αj,
  ns ∈ newton_segments K pol
  → r = root_multiplicity acf c₁ (Φq K pol ns)
    → Ψ = quotient_phi_x_sub_c_pow_r K (Φq K pol ns) c₁ r
      → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
        → tl = List.map (term_of_point K pol) pl
          → l = List.map (λ t, power t) tl
            → ini_pt ns = (Qnat j, αj)
              → (POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx j .* Kx
                 poly_compose Kx (poly_inject_K_in_Kx K (Φq K pol ns))
                   (POL [c_x_power K c₁ 0; .1 K%ps … []]) .= Kx
                 POL [.0 K%ps; .1 K%ps … []] .^ Kx r .* Kx
                 POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx j .* Kx
                 poly_compose Kx (poly_inject_K_in_Kx K Ψ)
                   (POL [c_x_power K c₁ 0; .1 K%ps … []]))%pol.
Proof.
intros pol ns pl tl l c₁ r Ψ j αj Hns Hr HΨ Hpl Htl Hl Hini.
symmetry.
rewrite poly_mul_comm, poly_mul_assoc, poly_mul_comm.
apply poly_mul_compat; [ reflexivity | idtac ].
symmetry.
subst K.
rewrite phi_zq_eq_z_sub_c₁_psy; try eassumption.
remember (ac_field acf) as K eqn:HK .
rewrite poly_inject_inj_mul.
rewrite poly_compose_mul_distr_r.
rewrite poly_mul_comm.
apply poly_mul_compat; [ reflexivity | idtac ].
bbb.

......

(* [Walker, p. 101] « Since āh = ah.x^αh + ...,

     f₁(x,y₁) = x^(-β₁).Σah.x^(αh+h.γ₁).(c₁+y₁)^h +
                x^(-β₁).[Σ(āh-ah.x^αh).x^(h.γ₁).(c₁+y₁)^h +
                         Σāl.x^(l.γ₁).(c₁+y₁)^l]

.......

   Since αh + h.γ₁ = β₁, the first summation reduces to
      x^β₁.(c₁+y₁)^j.Φ((c₁+y₁)^q = ...
  ».

  We therefore have ...... to be rewritten
     f₁(x,y₁) = (c₁+y₁)^j.Φ((c₁+y₁)^q) +
                x^(-β₁).[Σ(āh-ah.x^αh).x^(h.γ₁).(c₁+y₁)^h +
                         Σāl.x^(l.γ₁).(c₁+y₁)^l]
*)
bbb.
Theorem ......... : ∀ pol ns c₁ pl tl j αj l₁ l₂,
  ns ∈ newton_segments K pol
  → pl = [ini_pt ns … oth_pts ns ++ [fin_pt ns]]
    → tl = List.map (term_of_point K pol) pl
      → l₁ = List.map (λ t, power t) tl
        → split_list (List.seq 0 (length (al pol))) l₁ l₂
          → ini_pt ns = (Qnat j, αj)
            → (pol₁ K pol (β ns) (γ ns) c₁ .= Kx
               POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx j .* Kx
               poly_compose Kx (poly_inject_K_in_Kx K (Φq K pol ns))
                 (POL [c_x_power K c₁ 0; .1 K%ps … []]) .+ Kx
               POL [x_power K (- β ns)] .* Kx
               (poly_summation Kx l₁
                  (λ h,
                   let ah := c_x_power K (coeff_of_term h tl) 0 in
                   let αh := val_of_pt h pl in
                   POL [((ā K h pol .- K ah .* K x_power K αh) .* K
                         x_power K (Qnat h * γ ns))%ps] .* Kx
                   POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx h) .+ Kx
                poly_summation Kx l₂
                  (λ l,
                   POL [(ā K l pol .* K x_power K (Qnat l * γ ns))%ps] .* Kx
                   POL [c_x_power K c₁ 0; .1 K%ps … []] .^ Kx l)))%pol.
Proof.
intros pol ns c₁ pl tl j αj l₁ l₂ Hns Hpl Htl Hl Hss Hini.
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
