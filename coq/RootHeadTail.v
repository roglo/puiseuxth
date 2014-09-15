(* RootHeadTail.v *)

Require Import Utf8 QArith NPeano Sorting.

Require Import Misc.
Require Import SlopeMisc.
Require Import Slope_base.
Require Import Qbar.
Require Import Nbar.
Require Import Field.
Require Import Fpolynomial.
Require Import Fsummation.
Require Import Newton.
Require Import ConvexHullMisc.
Require Import ConvexHull.
Require Import PolyConvexHull.
Require Import NotInSegment.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_mul.
Require Import Ps_div.
Require Import PSpolynomial.
Require Import Puiseux_base.
Require Import AlgCloCharPol.
Require Import CharactPolyn.
Require Import F1Eq.
Require Import PosOrder.
Require Import F1Prop.
Require Import InK1m.
Require Import Q_field.

Set Implicit Arguments.

Definition phony_ns :=
  {| ini_pt := (0, 0); fin_pt := (0, 0); oth_pts := [] |}.

Fixpoint nth_pol α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n pol ns :=
  match n with
  | 0%nat => pol
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_pol n₁ pol₁ ns₁
  end.

Fixpoint nth_ns α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n pol ns :=
  match n with
  | 0%nat => ns
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_ns n₁ pol₁ ns₁
  end.

Fixpoint nth_c α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n pol ns :=
  match n with
  | 0%nat => ac_root (Φq pol ns)
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_c n₁ pol₁ ns₁
  end.

Fixpoint nth_γ α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n pol ns :=
  match n with
  | 0%nat => γ ns
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_γ n₁ pol₁ ns₁
  end.

Fixpoint nth_r α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n pol ns :=
  match n with
  | 0%nat => root_multiplicity acf (ac_root (Φq pol ns)) (Φq pol ns)
  | S n₁ =>
      let c₁ := ac_root (Φq pol ns) in
      let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
      let ns₁ := List.hd phony_ns (newton_segments pol₁) in
      nth_r n₁ pol₁ ns₁
  end.

Definition next_pow pow ns₁ m :=
  let n := (γ ns₁ * inject_Z ('m)) in
  (pow + Z.to_nat (Qnum n / ' Qden n))%nat.

Fixpoint find_coeff α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} max_iter npow m pol ns i :=
  match max_iter with
  | 0%nat => 0%K
  | S mx =>
      if ps_zerop _ (ps_poly_nth 0 pol) then 0%K
      else
        match Nat.compare npow i with
        | Eq => ac_root (Φq pol ns)
        | Lt =>
            let c₁ := ac_root (Φq pol ns) in
            let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
            let ns₁ := List.hd phony_ns (newton_segments pol₁) in
            let npow₁ := next_pow npow ns₁ m in
            find_coeff mx npow₁ m pol₁ ns₁ i
        | Gt => 0%K
        end
  end.

Definition root_tail_series_from_cγ_list α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} m pol ns i :=
  find_coeff (S i) 0%nat m pol ns i.

Definition root_tail_from_cγ_list α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} m pol ns :=
  {| ps_terms := {| terms := root_tail_series_from_cγ_list m pol ns |};
     ps_ordnum := Qnum (γ ns) * ' m / ' Qden (γ ns);
     ps_polord := m |}.

Definition γ_sum α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} b n pol ns :=
  let qr := Q_ring in
  Σ (i = 0, n), nth_γ (b + i) pol ns.

Fixpoint root_head_from_cγ_list α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} pol ns b n i :=
  (ps_monom (nth_c (b + i) pol ns) (γ_sum b i pol ns) +
   match n with
   | O => 0%ps
   | S n₁ =>
       if ps_zerop R (ps_poly_nth 0 (nth_pol (b + S i) pol ns)) then 0%ps
       else root_head_from_cγ_list pol ns b n₁ (S i)
   end)%ps.

Fixpoint zerop_1st_n_const_coeff α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} n pol ns :=
  if ps_zerop _ (ps_poly_nth 0 pol) then true
  else
    match n with
    | O => false
    | S n₁ =>
        let c₁ := ac_root (Φq pol ns) in
        let pol₁ := next_pol pol (β ns) (γ ns) c₁ in
        let ns₁ := List.hd phony_ns (newton_segments pol₁) in
        zerop_1st_n_const_coeff n₁ pol₁ ns₁
    end.

(* Σ _(i=0,n).c_{b+i} x^Σ_(j=0,i) γ_{b+j} *)
Definition root_head α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  b n pol ns :=
  if zerop_1st_n_const_coeff b pol ns then 0%ps
  else root_head_from_cγ_list pol ns b n 0.

(* Σ _(i=n+1,∞).c_i x^Σ_(j=n+1,∞) γ_j *)
Definition root_tail α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  m n pol ns :=
  if zerop_1st_n_const_coeff n pol ns then 0%ps
  else root_tail_from_cγ_list m (nth_pol n pol ns) (nth_ns n pol ns).

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Theorem fold_γ_sum : ∀ b n pol ns,
  let qr := Q_ring in
  Σ (i = 0, n), nth_γ (b + i) pol ns = γ_sum b n pol ns.
Proof. reflexivity. Qed.

(* *)

(* f₁(x,y₁) = 0 => f(x,c₁.x^γ+x^γ.y₁) = 0 *)
Theorem f₁_root_f_root : ∀ f f₁ β γ c₁ y y₁,
  f₁ = next_pol f β γ c₁
  → (y = ps_monom c₁ γ + ps_monom 1%K γ * y₁)%ps
  → (ps_pol_apply f₁ y₁ = 0)%ps
  → (ps_pol_apply f y = 0)%ps.
Proof.
intros f f₁ β γ c₁ y y₁ Hpol₁ Hy Happ.
destruct (ps_zerop R 1%ps) as [Hzo| Hnzo].
 apply eq_1_0_all_0; assumption.

 subst f₁.
 unfold next_pol in Happ.
 unfold ps_pol_apply, apply_poly in Happ; simpl in Happ.
 unfold next_lap in Happ; simpl in Happ.
 unfold ps_pol_apply, apply_poly.
 rewrite apply_lap_mul in Happ.
 rewrite apply_lap_compose in Happ.
 simpl in Happ.
 rewrite ps_mul_0_l in Happ.
 do 2 rewrite ps_add_0_l in Happ.
 rewrite ps_add_comm, <- Hy in Happ.
 apply fld_eq_mul_0_r in Happ; [ assumption | apply ps_field | idtac ].
 simpl; intros H.
 apply ps_monom_0_coeff_0 in H.
 apply Hnzo.
 unfold ps_one; rewrite H.
 apply ps_zero_monom_eq.
Qed.

Theorem exists_ini_pt_nat_fst_seg : ∀ pol ns,
  ns = List.hd phony_ns (newton_segments pol)
  → ∃ i αi, ini_pt ns = (Qnat i, αi).
Proof.
intros pol ns Hns.
remember (newton_segments pol) as nsl eqn:Hnsl .
symmetry in Hnsl.
destruct nsl as [| ns₁].
 subst ns; simpl.
 exists 0%nat, 0; reflexivity.

 simpl in Hns; subst ns₁.
 eapply exists_ini_pt_nat with (pol := pol).
 rewrite Hnsl; left; reflexivity.
Qed.

Theorem exists_fin_pt_nat_fst_seg : ∀ pol ns,
  ns = List.hd phony_ns (newton_segments pol)
  → ∃ i αi, fin_pt ns = (Qnat i, αi).
Proof.
intros pol ns Hns.
remember (newton_segments pol) as nsl eqn:Hnsl .
symmetry in Hnsl.
destruct nsl as [| ns₁].
 subst ns; simpl.
 exists 0%nat, 0; reflexivity.

 simpl in Hns; subst ns₁.
 eapply exists_fin_pt_nat with (pol := pol).
 rewrite Hnsl; left; reflexivity.
Qed.

Theorem List_hd_in : ∀ α (l : list α) d a,
  a = List.hd d l
  → l ≠ []
  → a ∈ l.
Proof.
intros α₁ l d a Ha Hl.
destruct l; [ exfalso; apply Hl; reflexivity | left; auto ].
Qed.

Theorem hd_newton_segments : ∀ pol ns j k αj αk,
  ns = List.hd phony_ns (newton_segments pol)
 → ini_pt ns = (Qnat j, αj)
  → fin_pt ns = (Qnat k, αk)
  → (j < k)%nat
  → ns ∈ newton_segments pol.
Proof.
intros pol ns j k αj αk Hns Hini Hfin Hjk.
remember (newton_segments pol) as nsl.
symmetry in Heqnsl.
destruct nsl as [| ns₁]; simpl in Hns.
 subst ns; simpl in Hini, Hfin.
 injection Hini; intros; subst.
 injection Hfin; intros; subst.
 rewrite <- Nat2Z.inj_0 in H0.
 rewrite <- Nat2Z.inj_0 in H1.
 apply Nat2Z.inj in H0.
 apply Nat2Z.inj in H1.
 subst j k; exfalso; revert Hjk; apply Nat.lt_irrefl.

 subst ns; left; reflexivity.
Qed.

(* *)

Theorem nth_pol_succ : ∀ n pol ns pol₁ ns₁ c₁,
  pol₁ = nth_pol n pol ns
  → ns₁ = nth_ns n pol ns
  → c₁ = nth_c n pol ns
  → nth_pol (S n) pol ns = next_pol pol₁ (β ns₁) (γ ns₁) c₁.
Proof.
intros n pol ns pol₁ ns₁ c₁ Hpol₁ Hns₁ Hc₁; subst.
revert pol ns.
induction n; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
apply IHn.
Qed.

Theorem nth_ns_succ : ∀ n pol ns pol₁,
  pol₁ = nth_pol (S n) pol ns
  → nth_ns (S n) pol ns = List.hd phony_ns (newton_segments pol₁).
Proof.
intros n pol ns pol₁ Hpol₁; subst.
revert pol ns.
induction n; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
apply IHn.
Qed.

Theorem nth_c_succ : ∀ n pol ns pol₁ ns₁,
  pol₁ = nth_pol (S n) pol ns
  → ns₁ = nth_ns (S n) pol ns
  → nth_c (S n) pol ns = ac_root (Φq pol₁ ns₁).
Proof.
intros n pol ns pol₁ ns₁ Hpol₁ Hns₁; subst.
revert pol ns.
induction n; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
apply IHn.
Qed.

Theorem Qnum_inv_Qnat_sub : ∀ j k,
  (j < k)%nat
  → Qnum (/ (Qnat k - Qnat j)) = 1%Z.
Proof.
intros j k Hjk.
rewrite Qnum_inv; [ reflexivity | simpl ].
do 2 rewrite Z.mul_1_r.
rewrite Z.add_opp_r.
rewrite <- Nat2Z.inj_sub.
 rewrite <- Nat2Z.inj_0.
 apply Nat2Z.inj_lt.
 apply Nat.lt_add_lt_sub_r; assumption.

 apply Nat.lt_le_incl; assumption.
Qed.

Theorem Qden_inv_Qnat_sub : ∀ j k,
  (j < k)%nat
  → Qden (/ (Qnat k - Qnat j)) = Pos.of_nat (k - j).
Proof.
intros j k Hjk.
apply Pos2Z.inj.
rewrite Qden_inv.
 simpl.
 do 2 rewrite Z.mul_1_r.
 symmetry.
 rewrite <- positive_nat_Z; simpl.
 rewrite Nat2Pos.id.
  rewrite Nat2Z.inj_sub; auto.
  apply Nat.lt_le_incl; assumption.

  intros H.
  apply Nat.sub_0_le in H.
  apply Nat.nlt_ge in H; contradiction.

 simpl.
 do 2 rewrite Z.mul_1_r.
 rewrite Z.add_opp_r.
 rewrite <- Nat2Z.inj_sub.
  rewrite <- Nat2Z.inj_0.
  apply Nat2Z.inj_lt.
  apply Nat.lt_add_lt_sub_r; assumption.

  apply Nat.lt_le_incl; assumption.
Qed.

Theorem num_m_den_is_pos : ∀ pol ns j αj m,
  ns ∈ newton_segments pol
  → pol_in_K_1_m pol m
  → ini_pt ns = (Qnat j, αj)
  → (0 < Qnum αj)%Z
  → (0 < Z.to_nat (Qnum αj * ' m / ' Qden αj))%nat.
Proof.
intros pol ns j αj m Hns Hm Hini Hn.
assert (' Qden αj | Qnum αj * ' m)%Z as H.
 eapply den_αj_divides_num_αj_m; eauto .

 destruct H as (d, Hd).
 rewrite Hd.
 rewrite Z.div_mul; auto.
 destruct d as [| d| d].
  simpl in Hd.
  apply Z.eq_mul_0_l in Hd; auto.
  rewrite Hd in Hn.
  exfalso; revert Hn; apply Z.lt_irrefl.

  apply Pos2Nat.is_pos.

  simpl in Hd.
  pose proof (Pos2Z.neg_is_neg (d * Qden αj)) as I.
  rewrite <- Hd in I.
  apply Z.nle_gt in I.
  exfalso; apply I.
  apply Z.mul_nonneg_nonneg; auto.
  apply Z.lt_le_incl; assumption.
Qed.

Theorem next_pow_add : ∀ p q ns m,
  next_pow (p + q) ns m = (next_pow p ns m + q)%nat.
Proof.
intros p q ns m.
unfold next_pow.
rewrite Nat.add_shuffle0; reflexivity.
Qed.

Theorem nat_compare_add : ∀ a b c,
  Nat.compare a b = Nat.compare (a + c) (b + c).
Proof.
intros a b c.
remember (Nat.compare a b) as c₁ eqn:Hc₁ .
remember (Nat.compare (a + c) (b + c)) as c₂ eqn:Hc₂ .
symmetry in Hc₁, Hc₂.
destruct c₁.
 apply nat_compare_eq in Hc₁.
 destruct c₂; auto.
  apply nat_compare_lt in Hc₂.
  exfalso; omega.

  apply nat_compare_gt in Hc₂.
  exfalso; omega.

 apply nat_compare_lt in Hc₁.
 destruct c₂; auto.
  apply nat_compare_eq in Hc₂.
  exfalso; omega.

  apply nat_compare_gt in Hc₂.
  exfalso; omega.

 apply nat_compare_gt in Hc₁.
 destruct c₂; auto.
  apply nat_compare_eq in Hc₂.
  exfalso; omega.

  apply nat_compare_lt in Hc₂.
  exfalso; omega.
Qed.

Theorem find_coeff_add : ∀ pol ns m mx p dp i,
  (find_coeff mx (p + dp) m pol ns (i + dp) =
   find_coeff mx p m pol ns i)%K.
Proof.
intros pol ns m mx p dp i.
revert pol ns m p dp i.
induction mx; intros; [ reflexivity | simpl ].
destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁]; auto.
rewrite <- nat_compare_add.
remember (Nat.compare p i) as cmp eqn:Hcmp .
symmetry in Hcmp.
destruct cmp; auto.
rewrite next_pow_add.
apply IHmx.
Qed.

Theorem zerop_1st_n_const_coeff_succ : ∀ pol ns n,
  zerop_1st_n_const_coeff (S n) pol ns =
  zerop_1st_n_const_coeff 0 pol ns ||
  zerop_1st_n_const_coeff n (nth_pol 1 pol ns) (nth_ns 1 pol ns).
Proof.
intros pol ns n; simpl.
destruct (ps_zerop R (ps_poly_nth 0 pol)); reflexivity.
Qed.

Theorem zerop_1st_n_const_coeff_succ2 : ∀ pol ns n,
  zerop_1st_n_const_coeff (S n) pol ns =
  zerop_1st_n_const_coeff n pol ns ||
  zerop_1st_n_const_coeff 0 (nth_pol (S n) pol ns) (nth_ns (S n) pol ns).
Proof.
intros pol ns n.
revert pol ns.
induction n; intros.
 simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol)); reflexivity.

 remember (S n) as sn; simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
  rewrite Heqsn in |- * at 1; simpl.
  destruct (ps_zerop R (ps_poly_nth 0 pol)); [ auto | contradiction ].

  remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
  remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  rewrite IHn; simpl.
  remember (nth_pol sn pol₁ ns₁) as poln eqn:Hpoln .
  destruct (ps_zerop R (ps_poly_nth 0 poln)) as [H₂| H₂].
   do 2 rewrite Bool.orb_true_r; reflexivity.

   do 2 rewrite Bool.orb_false_r.
   subst sn; simpl.
   destruct (ps_zerop R (ps_poly_nth 0 pol)); [ contradiction | subst; auto ].
Qed.

Theorem zerop_1st_n_const_coeff_false_iff : ∀ pol ns n,
  zerop_1st_n_const_coeff n pol ns = false
  ↔ ∀ i : nat, i ≤ n → (ps_poly_nth 0 (nth_pol i pol ns) ≠ 0)%ps.
Proof.
intros pol ns n.
split; intros H.
 intros i Hin.
 revert pol ns i H Hin.
 induction n; intros.
  simpl in H.
  apply Nat.le_0_r in Hin; subst i.
  destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
  discriminate H.

  simpl in H.
  destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
   discriminate H.

   destruct i; auto; simpl.
   apply IHn; auto.
   apply Nat.succ_le_mono; assumption.

 revert pol ns H.
 induction n; intros; simpl.
  destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁]; auto.
  pose proof (H O (Nat.le_refl 0)) as H₂.
  contradiction.

  destruct (ps_zerop R (ps_poly_nth 0 pol)) as [H₁| H₁].
   pose proof (H O (Nat.le_0_l (S n))) as H₂.
   contradiction.

   apply IHn; intros i Hin.
   apply Nat.succ_le_mono, H in Hin; assumption.
Qed.

Theorem nth_c_n : ∀ pol₁ ns₁ poln nsn n,
  poln = nth_pol n pol₁ ns₁
  → nsn = nth_ns n pol₁ ns₁
  → nth_c n pol₁ ns₁ = ac_root (Φq poln nsn).
Proof.
intros pol₁ ns₁ poln nsn n Hpoln Hnsn.
revert pol₁ ns₁ poln nsn Hpoln Hnsn.
induction n; intros.
 simpl in Hpoln, Hnsn; simpl.
 subst poln nsn; reflexivity.

 simpl in Hpoln, Hnsn; simpl.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
 apply IHn; assumption.
Qed.

Theorem nth_pol_n : ∀ pol ns c pol₁ ns₁ poln nsn cn n,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → poln = nth_pol n pol ns
  → nsn = nth_ns n pol ns
  → cn = ac_root (Φq poln nsn)
  → nth_pol n pol₁ ns₁ = next_pol poln (β nsn) (γ nsn) cn.
Proof.
intros pol₁ ns₁ c₁ pol₂ ns₂ poln nsn cn n.
intros Hc₁ Hpol₂ Hns₂ Hpoln Hnsn Hcn.
revert pol₁ ns₁ c₁ pol₂ ns₂ poln nsn cn Hc₁ Hpol₂ Hns₂ Hpoln Hnsn Hcn.
induction n; intros.
 simpl in Hpoln, Hnsn; simpl.
 subst poln nsn pol₂ c₁ cn; reflexivity.

 simpl in Hpoln, Hnsn; simpl.
 remember (ac_root (Φq pol₂ ns₂)) as c₂ eqn:Hc₂ .
 remember (next_pol pol₂ (β ns₂) (γ ns₂) c₂) as pol₃ eqn:Hpol₃ .
 remember (List.hd phony_ns (newton_segments pol₃)) as ns₃ eqn:Hns₃ .
 rewrite <- Hc₁, <- Hpol₂, <- Hns₂ in Hpoln, Hnsn.
 eapply IHn; eauto .
Qed.

Theorem nth_ns_n : ∀ pol ns c pol₁ ns₁ poln nsn cn npoln n,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → poln = nth_pol n pol ns
  → nsn = nth_ns n pol ns
  → cn = ac_root (Φq poln nsn)
  → npoln = next_pol poln (β nsn) (γ nsn) cn
  → nth_ns n pol₁ ns₁ = List.hd phony_ns (newton_segments npoln).
Proof.
intros pol ns c pol₁ ns₁ poln nsn cn npoln n.
intros Hc Hpol₁ Hns₁ Hpoln Hnsn Hcn Hnpoln.
revert pol ns c pol₁ ns₁ poln nsn cn npoln Hc Hpol₁ Hns₁ Hpoln Hnsn Hcn
 Hnpoln.
induction n; intros.
 simpl in Hpoln, Hnsn; simpl.
 subst poln nsn npoln pol₁ ns₁ c cn.
 reflexivity.

 simpl in Hpoln, Hnsn; simpl.
 rewrite <- Hc, <- Hpol₁, <- Hns₁ in Hpoln, Hnsn.
 remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
 remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
 remember (List.hd phony_ns (newton_segments pol₂)) as ns₂.
 rename Heqns₂ into Hns₂.
 eapply IHn with (c := c₁); eauto .
Qed.

Theorem nth_γ_n : ∀ pol ns n nsn jn αjn kn αkn,
  nsn = nth_ns n pol ns
  → ini_pt nsn = (jn, αjn)
  → fin_pt nsn = (kn, αkn)
  → nth_γ n pol ns = (αjn - αkn) / (kn - jn).
Proof.
intros pol ns n nsn jm αjn kn αkn Hnsn Hini Hfin.
revert pol ns nsn jm αjn kn αkn Hnsn Hini Hfin.
induction n; intros.
 simpl in Hnsn; simpl.
 subst nsn; unfold γ; simpl.
 rewrite Hini, Hfin; simpl.
 reflexivity.

 simpl in Hnsn; simpl.
 eapply IHn; eauto .
Qed.

Theorem zerop_1st_n_const_coeff_true_if : ∀ pol ns b,
  zerop_1st_n_const_coeff b pol ns = true
  → ∀ n, zerop_1st_n_const_coeff (b + n) pol ns = true.
Proof.
intros pol ns b Hz n.
revert pol ns Hz n.
induction b; intros.
 simpl.
 revert pol ns Hz.
 induction n; intros; auto.
 simpl in Hz; simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
 discriminate Hz.

 simpl in Hz; simpl.
 destruct (ps_zerop R (ps_poly_nth 0 pol)); auto.
Qed.

Theorem root_head_from_cγ_list_succ : ∀ pol ns b n i,
  zerop_1st_n_const_coeff (b + i) pol ns = false
  → (root_head_from_cγ_list pol ns b (S n) i =
     root_head_from_cγ_list pol ns b n i +
      (if zerop_1st_n_const_coeff (b + i + S n) pol ns then 0
       else
         ps_monom (nth_c (b + i + S n) pol ns)
           (γ_sum b (i + S n) pol ns)))%ps.
Proof.
intros pol ns b n i Hz; simpl.
revert b i Hz.
induction n; intros; simpl.
 symmetry; rewrite rng_add_0_r; symmetry.
 rewrite Nat.add_1_r.
 remember (zerop_1st_n_const_coeff (S (b + i)) pol ns) as z₁ eqn:Hz₁ .
 symmetry in Hz₁.
 rewrite Nat.add_succ_r.
 destruct z₁.
  rewrite zerop_1st_n_const_coeff_succ2 in Hz₁.
  rewrite Hz, Bool.orb_false_l in Hz₁.
  remember (nth_pol (S (b + i)) pol ns) as p.
  simpl in Hz₁.
  destruct (ps_zerop R (ps_poly_nth 0 p)) as [H₂| H₂]; subst p.
   reflexivity.

   discriminate Hz₁.

  apply zerop_1st_n_const_coeff_false_iff with (i := S (b + i)) in Hz₁.
   remember (nth_pol (S (b + i)) pol ns) as p.
   destruct (ps_zerop R (ps_poly_nth 0 p)) as [H₂| H₂]; subst p.
    contradiction.

    rewrite rng_add_0_r, Nat.add_1_r; reflexivity.

   reflexivity.

 rewrite <- rng_add_assoc; simpl.
 apply rng_add_compat_l; simpl.
 remember (nth_pol (b + S i) pol ns) as p.
 destruct (ps_zerop R (ps_poly_nth 0 p)) as [H₁| H₁]; subst p.
  rewrite rng_add_0_l.
  remember (zerop_1st_n_const_coeff (b + i + S (S n)) pol ns) as z₁ eqn:Hz₁ .
  symmetry in Hz₁.
  destruct z₁; [ reflexivity | idtac ].
  rewrite zerop_1st_n_const_coeff_false_iff in Hz₁.
  assert (b + S i ≤ b + i + S (S n)) as H by fast_omega .
  apply Hz₁ in H; contradiction.

  rewrite IHn.
   do 7 rewrite Nat.add_succ_r; rewrite Nat.add_succ_l.
   reflexivity.

   rewrite Nat.add_succ_r.
   rewrite zerop_1st_n_const_coeff_succ2.
   rewrite Hz, Bool.orb_false_l.
   rewrite <- Nat.add_succ_r.
   apply zerop_1st_n_const_coeff_false_iff.
   intros j Hj.
   apply Nat.le_0_r in Hj; subst j.
   assumption.
Qed.

Theorem root_head_succ : ∀ pol ns b n,
  zerop_1st_n_const_coeff b pol ns = false
  → (root_head b (S n) pol ns =
     root_head b n pol ns +
     if zerop_1st_n_const_coeff (b + S n) pol ns then 0
     else ps_monom (nth_c (b + S n) pol ns) (γ_sum b (S n) pol ns))%ps.
Proof.
intros pol ns b n Hz.
unfold root_head; rewrite Hz.
rewrite root_head_from_cγ_list_succ.
 rewrite Nat.add_0_r, Nat.add_0_l.
 reflexivity.

 rewrite Nat.add_0_r; assumption.
Qed.

End theorems.
