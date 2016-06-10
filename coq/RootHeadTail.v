(* RootHeadTail.v *)

Require Import Utf8 QArith NPeano Sorting.

Require Import Misc.
Require Import Field.
Require Import Fpolynomial.
Require Import Fsummation.
Require Import Newton.
Require Import ConvexHull.
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
Require Import F1Prop.
Require Import Q_field.
Require Import PosOrder.
Require Import Qbar.

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
       if ps_zerop K (ps_poly_nth 0 (nth_pol (b + S i) pol ns)) then 0%ps
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
destruct (ps_zerop K 1%ps) as [Hzo| Hnzo].
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

Theorem nth_pol_succ2 : ∀ pol ns c pol₁ ns₁ n,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → nth_pol (S n) pol ns = nth_pol n pol₁ ns₁.
Proof. intros; subst; reflexivity. Qed.

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

Theorem nth_ns_succ2 : ∀ pol ns c pol₁ ns₁ n,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → nth_ns (S n) pol ns = nth_ns n pol₁ ns₁.
Proof. intros; subst; reflexivity. Qed.

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

Theorem nth_r_succ2 : ∀ pol ns c pol₁ ns₁ n,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → nth_r (S n) pol ns = nth_r n pol₁ ns₁.
Proof. intros; subst; reflexivity. Qed.

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

Theorem find_coeff_add : ∀ pol ns m mx p dp i,
  (find_coeff mx (p + dp) m pol ns (i + dp) =
   find_coeff mx p m pol ns i)%K.
Proof.
intros pol ns m mx p dp i.
revert pol ns m p dp i.
induction mx; intros; [ reflexivity | simpl ].
destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₁| H₁]; auto.
rewrite <- Nat_compare_add.
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
destruct (ps_zerop K (ps_poly_nth 0 pol)); reflexivity.
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
 destruct (ps_zerop K (ps_poly_nth 0 pol)); reflexivity.

 remember (S n) as sn; simpl.
 destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₁| H₁].
  rewrite Heqsn in |- * at 1; simpl.
  destruct (ps_zerop K (ps_poly_nth 0 pol)); [ auto | contradiction ].

  remember (ac_root (Φq pol ns)) as c₁ eqn:Hc₁ .
  remember (next_pol pol (β ns) (γ ns) c₁) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  rewrite IHn; simpl.
  remember (nth_pol sn pol₁ ns₁) as poln eqn:Hpoln .
  destruct (ps_zerop K (ps_poly_nth 0 poln)) as [H₂| H₂].
   do 2 rewrite Bool.orb_true_r; reflexivity.

   do 2 rewrite Bool.orb_false_r.
   subst sn; simpl.
   destruct (ps_zerop K (ps_poly_nth 0 pol)); [ contradiction | subst; auto ].
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
  destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.
  discriminate H.

  simpl in H.
  destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₁| H₁].
   discriminate H.

   destruct i; auto; simpl.
   apply IHn; auto.
   apply Nat.succ_le_mono; assumption.

 revert pol ns H.
 induction n; intros; simpl.
  destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₁| H₁]; auto.
  pose proof (H O (Nat.le_refl 0)) as H₂.
  contradiction.

  destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₁| H₁].
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

Theorem nth_r_n : ∀ pol ns pol₁ ns₁ c₁ n,
  pol₁ = nth_pol n pol ns
  → ns₁ = nth_ns n pol ns
  → c₁ = nth_c n pol ns
  → nth_r n pol ns = root_multiplicity acf c₁ (Φq pol₁ ns₁).
Proof.
intros pol ns pol₁ ns₁ c₁ n Hpol₁ Hns₁ Hc₁.
revert pol ns pol₁ ns₁ c₁ Hpol₁ Hns₁ Hc₁.
induction n; intros; [ subst; reflexivity | simpl ].
apply IHn; subst; reflexivity.
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
 destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.
 discriminate Hz.

 simpl in Hz; simpl.
 destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.
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
  destruct (ps_zerop K (ps_poly_nth 0 p)) as [H₂| H₂]; subst p.
   reflexivity.

   discriminate Hz₁.

  apply zerop_1st_n_const_coeff_false_iff with (i := S (b + i)) in Hz₁.
   remember (nth_pol (S (b + i)) pol ns) as p.
   destruct (ps_zerop K (ps_poly_nth 0 p)) as [H₂| H₂]; subst p.
    contradiction.

    rewrite rng_add_0_r, Nat.add_1_r; reflexivity.

   reflexivity.

 rewrite <- rng_add_assoc; simpl.
 apply rng_add_compat_l; simpl.
 remember (nth_pol (b + S i) pol ns) as p.
 destruct (ps_zerop K (ps_poly_nth 0 p)) as [H₁| H₁]; subst p.
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

Theorem root_head_from_cγ_list_succ_r : ∀ pol ns pol₁ ns₁ c n i,
  c = ac_root (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → zerop_1st_n_const_coeff n pol₁ ns₁ = false
  → (ps_poly_nth 0 pol₁ ≠ 0)%ps
  → (root_head_from_cγ_list pol ns 0 n (S i) =
      ps_monom 1%K (γ ns) * root_head_from_cγ_list pol₁ ns₁ 0 n i)%ps.
Proof.
intros pol ns pol₁ ns₁ c n i Hc Hpol₁ Hns₁ Hnz Hnz₁.
revert pol ns pol₁ ns₁ c i Hc Hpol₁ Hns₁ Hnz Hnz₁.
induction n; intros.
 simpl.
 unfold γ_sum; simpl.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite summation_shift; [ idtac | apply le_n_S, Nat.le_0_l ].
 rewrite Nat_sub_succ_1.
 do 2 rewrite rng_add_0_r; simpl.
 rewrite <- Hc, <- Hpol₁, <- Hns₁.
 rewrite rng_add_comm.
 rewrite ps_monom_add_r.
 apply ps_mul_comm.

 simpl in Hnz.
 destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hnz.

  remember (S i) as si; simpl.
  rewrite <- Hc, <- Hpol₁, <- Hns₁.
  subst si; simpl.
  rewrite <- Hc, <- Hpol₁, <- Hns₁.
  remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
  remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
  remember (List.hd phony_ns (newton_segments pol₂)) as ns₂.
  unfold γ_sum; simpl.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite summation_shift; [ idtac | apply le_n_S, Nat.le_0_l ].
  rewrite Nat_sub_succ_1.
  destruct (ps_zerop K (ps_poly_nth 0 (nth_pol i pol₂ ns₂))) as [H₂| H₂].
   do 2 rewrite rng_add_0_r.
   rewrite rng_add_comm.
   rewrite ps_monom_add_r; simpl.
   rewrite <- Hc, <- Hpol₁, <- Hns₁.
   apply ps_mul_comm.

   simpl.
   rewrite <- Hc, <- Hpol₁, <- Hns₁.
   rewrite ps_mul_add_distr_l.
   apply rng_add_compat.
    rewrite rng_add_comm; simpl.
    rewrite ps_monom_add_r.
    apply ps_mul_comm.

    apply IHn with (c := c); auto.
    rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
    apply zerop_1st_n_const_coeff_false_iff.
    clear i H₂.
    intros i Hin.
    destruct i; [ assumption | simpl ].
    rewrite <- Hc₁, <- Hpol₂, <- Heqns₂.
    apply Hnz, Nat.lt_le_incl; auto.
Qed.

Theorem apply_nth_pol : ∀ pol ns y n,
  let qr := Q_ring in
  zerop_1st_n_const_coeff n pol ns = false
  → (ps_pol_apply pol
       (root_head 0 n pol ns + ps_monom 1%K (γ_sum 0 n pol ns) * y) =
     ps_monom 1%K (Σ (i = 0, n), β (nth_ns i pol ns)) *
     ps_pol_apply (nth_pol (S n) pol ns) y)%ps.
Proof.
intros; revert H; intros Hnz.
revert pol ns y Hnz.
induction n; intros.
 unfold root_head; simpl.
 unfold γ_sum, summation; simpl.
 unfold next_pol; simpl.
 unfold ps_pol_apply; simpl.
 unfold apply_poly; simpl.
 unfold next_lap; simpl.
 remember (ac_root (Φq pol ns)) as c eqn:Hc .
 rewrite apply_lap_mul; simpl.
 rewrite rng_mul_0_l, rng_add_0_l.
 symmetry; rewrite rng_add_0_r; symmetry.
 rewrite rng_mul_assoc; simpl.
 rewrite <- ps_monom_add_r.
 rewrite rng_add_opp_r; simpl.
 rewrite ps_mul_1_l.
 rewrite apply_lap_compose; simpl.
 rewrite rng_mul_0_l, rng_add_0_l.
 simpl in Hnz.
 destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₁| H₁].
  discriminate Hnz.

  do 2 rewrite rng_add_0_r.
  rewrite rng_add_comm; reflexivity.

 simpl in Hnz.
 destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₁| H₁].
  discriminate Hnz.

  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite summation_shift; [ idtac | apply le_n_S, Nat.le_0_l ].
  rewrite Nat_sub_succ_1.
  remember (S n) as sn in |- *; simpl.
  remember (ac_root (Φq pol ns)) as c eqn:Hc .
  remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
  remember (List.hd phony_ns (newton_segments pol₁)) as ns₁ eqn:Hns₁ .
  rewrite ps_monom_add_r.
  rewrite <- rng_mul_assoc.
  subst sn; simpl.
  erewrite nth_pol_n with (pol := pol₁) (ns := ns₁); eauto .
  erewrite <- nth_pol_succ; eauto ; [ idtac | erewrite nth_c_n; eauto  ].
  remember (S n) as sn in |- *; simpl.
  unfold root_head; simpl.
  destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₂| H₂].
   contradiction.

   clear H₂.
   rewrite Heqsn in |- * at 1; simpl.
   rewrite <- Hc, <- Hpol₁.
   destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₂| H₂].
    rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
    pose proof (Hnz O (Nat.le_0_l n)) as H; contradiction.

    subst sn.
    rewrite <- IHn; auto.
    unfold root_head; simpl.
    destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₃| H₃].
     contradiction.

     clear H₃.
     unfold γ_sum at 1, summation; simpl.
     rewrite rng_add_0_r.
     unfold γ_sum.
     rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
     rewrite summation_shift; [ idtac | apply le_n_S, Nat.le_0_l ].
     rewrite Nat_sub_succ_1; simpl.
     rewrite <- Hc, <- Hpol₁, <- Hns₁.
     rewrite ps_monom_add_r.
     remember Σ (i = 0, n), nth_γ i pol₁ ns₁ as sγ eqn:Hsγ .
     rewrite <- ps_mul_assoc.
     remember (ps_monom 1%K sγ * y)%ps as u eqn:Hu .
     rewrite Hpol₁ in |- * at 1; simpl.
     unfold next_pol; simpl.
     unfold ps_pol_apply; simpl.
     unfold apply_poly; simpl.
     unfold next_lap; simpl.
     rewrite apply_lap_mul; simpl.
     rewrite rng_mul_0_l, rng_add_0_l.
     rewrite rng_mul_assoc; simpl.
     rewrite <- ps_monom_add_r.
     rewrite rng_add_opp_r; simpl.
     rewrite ps_mul_1_l.
     rewrite apply_lap_compose; simpl.
     rewrite rng_mul_0_l, rng_add_0_l.
     symmetry; rewrite ps_add_comm; symmetry.
     rewrite ps_mul_add_distr_l.
     rewrite ps_add_assoc.
     rewrite root_head_from_cγ_list_succ_r; eauto .
     reflexivity.
Qed.

Theorem summation_all_lt : ∀ f n x,
  let qr := Q_ring in
  (∀ i : nat, i ≤ n → x < f i)
  → x * Qnat (S n) < Σ (i = 0, n), f i.
Proof.
intros f n x qr Hi.
induction n.
 unfold Qnat, summation; simpl.
 rewrite rng_add_0_r.
 rewrite rng_mul_1_r.
 apply Hi; reflexivity.

 rewrite summation_split_last; [ simpl | apply Nat.le_0_l ].
 rewrite Qnat_succ.
 apply Qplus_lt_le_compat.
  apply IHn.
  intros i Hin; apply Hi.
  apply Nat.le_le_succ_r; auto.

  apply Qlt_le_weak.
  apply Hi; reflexivity.
Qed.

Theorem order_pol_apply_nonneg : ∀ pol y,
  (∀ a, a ∈ al pol → (0 ≤ order a)%Qbar)
  → (0 ≤ order y)%Qbar
  → (0 ≤ order (ps_pol_apply pol y))%Qbar.
Proof.
intros pol y Ha Hy.
unfold ps_pol_apply, apply_poly.
remember (al pol) as la; clear Heqla.
induction la as [| a]; intros; simpl.
 rewrite order_0; constructor.

 eapply Qbar.le_trans; [ idtac | apply order_add ].
 rewrite order_mul; auto.
 apply Qbar.min_glb.
  eapply Qbar.le_trans; eauto .
  rewrite Qbar.add_comm.
  apply Qbar.le_sub_le_add_l.
  rewrite Qbar.sub_diag.
  apply IHla.
  intros b Hb.
  apply Ha; right; assumption.

  apply Ha; left; reflexivity.
Qed.

Theorem eq_1_0_ps_0 : (1 = 0)%K → ∀ a, (a = 0)%ps.
Proof.
intros H a.
apply order_inf.
unfold order.
remember (series_order (ps_terms a) 0) as v eqn:Hv .
symmetry in Hv.
destruct v as [v| ]; auto.
apply series_order_iff in Hv.
destruct Hv as (_, Hv).
exfalso; apply Hv; simpl.
apply eq_1_0_all_0; assumption.
Qed.

Theorem lowest_zerop_1st_n_const_coeff : ∀ pol ns n,
  zerop_1st_n_const_coeff n pol ns = true
  → ∃ i,
    i ≤ n ∧
    (i = O ∨ zerop_1st_n_const_coeff (pred i) pol ns = false) ∧
    zerop_1st_n_const_coeff i pol ns = true.
Proof.
intros pol ns n Hz.
revert pol ns Hz.
induction n; intros.
 exists O.
 split; [ reflexivity | idtac ].
 split; [ left; reflexivity | assumption ].

 simpl in Hz.
 destruct (ps_zerop K (ps_poly_nth 0 pol)) as [H₁| H₁].
  exists O.
  split; [ apply Nat.le_0_l | idtac ].
  split; [ left; reflexivity | simpl ].
  destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.

  apply IHn in Hz.
  destruct Hz as (i, (Hin, (Hji, Hz))).
  destruct Hji as [Hji| Hji].
   subst i.
   simpl in Hz.
   remember (ac_root (Φq pol ns)) as c eqn:Hc .
   remember (next_pol pol (β ns) (γ ns) c) as pol₁ eqn:Hpol₁ .
   destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₂| H₂].
    exists 1%nat.
    split; [ apply le_n_S, Nat.le_0_l | simpl ].
    destruct (ps_zerop K (ps_poly_nth 0 pol)); [ contradiction | idtac ].
    split; [ right; reflexivity | idtac ].
    rewrite <- Hc, <- Hpol₁.
    destruct (ps_zerop K (ps_poly_nth 0 pol₁)); auto.

    discriminate Hz.

   destruct i.
    simpl in Hji, Hz.
    rewrite Hji in Hz.
    discriminate Hz.

    simpl in Hji.
    exists (S (S i)).
    split; [ apply le_n_S; auto | idtac ].
    split.
     right; simpl.
     destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.
     contradiction.

     remember (S i) as si; simpl; subst si.
     destruct (ps_zerop K (ps_poly_nth 0 pol)); auto.
Qed.

Theorem first_null_coeff : ∀ pol₁ ns₁ i a₁ la₁,
  zerop_1st_n_const_coeff i pol₁ ns₁ = false
  → zerop_1st_n_const_coeff (S i) pol₁ ns₁ = true
  → al (nth_pol (S i) pol₁ ns₁) = [a₁ … la₁]
  → (a₁ = 0)%ps.
Proof.
intros pol₁ ns₁ i a₁ la₁ Hnz₁ Hz₁ Hla₁.
revert pol₁ ns₁ a₁ la₁ Hnz₁ Hz₁ Hla₁.
induction i; intros.
 simpl in Hnz₁, Hz₁, Hla₁.
 destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hnz₁.

  remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
  remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
  remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
  destruct (ps_zerop K (ps_poly_nth 0 pol₂)) as [H₂| H₂].
   unfold ps_poly_nth, ps_lap_nth in H₂; simpl in H₂.
   unfold next_pol in Hpol₂.
   rewrite Hla₁ in Hpol₂.
   rewrite Hpol₂ in H₂; simpl in H₂.
   assumption.

   discriminate Hz₁.

 remember (S i) as si; simpl in Hz₁, Hla₁; subst si.
 simpl in Hnz₁.
 destruct (ps_zerop K (ps_poly_nth 0 pol₁)) as [H₁| H₁].
  discriminate Hnz₁.

  remember (ac_root (Φq pol₁ ns₁)) as c₁ eqn:Hc₁ .
  remember (next_pol pol₁ (β ns₁) (γ ns₁) c₁) as pol₂ eqn:Hpol₂ .
  remember (List.hd phony_ns (newton_segments pol₂)) as ns₂ eqn:Hns₂ .
  eapply IHi; eauto .
Qed.

Theorem a₀_0_root_0 : ∀ pol,
  (ps_poly_nth 0 pol = 0)%ps
  → (ps_pol_apply pol 0 = 0)%ps.
Proof.
intros pol H.
unfold ps_pol_apply, apply_poly, apply_lap; simpl.
unfold ps_poly_nth in H.
destruct (al pol) as [| a la]; [ reflexivity | simpl ].
unfold ps_lap_nth in H; simpl in H.
rewrite rng_mul_0_r, rng_add_0_l; assumption.
Qed.

Theorem root_when_fin : ∀ pol ns n,
  zerop_1st_n_const_coeff (pred n) pol ns = false
  → zerop_1st_n_const_coeff n pol ns = true
  → ∃ s, (ps_pol_apply pol s = 0)%ps.
Proof.
intros pol ns n Hnz Hz.
exists (root_head 0 (pred n) pol ns).
destruct n.
 rewrite Nat.pred_0 in Hnz.
 rewrite Hnz in Hz; discriminate Hz.

 rewrite Nat.pred_succ in Hnz.
 rewrite Nat.pred_succ.
 remember Hnz as H; clear HeqH.
 eapply apply_nth_pol with (y := 0%ps) in H.
 rewrite rng_mul_0_r, rng_add_0_r in H; rewrite H.
 unfold ps_pol_apply, apply_poly.
 remember (S n) as sn.
 unfold apply_lap; simpl.
 remember (al (nth_pol sn pol ns)) as la eqn:Hla .
 symmetry in Hla.
 destruct la as [| a]; simpl.
  rewrite rng_mul_0_r; reflexivity.

  rewrite rng_mul_0_r, rng_add_0_l; subst sn.
  rewrite first_null_coeff with (a₁ := a); eauto .
  rewrite rng_mul_0_r; reflexivity.
Qed.

Theorem no_newton_segments : ∀ pol,
  (ps_poly_nth 0 pol ≠ 0)%ps
  → newton_segments pol = []
  → (∀ i, (0 < i)%nat → (ps_poly_nth i pol = 0)%ps).
Proof.
(* perhaps simplifiable *)
intros pol Hnz Hns i Hi.
destruct i; [ exfalso; revert Hi; apply Nat.lt_irrefl | idtac ].
clear Hi.
unfold newton_segments in Hns.
unfold lower_convex_hull_points in Hns.
unfold points_of_ps_polynom in Hns.
unfold points_of_ps_lap in Hns.
remember (al pol) as la eqn:Hla .
symmetry in Hla.
unfold ps_poly_nth.
unfold ps_poly_nth in Hnz.
rewrite Hla in Hnz; rewrite Hla.
clear pol Hla.
unfold points_of_ps_lap_gen in Hns.
unfold qpower_list in Hns.
remember (pair_rec (λ pow ps, (Qnat pow, ps))) as f.
unfold ps_lap_nth in Hnz.
unfold ps_lap_nth.
revert la Hnz Hns.
induction i; intros.
 destruct la as [| a].
  exfalso; apply Hnz; reflexivity.

  simpl in Hnz; simpl.
  simpl in Hns.
  remember (f (O, a)) as fa.
  rewrite Heqf in Heqfa.
  simpl in Heqfa.
  unfold pair_rec in Heqfa; simpl in Heqfa.
  subst fa; simpl in Hns.
  apply order_fin in Hnz.
  remember (order a) as oa.
  symmetry in Heqoa.
  destruct oa as [oa| ]; [ idtac | exfalso; apply Hnz; reflexivity ].
  simpl in Hns.
  remember (filter_finite_ord (List.map f (power_list 1 la))) as pts.
  symmetry in Heqpts.
  destruct pts; [ idtac | discriminate Hns ].
  clear Hns Hnz.
  destruct la as [| b]; [ reflexivity | simpl ].
  simpl in Heqpts.
  remember (f (1%nat, b)) as fb.
  rewrite Heqf in Heqfb.
  unfold pair_rec in Heqfb.
  simpl in Heqfb.
  subst fb; simpl in Heqpts.
  remember (order b) as ob.
  symmetry in Heqob.
  destruct ob as [ob| ]; auto.
   discriminate Heqpts.

   apply order_inf; assumption.

 destruct la as [| a]; [ reflexivity | simpl ].
 simpl in Hnz.
 simpl in Hns.
 remember (f (O, a)) as fa.
 rewrite Heqf in Heqfa.
 simpl in Heqfa.
 unfold pair_rec in Heqfa; simpl in Heqfa.
 subst fa; simpl in Hns.
 apply order_fin in Hnz.
 remember (order a) as oa.
 symmetry in Heqoa.
 destruct oa as [oa| ]; [ idtac | exfalso; apply Hnz; reflexivity ].
 simpl in Hns.
 remember (filter_finite_ord (List.map f (power_list 1 la))) as pts.
 symmetry in Heqpts.
 destruct pts; [ idtac | discriminate Hns ].
 clear Hns.
 clear Hnz.
 revert Heqf Heqpts; clear; intros.
 remember 1%nat as pow; clear Heqpow.
 revert i pow Heqpts.
 induction la as [| a]; intros; [ reflexivity | idtac ].
 simpl in Heqpts.
 remember (f (pow, a)) as fa.
 rewrite Heqf in Heqfa.
 unfold pair_rec in Heqfa.
 simpl in Heqfa.
 subst fa; simpl in Heqpts.
 remember (order a) as oa.
 symmetry in Heqoa.
 destruct oa as [oa| ]; [ discriminate Heqpts | simpl ].
 destruct i.
  destruct la as [| b]; [ reflexivity | simpl ].
  simpl in Heqpts.
  remember (f (S pow, b)) as fb.
  rewrite Heqf in Heqfb.
  unfold pair_rec in Heqfb; simpl in Heqfb.
  subst fb.
  apply order_inf.
  remember (order b) as ob.
  symmetry in Heqob.
  destruct ob as [ob| ]; [ discriminate Heqpts | reflexivity ].

  eapply IHla; eauto .
Qed.

Theorem root_multiplicity_0 : ∀ c cpol,
  c = ac_root cpol
  → root_multiplicity acf c cpol = 0%nat
  → (degree fld_zerop cpol = 0)%nat.
Proof.
intros c cpol Hc Hr.
unfold root_multiplicity in Hr.
unfold degree, apply_poly.
remember (al cpol) as la.
symmetry in Heqla.
destruct la as [| a]; [ reflexivity | simpl ].
simpl in Hr.
unfold lap_mod_deg_1 in Hr; simpl in Hr.
destruct (fld_zerop (apply_lap la c * c + a)%K) as [H₁| H₁].
 discriminate Hr.

 remember (degree fld_zerop cpol) as deg eqn:Hdeg .
 symmetry in Hdeg.
 destruct deg.
  unfold degree in Hdeg.
  rewrite Heqla in Hdeg.
  simpl in Hdeg.
  assumption.

  assert (degree fld_zerop cpol ≥ 1)%nat as H.
   rewrite Hdeg; apply le_n_S, Nat.le_0_l.

   clear Hdeg.
   apply ac_prop_root in H.
   rewrite <- Hc in H.
   unfold apply_poly in H.
   rewrite Heqla in H; simpl in H.
   contradiction.
Qed.

Theorem degree_eq_0_if : ∀ cpol,
  degree fld_zerop cpol = O
  → (cpol = POL [])%pol ∨ (∃ a, (a ≠ 0)%K ∧ (cpol = POL [a])%pol).
Proof.
intros cpol Hdeg.
unfold degree in Hdeg.
unfold eq_poly; simpl.
remember (al cpol) as la; clear Heqla.
induction la as [| a]; [ left; reflexivity | idtac ].
simpl in Hdeg.
remember (degree_plus_1_of_list fld_zerop la) as deg eqn:Hdeg₁ .
symmetry in Hdeg₁.
destruct deg.
 clear Hdeg.
 pose proof (IHla (Nat.eq_refl O)) as H.
 clear IHla.
 destruct H as [Hla| Hla].
  rewrite Hla.
  destruct (fld_zerop a) as [H₁| H₁].
   left; rewrite H₁.
   apply lap_eq_0.

   right.
   exists a.
   split; [ assumption | idtac ].
   rewrite Hla; reflexivity.

  clear cpol.
  destruct Hla as (b, (Hb, Hla)).
  rewrite Hla.
  right.
  revert a b Hb Hla.
  induction la as [| c]; intros.
   apply lap_eq_nil_cons_inv in Hla.
   destruct Hla; contradiction.

   simpl in Hdeg₁.
   apply lap_eq_cons_inv in Hla.
   destruct Hla as (Hcb, Hla).
   remember (degree_plus_1_of_list fld_zerop la) as deg eqn:Hdeg .
   symmetry in Hdeg.
   destruct deg.
    destruct (fld_zerop c) as [H₁| H₁]; [ idtac | discriminate Hdeg₁ ].
    rewrite H₁ in Hcb.
    symmetry in Hcb; contradiction.

    discriminate Hdeg₁.

 discriminate Hdeg.
Qed.

Theorem multiplicity_neq_0 : ∀ pol ns c,
  ns ∈ newton_segments pol
  → c = ac_root (Φq pol ns)
  → root_multiplicity acf c (Φq pol ns) ≠ O.
Proof.
intros pol ns c Hns Hc Hr.
apply root_multiplicity_0 in Hr; eauto .
apply degree_eq_0_if in Hr.
destruct Hr as [Hr| Hr].
 unfold Φq in Hr; simpl in Hr.
 rewrite Nat.sub_diag in Hr; simpl in Hr.
 unfold eq_poly in Hr; simpl in Hr.
 remember Hns as H; clear HeqH.
 apply exists_ini_pt_nat in H.
 destruct H as (j, (αj, Hini)).
 rewrite Hini in Hr; simpl in Hr.
 rewrite nat_num_Qnat in Hr.
 apply lap_eq_cons_nil_inv in Hr.
 destruct Hr as (Hoj, Hcpol).
 exfalso; revert Hoj.
 eapply ord_coeff_non_zero_in_newt_segm; eauto .
 left; eassumption.

 destruct Hr as (a, (Ha, Hcpol)).
 unfold Φq in Hcpol; simpl in Hcpol.
 remember Hns as H; clear HeqH.
 apply exists_ini_pt_nat in H.
 destruct H as (j, (αj, Hini)).
 rewrite Hini in Hcpol; simpl in Hcpol.
 rewrite nat_num_Qnat in Hcpol.
 rewrite Nat.sub_diag in Hcpol.
 simpl in Hcpol.
 unfold eq_poly in Hcpol; simpl in Hcpol.
 apply lap_eq_cons_inv in Hcpol.
 destruct Hcpol as (Hoa, Hcpol).
 remember (oth_pts ns) as opts eqn:Hopts .
 symmetry in Hopts.
 destruct opts as [| pt].
  simpl in Hcpol.
  remember Hns as H; clear HeqH.
  apply exists_fin_pt_nat in H.
  destruct H as (k, (αk, Hfin)).
  rewrite Hfin in Hcpol.
  simpl in Hcpol.
  rewrite nat_num_Qnat in Hcpol; simpl in Hcpol.
  remember (k - S j)%nat as kj.
  clear Heqkj.
  induction kj.
   simpl in Hcpol.
   apply lap_eq_cons_nil_inv in Hcpol.
   destruct Hcpol as (Hoc, _).
   exfalso; revert Hoc.
   eapply ord_coeff_non_zero_in_newt_segm; eauto .
   rewrite Hopts; simpl.
   right; left; eassumption.

   simpl in Hcpol.
   apply lap_eq_cons_nil_inv in Hcpol.
   destruct Hcpol as (_, Hcpol).
   apply IHkj in Hcpol.
   assumption.

  simpl in Hcpol.
  remember Hns as H; clear HeqH.
  eapply exists_oth_pt_nat with (pt := pt) in H.
   destruct H as (h, (αh, Hoth)).
   rewrite Hoth in Hcpol; simpl in Hcpol.
   rewrite nat_num_Qnat in Hcpol.
   remember (h - S j)%nat as hj.
   clear Heqhj.
   induction hj.
    simpl in Hcpol.
    apply lap_eq_cons_nil_inv in Hcpol.
    destruct Hcpol as (Hoc, _).
    exfalso; revert Hoc.
    eapply ord_coeff_non_zero_in_newt_segm; eauto .
    right; apply List.in_or_app; left.
    rewrite Hopts; left; eassumption.

    simpl in Hcpol.
    apply lap_eq_cons_nil_inv in Hcpol.
    destruct Hcpol as (_, Hcpol).
    apply IHhj in Hcpol.
    assumption.

   rewrite Hopts; left; reflexivity.
Qed.

End theorems.
