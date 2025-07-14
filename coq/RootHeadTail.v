(* RootHeadTail.v *)

From Stdlib Require Import Utf8 Arith Sorting.

Require Import A_PosArith A_ZArith A_QArith.
Require Import Misc.
Require Import Field2.
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
Require Import QbarM.

Set Implicit Arguments.

Definition phony_ns :=
  {| ini_pt := (0%nat, 0); fin_pt := (0%nat, 0); oth_pts := [] |}.

Definition option_get {A} (x : A) v :=
  match v with
  | Some v => v
  | None => x
  end.

Fixpoint nth_pol α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n f L :=
  match n with
  | 0%nat => f
  | S n₁ =>
      let c₁ := ac_root (Φq f L) in
      let f₁ := next_pol f (β L) (γ L) c₁ in
      let L₁ := option_get phony_ns (newton_segments f₁) in
      nth_pol n₁ f₁ L₁
  end.

Fixpoint nth_ns α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n f L :=
  match n with
  | 0%nat => L
  | S n₁ =>
      let c₁ := ac_root (Φq f L) in
      let f₁ := next_pol f (β L) (γ L) c₁ in
      let L₁ := option_get phony_ns (newton_segments f₁) in
      nth_ns n₁ f₁ L₁
  end.

Fixpoint nth_c α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n f L :=
  match n with
  | 0%nat => ac_root (Φq f L)
  | S n₁ =>
      let c₁ := ac_root (Φq f L) in
      let f₁ := next_pol f (β L) (γ L) c₁ in
      let L₁ := option_get phony_ns (newton_segments f₁) in
      nth_c n₁ f₁ L₁
  end.

Fixpoint nth_γ α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n f L :=
  match n with
  | 0%nat => γ L
  | S n₁ =>
      let c₁ := ac_root (Φq f L) in
      let f₁ := next_pol f (β L) (γ L) c₁ in
      let L₁ := option_get phony_ns (newton_segments f₁) in
      nth_γ n₁ f₁ L₁
  end.

Fixpoint nth_r α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  n f L :=
  match n with
  | 0%nat => root_multiplicity acf (ac_root (Φq f L)) (Φq f L)
  | S n₁ =>
      let c₁ := ac_root (Φq f L) in
      let f₁ := next_pol f (β L) (γ L) c₁ in
      let L₁ := option_get phony_ns (newton_segments f₁) in
      nth_r n₁ f₁ L₁
  end.

Definition inject_Z a := a # 1.

Definition next_pow pow L₁ m :=
  let n := (γ L₁ * inject_Z (z_pos m)) in
  (pow + Z.to_nat (q_num n / z_pos (q_den n)))%nat.

Fixpoint find_coeff α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} max_iter npow m f L i :=
  match max_iter with
  | 0%nat => 0%K
  | S mx =>
      if ps_zerop _ (ps_poly_nth 0 f) then 0%K
      else
        match Nat.compare npow i with
        | Eq => ac_root (Φq f L)
        | Lt =>
            let c₁ := ac_root (Φq f L) in
            let f₁ := next_pol f (β L) (γ L) c₁ in
            let L₁ := option_get phony_ns (newton_segments f₁) in
            let npow₁ := next_pow npow L₁ m in
            find_coeff mx npow₁ m f₁ L₁ i
        | Gt => 0%K
        end
  end.

Definition root_tail_series_from_cγ_list α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} m f L i :=
  find_coeff (S i) 0%nat m f L i.

Definition root_tail_from_cγ_list α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} m f L :=
  {| ps_terms := {| terms := root_tail_series_from_cγ_list m f L |};
     ps_ordnum := q_num (γ L) * z_pos m / z_pos (q_den (γ L));
     ps_polydo := m |}.

Definition γ_sum α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} b n f L :=
  let qr := Q_ring in
  Σ (i = 0, n), nth_γ (b + i) f L.

Fixpoint root_head_from_cγ_list α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} f L b n i :=
  (ps_monom (nth_c (b + i) f L) (γ_sum b i f L) +
   match n with
   | O => 0%ps
   | S n₁ =>
       if ps_zerop K (ps_poly_nth 0 (nth_pol (b + S i) f L)) then 0%ps
       else root_head_from_cγ_list f L b n₁ (S i)
   end)%ps.

Fixpoint zerop_1st_n_const_coeff α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} n f L :=
  if ps_zerop _ (ps_poly_nth 0 f) then true
  else
    match n with
    | O => false
    | S n₁ =>
        let c₁ := ac_root (Φq f L) in
        let f₁ := next_pol f (β L) (γ L) c₁ in
        let L₁ := option_get phony_ns (newton_segments f₁) in
        zerop_1st_n_const_coeff n₁ f₁ L₁
    end.

(* Σ _(i=0,n).c_{b+i} x^Σ_(j=0,i) γ_{b+j} *)
Definition root_head α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  b n f L :=
  if zerop_1st_n_const_coeff b f L then 0%ps
  else root_head_from_cγ_list f L b n 0.

(* Σ _(i=n,∞).c_i x^Σ_(j=n,i) γ_j *)
Definition root_tail α {R : ring α} {K : field R} {acf : algeb_closed_field K}
  m n f L :=
  if zerop_1st_n_const_coeff n f L then 0%ps
  else root_tail_from_cγ_list m (nth_pol n f L) (nth_ns n f L).

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Theorem fold_γ_sum : ∀ b n f L,
  let qr := Q_ring in
  Σ (i = 0, n), nth_γ (b + i) f L = γ_sum b n f L.
Proof. reflexivity. Qed.

(* *)

(* f₁(x,y₁) = 0 => f(x,c₁.x^γ+x^γ.y₁) = 0 *)
Theorem f₁_root_f_root : ∀ f f₁ β γ c₁ y y₁,
  f₁ = next_pol f β γ c₁
  → (y = ps_monom c₁ γ + ps_monom 1%K γ * y₁)%ps
  → (ps_pol_apply f₁ y₁ = 0)%ps
  → (ps_pol_apply f y = 0)%ps.
Proof.
intros f f₁ β γ c₁ y y₁ Hf₁ Hy Happ.
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

Theorem exists_ini_pt_nat_fst_seg : ∀ f L,
  L = option_get phony_ns (newton_segments f)
  → ∃ i αi, ini_pt L = (i, αi).
Proof.
intros f L HL.
remember (newton_segments f) as Ll eqn:HLl .
symmetry in HLl.
destruct Ll as [L₁| ]. {
  remember (ini_pt L) as j eqn:Hini.
  destruct j as (j, αj).
  symmetry in Hini.
  now exists j, αj.
}
subst L; simpl.
exists 0%nat, 0; reflexivity.
Qed.

Theorem exists_fin_pt_nat_fst_seg : ∀ f L,
  L = option_get phony_ns (newton_segments f)
  → ∃ i αi, fin_pt L = (i, αi).
Proof.
intros f L HL.
remember (newton_segments f) as Ll eqn:HLl .
symmetry in HLl.
destruct Ll as [L₁| ]. {
  remember (fin_pt L) as j eqn:Hini.
  destruct j as (j, αj).
  symmetry in Hini.
  now exists j, αj.
}
subst L; simpl.
exists 0%nat, 0; reflexivity.
Qed.

Theorem hd_newton_segments : ∀ f L j k αj αk,
  L = option_get phony_ns (newton_segments f)
 → ini_pt L = (j, αj)
  → fin_pt L = (k, αk)
  → (j < k)%nat
  → newton_segments f = Some L.
Proof.
intros f L j k αj αk HL Hini Hfin Hjk.
remember (newton_segments f) as Ll.
symmetry in HeqLl.
destruct Ll as [L₁| ]; simpl in HL. {
  subst L; reflexivity.
}
subst L; simpl in Hini, Hfin.
injection Hini; intros; subst.
injection Hfin; intros; subst.
now apply Nat.lt_irrefl in Hjk.
Qed.

(* *)

Theorem nth_pol_succ : ∀ n f L f₁ L₁ c₁,
  f₁ = nth_pol n f L
  → L₁ = nth_ns n f L
  → c₁ = nth_c n f L
  → nth_pol (S n) f L = next_pol f₁ (β L₁) (γ L₁) c₁.
Proof.
intros n f L f₁ L₁ c₁ Hf₁ HL₁ Hc₁; subst.
revert f L.
induction n; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
apply IHn.
Qed.

Theorem nth_pol_succ2 : ∀ f L c f₁ L₁ n,
  c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → nth_pol (S n) f L = nth_pol n f₁ L₁.
Proof. intros; subst; reflexivity. Qed.

Theorem nth_ns_succ : ∀ n f L f₁,
  f₁ = nth_pol (S n) f L
  → nth_ns (S n) f L = option_get phony_ns (newton_segments f₁).
Proof.
intros n f L f₁ Hf₁; subst.
revert f L.
induction n; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
apply IHn.
Qed.

Theorem nth_ns_succ2 : ∀ f L c f₁ L₁ n,
  c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → nth_ns (S n) f L = nth_ns n f₁ L₁.
Proof. intros; subst; reflexivity. Qed.

Theorem nth_c_succ : ∀ n f L f₁ L₁,
  f₁ = nth_pol (S n) f L
  → L₁ = nth_ns (S n) f L
  → nth_c (S n) f L = ac_root (Φq f₁ L₁).
Proof.
intros n f L f₁ L₁ Hf₁ HL₁; subst.
revert f L.
induction n; intros; [ reflexivity | idtac ].
remember (S n) as sn; simpl; subst sn.
apply IHn.
Qed.

Theorem nth_r_succ2 : ∀ f L c f₁ L₁ n,
  c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → nth_r (S n) f L = nth_r n f₁ L₁.
Proof. intros; subst; reflexivity. Qed.

Theorem Qnum_inv_Qnat_sub : ∀ j k,
  (j < k)%nat
  → q_num ((Qnat k - Qnat j)⁻¹) = 1%Z.
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
  → q_den ((Qnat k - Qnat j)⁻¹) = Pos.of_nat (k - j).
Proof.
intros j k Hjk.
apply Pos2Z.inj.
rewrite Qden_inv.
 simpl.
 do 2 rewrite Z.mul_1_r.
 symmetry.
 rewrite <- Z.pos_nat; simpl.
 rewrite Nat2Pos.id.
  rewrite Nat2Z.inj_sub; [ | apply Nat.lt_le_incl; assumption ].
  reflexivity.

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

Theorem num_m_den_is_pos : ∀ f L j αj m,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → ini_pt L = (j, αj)
  → (0 < q_num αj)%Z
  → (0 < Z.to_nat (q_num αj * z_pos m / z_pos (q_den αj)))%nat.
Proof.
intros f L j αj m HL Hm Hini Hn.
assert (z_pos (q_den αj) | q_num αj * z_pos m)%Z as H.
 eapply den_αj_divides_num_αj_m; eassumption.

 destruct H as (d, Hd).
 rewrite Hd.
 rewrite Z.mul_div; [ | apply Pos2Z_ne_0 ].
 destruct d as [| sd vd].
  simpl in Hd.
  apply Z.eq_mul_0_l in Hd; [ | apply Pos2Z_ne_0 ].
  rewrite Hd in Hn.
  exfalso; revert Hn; apply Z.lt_irrefl.

  destruct sd; [ apply Pos2Nat.is_pos | ].
  simpl in Hd.
  pose proof (Pos2Z.neg_is_neg (vd * q_den αj)) as I.
  progress unfold z_neg in I.
  rewrite <- Hd in I.
  apply Z.nle_gt in I.
  exfalso; apply I.
  apply Z.mul_nonneg_nonneg; [ | apply Pos2Z.is_nonneg].
  apply Z.lt_le_incl; assumption.
Qed.

Theorem next_pow_add : ∀ p q L m,
  next_pow (p + q) L m = (next_pow p L m + q)%nat.
Proof.
intros p q L m.
unfold next_pow.
rewrite Nat.add_shuffle0; reflexivity.
Qed.

Theorem find_coeff_add : ∀ f L m mx p dp i,
  (find_coeff mx (p + dp) m f L (i + dp) =
   find_coeff mx p m f L i)%K.
Proof.
intros f L m mx p dp i.
revert f L m p dp i.
induction mx; intros; [ reflexivity | simpl ].
destruct (ps_zerop K (ps_poly_nth 0 f)) as [| H₁]; [ reflexivity | ].
rewrite <- Nat_compare_add.
remember (Nat.compare p i) as cmp eqn:Hcmp .
symmetry in Hcmp.
destruct cmp; [ reflexivity | | reflexivity ].
rewrite next_pow_add.
apply IHmx.
Qed.

Theorem zerop_1st_n_const_coeff_succ : ∀ f L n,
  zerop_1st_n_const_coeff (S n) f L =
  zerop_1st_n_const_coeff 0 f L ||
  zerop_1st_n_const_coeff n (nth_pol 1 f L) (nth_ns 1 f L).
Proof.
intros f L n; simpl.
destruct (ps_zerop K (ps_poly_nth 0 f)); reflexivity.
Qed.

Theorem zerop_1st_n_const_coeff_succ2 : ∀ f L n,
  zerop_1st_n_const_coeff (S n) f L =
  zerop_1st_n_const_coeff n f L ||
  zerop_1st_n_const_coeff 0 (nth_pol (S n) f L) (nth_ns (S n) f L).
Proof.
intros f L n.
revert f L.
induction n; intros.
 simpl.
 destruct (ps_zerop K (ps_poly_nth 0 f)); reflexivity.

 remember (S n) as sn; simpl.
 destruct (ps_zerop K (ps_poly_nth 0 f)) as [H₁| H₁].
  rewrite Heqsn in |- * at 1; simpl.
  destruct (ps_zerop K (ps_poly_nth 0 f)); [ | contradiction ].
  symmetry; apply Bool.orb_true_l.

  remember (ac_root (Φq f L)) as c₁ eqn:Hc₁ .
  remember (next_pol f (β L) (γ L) c₁) as f₁ eqn:Hf₁ .
  remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
  rewrite IHn; simpl.
  remember (nth_pol sn f₁ L₁) as fn eqn:Hfn .
  destruct (ps_zerop K (ps_poly_nth 0 fn)) as [H₂| H₂].
   do 2 rewrite Bool.orb_true_r; reflexivity.

   do 2 rewrite Bool.orb_false_r.
   subst sn; simpl.
   destruct (ps_zerop K (ps_poly_nth 0 f)); [ contradiction | ];
   subst; reflexivity.
Qed.

Theorem zerop_1st_n_const_coeff_false_iff : ∀ f L n,
  zerop_1st_n_const_coeff n f L = false
  ↔ ∀ i : nat, (i <= n)%nat → (ps_poly_nth 0 (nth_pol i f L) ≠ 0)%ps.
Proof.
intros f L n.
split; intros H.
 intros i Hin.
 revert f L i H Hin.
 induction n; intros.
  simpl in H.
  apply Nat.le_0_r in Hin; subst i.
  destruct (ps_zerop K (ps_poly_nth 0 f)); auto.
  discriminate H.

  simpl in H.
  destruct (ps_zerop K (ps_poly_nth 0 f)) as [H₁| H₁].
   discriminate H.

   destruct i; auto; simpl.
   apply IHn; auto.
   apply Nat.succ_le_mono; assumption.

 revert f L H.
 induction n; intros; simpl.
  destruct (ps_zerop K (ps_poly_nth 0 f)) as [H₁| H₁]; auto.
  pose proof (H O (Nat.le_refl 0)) as H₂.
  contradiction.

  destruct (ps_zerop K (ps_poly_nth 0 f)) as [H₁| H₁].
   pose proof (H O (Nat.le_0_l (S n))) as H₂.
   contradiction.

   apply IHn; intros i Hin.
   apply Nat.succ_le_mono, H in Hin; assumption.
Qed.

Theorem nth_c_n : ∀ f₁ L₁ fn Ln n,
  fn = nth_pol n f₁ L₁
  → Ln = nth_ns n f₁ L₁
  → nth_c n f₁ L₁ = ac_root (Φq fn Ln).
Proof.
intros f₁ L₁ fn Ln n Hfn HLn.
revert f₁ L₁ fn Ln Hfn HLn.
induction n; intros.
 simpl in Hfn, HLn; simpl.
 subst fn Ln; reflexivity.

 simpl in Hfn, HLn; simpl.
 remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
 remember (next_pol f₁ (β L₁) (γ L₁) c₁) as f₂ eqn:Hf₂ .
 remember (option_get phony_ns (newton_segments f₂)) as L₂ eqn:HL₂ .
 apply IHn; assumption.
Qed.

Theorem nth_pol_n : ∀ f L c f₁ L₁ fn Ln cn n,
  c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → fn = nth_pol n f L
  → Ln = nth_ns n f L
  → cn = ac_root (Φq fn Ln)
  → nth_pol n f₁ L₁ = next_pol fn (β Ln) (γ Ln) cn.
Proof.
intros f₁ L₁ c₁ f₂ L₂ fn Ln cn n.
intros Hc₁ Hf₂ HL₂ Hfn HLn Hcn.
revert f₁ L₁ c₁ f₂ L₂ fn Ln cn Hc₁ Hf₂ HL₂ Hfn HLn Hcn.
induction n; intros.
 simpl in Hfn, HLn; simpl.
 subst fn Ln f₂ c₁ cn; reflexivity.

 simpl in Hfn, HLn; simpl.
 remember (ac_root (Φq f₂ L₂)) as c₂ eqn:Hc₂ .
 remember (next_pol f₂ (β L₂) (γ L₂) c₂) as f₃ eqn:Hf₃ .
 remember (option_get phony_ns (newton_segments f₃)) as L₃ eqn:HL₃ .
 rewrite <- Hc₁, <- Hf₂, <- HL₂ in Hfn, HLn.
 eapply IHn; eauto .
Qed.

Theorem nth_ns_n : ∀ f L c f₁ L₁ fn Ln cn nfn n,
  c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → fn = nth_pol n f L
  → Ln = nth_ns n f L
  → cn = ac_root (Φq fn Ln)
  → nfn = next_pol fn (β Ln) (γ Ln) cn
  → nth_ns n f₁ L₁ = option_get phony_ns (newton_segments nfn).
Proof.
intros f L c f₁ L₁ fn Ln cn nfn n.
intros Hc Hf₁ HL₁ Hfn HLn Hcn Hnfn.
revert f L c f₁ L₁ fn Ln cn nfn Hc Hf₁ HL₁ Hfn HLn Hcn
 Hnfn.
induction n; intros.
 simpl in Hfn, HLn; simpl.
 subst fn Ln nfn f₁ L₁ c cn.
 reflexivity.

 simpl in Hfn, HLn; simpl.
 rewrite <- Hc, <- Hf₁, <- HL₁ in Hfn, HLn.
 remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
 remember (next_pol f₁ (β L₁) (γ L₁) c₁) as f₂ eqn:Hf₂ .
 remember (option_get phony_ns (newton_segments f₂)) as L₂.
 rename HeqL₂ into HL₂.
 eapply IHn with (c := c₁); eauto .
Qed.

Theorem nth_r_n : ∀ f L f₁ L₁ c₁ n,
  f₁ = nth_pol n f L
  → L₁ = nth_ns n f L
  → c₁ = nth_c n f L
  → nth_r n f L = root_multiplicity acf c₁ (Φq f₁ L₁).
Proof.
intros f L f₁ L₁ c₁ n Hf₁ HL₁ Hc₁.
revert f L f₁ L₁ c₁ Hf₁ HL₁ Hc₁.
induction n; intros; [ subst; reflexivity | simpl ].
apply IHn; subst; reflexivity.
Qed.

Theorem nth_γ_n : ∀ f L n Ln jn αjn kn αkn,
  Ln = nth_ns n f L
  → ini_pt Ln = (jn, αjn)
  → fin_pt Ln = (kn, αkn)
  → nth_γ n f L = (αjn - αkn) / (Qnat kn - Qnat jn).
Proof.
intros f L n Ln jm αjn kn αkn HLn Hini Hfin.
revert f L Ln jm αjn kn αkn HLn Hini Hfin.
induction n; intros.
 simpl in HLn; simpl.
 subst Ln; unfold γ; simpl.
 rewrite Hini, Hfin; simpl.
 reflexivity.

 simpl in HLn; simpl.
 eapply IHn; eauto .
Qed.

Theorem zerop_1st_n_const_coeff_true_if : ∀ f L b,
  zerop_1st_n_const_coeff b f L = true
  → ∀ n, zerop_1st_n_const_coeff (b + n) f L = true.
Proof.
intros f L b Hz n.
revert f L Hz n.
induction b; intros.
 simpl.
 revert f L Hz.
 induction n; intros; auto.
 simpl in Hz; simpl.
 destruct (ps_zerop K (ps_poly_nth 0 f)); auto.
 discriminate Hz.

 simpl in Hz; simpl.
 destruct (ps_zerop K (ps_poly_nth 0 f)); auto.
Qed.

Theorem root_head_from_cγ_list_succ : ∀ f L b n i,
  zerop_1st_n_const_coeff (b + i) f L = false
  → (root_head_from_cγ_list f L b (S n) i =
     root_head_from_cγ_list f L b n i +
      (if zerop_1st_n_const_coeff (b + i + S n) f L then 0
       else
         ps_monom (nth_c (b + i + S n) f L)
           (γ_sum b (i + S n) f L)))%ps.
Proof.
intros f L b n i Hz; simpl.
revert b i Hz.
induction n; intros; simpl.
 symmetry; rewrite rng_add_0_r; symmetry.
 rewrite Nat.add_1_r.
 remember (zerop_1st_n_const_coeff (S (b + i)) f L) as z₁ eqn:Hz₁ .
 symmetry in Hz₁.
 rewrite Nat.add_succ_r.
 destruct z₁.
  rewrite zerop_1st_n_const_coeff_succ2 in Hz₁.
  rewrite Hz, Bool.orb_false_l in Hz₁.
  remember (nth_pol (S (b + i)) f L) as p.
  simpl in Hz₁.
  destruct (ps_zerop K (ps_poly_nth 0 p)) as [H₂| H₂]; subst p.
   reflexivity.

   discriminate Hz₁.

  apply zerop_1st_n_const_coeff_false_iff with (i := S (b + i)) in Hz₁.
   remember (nth_pol (S (b + i)) f L) as p.
   destruct (ps_zerop K (ps_poly_nth 0 p)) as [H₂| H₂]; subst p.
    contradiction.

    rewrite rng_add_0_r, Nat.add_1_r; reflexivity.

   reflexivity.

 rewrite <- rng_add_assoc; simpl.
 apply rng_add_compat_l; simpl.
 remember (nth_pol (b + S i) f L) as p.
 destruct (ps_zerop K (ps_poly_nth 0 p)) as [H₁| H₁]; subst p.
  rewrite rng_add_0_l.
  remember (zerop_1st_n_const_coeff (b + i + S (S n)) f L) as z₁ eqn:Hz₁ .
  symmetry in Hz₁.
  destruct z₁; [ reflexivity | idtac ].
  rewrite zerop_1st_n_const_coeff_false_iff in Hz₁.
  assert (H : (b + S i <= b + i + S (S n))%nat) by fast_omega .
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

Theorem root_head_succ : ∀ f L b n,
  zerop_1st_n_const_coeff b f L = false
  → (root_head b (S n) f L =
     root_head b n f L +
     if zerop_1st_n_const_coeff (b + S n) f L then 0
     else ps_monom (nth_c (b + S n) f L) (γ_sum b (S n) f L))%ps.
Proof.
intros f L b n Hz.
unfold root_head; rewrite Hz.
rewrite root_head_from_cγ_list_succ.
 rewrite Nat.add_0_r, Nat.add_0_l.
 reflexivity.

 rewrite Nat.add_0_r; assumption.
Qed.

Theorem root_head_from_cγ_list_succ_r : ∀ f L f₁ L₁ c n i,
  c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → zerop_1st_n_const_coeff n f₁ L₁ = false
  → (ps_poly_nth 0 f₁ ≠ 0)%ps
  → (root_head_from_cγ_list f L 0 n (S i) =
      ps_monom 1%K (γ L) * root_head_from_cγ_list f₁ L₁ 0 n i)%ps.
Proof.
intros f L f₁ L₁ c n i Hc Hf₁ HL₁ Hnz Hnz₁.
revert f L f₁ L₁ c i Hc Hf₁ HL₁ Hnz Hnz₁.
induction n; intros.
 simpl.
 unfold γ_sum; simpl.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite summation_shift; [ idtac | apply le_n_S, Nat.le_0_l ].
 rewrite Nat_sub_succ_1.
 do 2 rewrite rng_add_0_r; simpl.
 rewrite <- Hc, <- Hf₁, <- HL₁.
 rewrite rng_add_comm.
 rewrite ps_monom_add_r.
 apply ps_mul_comm.

 simpl in Hnz.
 destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₁| H₁].
  discriminate Hnz.

  remember (S i) as si; simpl.
  rewrite <- Hc, <- Hf₁, <- HL₁.
  subst si; simpl.
  rewrite <- Hc, <- Hf₁, <- HL₁.
  remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
  remember (next_pol f₁ (β L₁) (γ L₁) c₁) as f₂ eqn:Hf₂ .
  remember (option_get phony_ns (newton_segments f₂)) as L₂.
  unfold γ_sum; simpl.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite summation_shift; [ idtac | apply le_n_S, Nat.le_0_l ].
  rewrite Nat_sub_succ_1.
  destruct (ps_zerop K (ps_poly_nth 0 (nth_pol i f₂ L₂))) as [H₂| H₂].
   do 2 rewrite rng_add_0_r.
   rewrite rng_add_comm.
   rewrite ps_monom_add_r; simpl.
   rewrite <- Hc, <- Hf₁, <- HL₁.
   apply ps_mul_comm.

   simpl.
   rewrite <- Hc, <- Hf₁, <- HL₁.
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
    rewrite <- Hc₁, <- Hf₂, <- HeqL₂.
    apply Hnz, Nat.lt_le_incl; auto.
Qed.

Theorem apply_nth_pol : ∀ f L y n,
  let qr := Q_ring in
  zerop_1st_n_const_coeff n f L = false
  → (ps_pol_apply f
       (root_head 0 n f L + ps_monom 1%K (γ_sum 0 n f L) * y) =
     ps_monom 1%K (Σ (i = 0, n), β (nth_ns i f L)) *
     ps_pol_apply (nth_pol (S n) f L) y)%ps.
Proof.
intros; revert H; intros Hnz.
revert f L y Hnz.
induction n; intros.
 unfold root_head; simpl.
 unfold γ_sum, summation; simpl.
 unfold next_pol; simpl.
 unfold ps_pol_apply; simpl.
 unfold apply_poly; simpl.
 unfold next_lap; simpl.
 remember (ac_root (Φq f L)) as c eqn:Hc .
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
 destruct (ps_zerop K (ps_poly_nth 0 f)) as [H₁| H₁].
  discriminate Hnz.

  do 2 rewrite rng_add_0_r.
  rewrite rng_add_comm; reflexivity.

 simpl in Hnz.
 destruct (ps_zerop K (ps_poly_nth 0 f)) as [H₁| H₁].
  discriminate Hnz.

  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite summation_shift; [ idtac | apply le_n_S, Nat.le_0_l ].
  rewrite Nat_sub_succ_1.
  remember (S n) as sn in |- *; simpl.
  remember (ac_root (Φq f L)) as c eqn:Hc .
  remember (next_pol f (β L) (γ L) c) as f₁ eqn:Hf₁ .
  remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
  rewrite ps_monom_add_r.
  rewrite <- rng_mul_assoc.
  subst sn; simpl.
  erewrite nth_pol_n with (f := f₁) (L := L₁); eauto .
  erewrite <- nth_pol_succ; eauto ; [ idtac | erewrite nth_c_n; eauto  ].
  remember (S n) as sn in |- *; simpl.
  unfold root_head; simpl.
  destruct (ps_zerop K (ps_poly_nth 0 f)) as [H₂| H₂].
   contradiction.

   clear H₂.
   rewrite Heqsn in |- * at 1; simpl.
   rewrite <- Hc, <- Hf₁.
   destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₂| H₂].
    rewrite zerop_1st_n_const_coeff_false_iff in Hnz.
    pose proof (Hnz O (Nat.le_0_l n)) as H; contradiction.

    subst sn.
    rewrite <- IHn; auto.
    unfold root_head; simpl.
    destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₃| H₃].
     contradiction.

     clear H₃.
     unfold γ_sum at 1, summation; simpl.
     rewrite rng_add_0_r.
     unfold γ_sum.
     rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
     rewrite summation_shift; [ idtac | apply le_n_S, Nat.le_0_l ].
     rewrite Nat_sub_succ_1; simpl.
     rewrite <- Hc, <- Hf₁, <- HL₁.
     rewrite ps_monom_add_r.
     remember Σ (i = 0, n), nth_γ i f₁ L₁ as sγ eqn:Hsγ .
     rewrite <- ps_mul_assoc.
     remember (ps_monom 1%K sγ * y)%ps as u eqn:Hu .
     rewrite Hf₁ in |- * at 1; simpl.
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
  (∀ i : nat, (i <= n)%nat → x < f i)
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
 apply Q.add_lt_le_compat.
  apply IHn.
  intros i Hin; apply Hi.
  apply Nat.le_le_succ_r; auto.

  apply Q.lt_le_incl.
  apply Hi; reflexivity.
Qed.

Theorem order_pol_apply_nonneg : ∀ f y,
  (∀ a, a ∈ al f → (0 ≤ order a)%Qbar)
  → (0 ≤ order y)%Qbar
  → (0 ≤ order (ps_pol_apply f y))%Qbar.
Proof.
intros f y Ha Hy.
unfold ps_pol_apply, apply_poly.
remember (al f) as la; clear Heqla.
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

Fixpoint lowest_with_zero_1st_const_coeff n f L :=
  match n with
  | O => O
  | S n' =>
      if ps_zerop _ (ps_poly_nth 0 f) then O
      else
        let f₁ := next_pol f (β L) (γ L) (ac_root (Φq f L)) in
        let L₁ := option_get phony_ns (newton_segments f₁) in
        S (lowest_with_zero_1st_const_coeff n' f₁ L₁)
  end.

Theorem lowest_zerop_1st_n_const_coeff : ∀ f L n,
  zerop_1st_n_const_coeff n f L = true
  → ∃ i, i = lowest_with_zero_1st_const_coeff n f L ∧
    (i <= n)%nat ∧
    (i = O ∨ zerop_1st_n_const_coeff (pred i) f L = false) ∧
    zerop_1st_n_const_coeff i f L = true.
Proof.
intros f L n Hz.
remember (lowest_with_zero_1st_const_coeff n f L) as i eqn:Hi.
exists i; split; [ reflexivity | ].
revert f L i Hz Hi.
induction n; intros.
 simpl in Hi; subst i.
 split; [ reflexivity |  ].
 split; [ left; reflexivity | assumption ].

 simpl in Hi, Hz.
 remember (ps_zerop K (ps_poly_nth 0 f)) as t eqn:Ht .
 destruct t as [t| t].
  subst i.
  split; [ apply Nat.le_0_l |  ].
  split; [ left; reflexivity | simpl; rewrite <- Ht; reflexivity ].

  destruct i; [ discriminate Hi |  ].
  remember (ac_root (Φq f L)) as c eqn:Hc .
  remember (next_pol f (β L) (γ L) c) as f₁ eqn:Hf₁ ; subst c.
  remember (option_get phony_ns (newton_segments f₁)) as L₁ eqn:HL₁ .
  apply Nat.succ_inj in Hi.
  pose proof (IHn f₁ L₁ i Hz Hi) as H.
  destruct H as (Hin, (Hip, Hii)).
  split; [ rewrite <- Nat.succ_le_mono; assumption | simpl ].
  destruct Hip as [Hip| Hip].
   split; [ right; simpl |  ].
    subst i; simpl.
    rewrite Hip; simpl.
    rewrite <- Ht; reflexivity.

    rewrite <- Ht, <- Hf₁, <- HL₁; assumption.

   split; [ right; simpl |  ].
    destruct i; simpl; [ rewrite <- Ht; reflexivity |  ].
    rewrite <- Ht, <- Hf₁, <- HL₁; assumption.

    rewrite <- Ht, <- Hf₁, <- HL₁; assumption.
Qed.

Theorem first_null_coeff : ∀ f₁ L₁ i a₁ la₁,
  zerop_1st_n_const_coeff i f₁ L₁ = false
  → zerop_1st_n_const_coeff (S i) f₁ L₁ = true
  → al (nth_pol (S i) f₁ L₁) = [a₁ … la₁]
  → (a₁ = 0)%ps.
Proof.
intros f₁ L₁ i a₁ la₁ Hnz₁ Hz₁ Hla₁.
revert f₁ L₁ a₁ la₁ Hnz₁ Hz₁ Hla₁.
induction i; intros.
 simpl in Hnz₁, Hz₁, Hla₁.
 destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₁| H₁].
  discriminate Hnz₁.

  remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
  remember (next_pol f₁ (β L₁) (γ L₁) c₁) as f₂ eqn:Hf₂ .
  remember (option_get phony_ns (newton_segments f₂)) as L₂ eqn:HL₂ .
  destruct (ps_zerop K (ps_poly_nth 0 f₂)) as [H₂| H₂].
   unfold ps_poly_nth, ps_lap_nth in H₂; simpl in H₂.
   unfold next_pol in Hf₂.
   rewrite Hla₁ in Hf₂.
   rewrite Hf₂ in H₂; simpl in H₂.
   assumption.

   discriminate Hz₁.

 remember (S i) as si; simpl in Hz₁, Hla₁; subst si.
 simpl in Hnz₁.
 destruct (ps_zerop K (ps_poly_nth 0 f₁)) as [H₁| H₁].
  discriminate Hnz₁.

  remember (ac_root (Φq f₁ L₁)) as c₁ eqn:Hc₁ .
  remember (next_pol f₁ (β L₁) (γ L₁) c₁) as f₂ eqn:Hf₂ .
  remember (option_get phony_ns (newton_segments f₂)) as L₂ eqn:HL₂ .
  eapply IHi; eauto .
Qed.

Theorem a₀_0_root_0 : ∀ f,
  (ps_poly_nth 0 f = 0)%ps
  → (ps_pol_apply f 0 = 0)%ps.
Proof.
intros f H.
unfold ps_pol_apply, apply_poly, apply_lap; simpl.
unfold ps_poly_nth in H.
destruct (al f) as [| a la]; [ reflexivity | simpl ].
unfold ps_lap_nth in H; simpl in H.
rewrite rng_mul_0_r, rng_add_0_l; assumption.
Qed.

Theorem root_when_fin : ∀ f L n,
  zerop_1st_n_const_coeff (pred n) f L = false
  → zerop_1st_n_const_coeff n f L = true
  → (ps_pol_apply f (root_head 0 (pred n) f L) = 0)%ps.
Proof.
intros f L n Hnz Hz.
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
 remember (al (nth_pol sn f L)) as la eqn:Hla .
 symmetry in Hla.
 destruct la as [| a]; simpl.
  rewrite rng_mul_0_r; reflexivity.

  rewrite rng_mul_0_r, rng_add_0_l; subst sn.
  rewrite first_null_coeff with (a₁ := a); eauto .
  rewrite rng_mul_0_r; reflexivity.
Qed.

Theorem no_newton_segments : ∀ f,
  (ps_poly_nth 0 f ≠ 0)%ps
  → newton_segments f = None
  → (∀ i, (0 < i)%nat → (ps_poly_nth i f = 0)%ps).
Proof.
(* perhaps simplifiable *)
intros f Hnz HL i Hi.
destruct i; [ exfalso; revert Hi; apply Nat.lt_irrefl | idtac ].
clear Hi.
unfold newton_segments in HL.
unfold lower_convex_hull_points in HL.
unfold points_of_ps_polynom in HL.
unfold points_of_ps_lap in HL.
remember (al f) as la eqn:Hla .
symmetry in Hla.
unfold ps_poly_nth.
unfold ps_poly_nth in Hnz.
rewrite Hla in Hnz; rewrite Hla.
clear f Hla.
progress unfold points_of_ps_lap_gen in HL.
(*
unfold power_list in HL.
*)
remember (pair_rec (λ (pow : nat) (ps : puiseux_series α), (pow, ps))) as f.
progress unfold ps_lap_nth in Hnz.
progress unfold ps_lap_nth.
revert la Hnz HL.
induction i; intros. {
  destruct la as [| a]. {
    exfalso; apply Hnz; reflexivity.
  }
  simpl in Hnz; simpl.
  simpl in HL.
  remember (f (O, a)) as fa.
  rewrite Heqf in Heqfa.
  simpl in Heqfa.
  unfold pair_rec in Heqfa; simpl in Heqfa.
  subst fa; simpl in HL.
  apply order_fin in Hnz.
  remember (order a) as oa.
  symmetry in Heqoa.
  destruct oa as [oa| ]; [ idtac | exfalso; apply Hnz; reflexivity ].
  simpl in HL.
  remember (filter_finite_ord (power_list 1 la)) as pts.
  symmetry in Heqpts.
  destruct pts; [ idtac | discriminate HL ].
  clear HL Hnz.
  destruct la as [| b]; [ reflexivity | simpl ].
  simpl in Heqpts.
  remember (f (1%nat, b)) as fb.
  rewrite Heqf in Heqfb.
  unfold pair_rec in Heqfb.
  simpl in Heqfb.
  subst fb; simpl in Heqpts.
  remember (order b) as ob.
  symmetry in Heqob.
  destruct ob as [ob| ]; [ discriminate Heqpts | ].
  apply order_inf; assumption.
}
destruct la as [| a]; [ reflexivity | simpl ].
simpl in Hnz.
simpl in HL.
remember (f (O, a)) as fa.
rewrite Heqf in Heqfa.
simpl in Heqfa.
progress unfold pair_rec in Heqfa; simpl in Heqfa.
subst fa; simpl in HL.
apply order_fin in Hnz.
remember (order a) as oa.
symmetry in Heqoa.
destruct oa as [oa| ]; [ idtac | exfalso; apply Hnz; reflexivity ].
simpl in HL.
remember (filter_finite_ord (power_list 1 la)) as pts.
symmetry in Heqpts.
destruct pts; [ idtac | discriminate HL ].
clear HL.
clear Hnz.
revert Heqf Heqpts; clear; intros.
remember 1%nat as pow; clear Heqpow.
revert i pow Heqpts.
induction la as [| a]; intros; [ reflexivity | cbn ].
simpl in Heqpts.
remember (f (pow, a)) as fa.
rewrite Heqf in Heqfa.
unfold pair_rec in Heqfa.
simpl in Heqfa.
subst fa; simpl in Heqpts.
remember (order a) as oa.
symmetry in Heqoa.
destruct oa as [oa| ]; [ discriminate Heqpts | simpl ].
destruct i. {
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
}
eapply IHla; eauto .
Qed.

Theorem root_multiplicity_0 : ∀ c cf,
  c = ac_root cf
  → root_multiplicity acf c cf = 0%nat
  → (degree fld_zerop cf = 0)%nat.
Proof.
intros c cf Hc Hr.
unfold root_multiplicity in Hr.
unfold degree, apply_poly.
remember (al cf) as la.
symmetry in Heqla.
destruct la as [| a]; [ reflexivity | simpl ].
simpl in Hr.
unfold lap_mod_deg_1 in Hr; simpl in Hr.
destruct (fld_zerop (apply_lap la c * c + a)%K) as [H₁| H₁].
 discriminate Hr.

 remember (degree fld_zerop cf) as deg eqn:Hdeg .
 symmetry in Hdeg.
 destruct deg.
  unfold degree in Hdeg.
  rewrite Heqla in Hdeg.
  simpl in Hdeg.
  assumption.

  assert (degree fld_zerop cf ≥ 1)%nat as H.
   rewrite Hdeg; apply le_n_S, Nat.le_0_l.

   clear Hdeg.
   apply ac_prop_root in H.
   rewrite <- Hc in H.
   unfold apply_poly in H.
   rewrite Heqla in H; simpl in H.
   contradiction.
Qed.

Theorem degree_eq_0_if : ∀ cf,
  degree fld_zerop cf = O
  → (cf = POL [])%pol ∨ (∃ a, (a ≠ 0)%K ∧ (cf = POL [a])%pol).
Proof.
intros cf Hdeg.
unfold degree in Hdeg.
unfold eq_poly; simpl.
remember (al cf) as la; clear Heqla.
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

  clear cf.
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

Theorem multiplicity_neq_0 : ∀ f L c,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → root_multiplicity acf c (Φq f L) ≠ O.
Proof.
intros f L c HL Hc Hr.
apply root_multiplicity_0 in Hr; eauto .
apply degree_eq_0_if in Hr.
destruct Hr as [Hr| Hr]. {
  unfold Φq in Hr; simpl in Hr.
  rewrite Nat.sub_diag in Hr; simpl in Hr.
  unfold eq_poly in Hr; simpl in Hr.
  remember (ini_pt L) as j eqn:Hini.
  destruct j as (j, αj).
  symmetry in Hini.
  cbn in Hr.
  apply lap_eq_cons_nil_inv in Hr.
  destruct Hr as (Hoj, Hcf).
  exfalso; revert Hoj.
  eapply ord_coeff_non_zero_in_newt_segm; eauto .
  left; eassumption.
}
destruct Hr as (a, (Ha, Hcf)).
unfold Φq in Hcf; simpl in Hcf.
remember (ini_pt L) as j eqn:Hini.
destruct j as (j, αj).
symmetry in Hini.
simpl in Hcf.
rewrite Nat.sub_diag in Hcf.
simpl in Hcf.
unfold eq_poly in Hcf; simpl in Hcf.
apply lap_eq_cons_inv in Hcf.
destruct Hcf as (Hoa, Hcf).
remember (oth_pts L) as opts eqn:Hopts .
symmetry in Hopts.
destruct opts as [| pt]. {
  simpl in Hcf.
  remember (fin_pt L) as k eqn:Hfin.
  destruct k as (k, αk).
  symmetry in Hfin.
  simpl in Hcf.
  remember (k - S j)%nat as kj.
  clear Heqkj.
  induction kj. {
    simpl in Hcf.
    apply lap_eq_cons_nil_inv in Hcf.
    destruct Hcf as (Hoc, _).
    exfalso; revert Hoc.
    eapply ord_coeff_non_zero_in_newt_segm; eauto .
    rewrite Hopts; simpl.
    right; left; eassumption.
  }
  simpl in Hcf.
  apply lap_eq_cons_nil_inv in Hcf.
  destruct Hcf as (_, Hcf).
  apply IHkj in Hcf.
  assumption.
}
simpl in Hcf.
destruct pt as (h, αh).
simpl in Hcf.
remember (h - S j)%nat as hj.
clear Heqhj.
induction hj. {
  simpl in Hcf.
  apply lap_eq_cons_nil_inv in Hcf.
  destruct Hcf as (Hoc, _).
  exfalso; revert Hoc.
  eapply ord_coeff_non_zero_in_newt_segm; eauto .
  right; apply List.in_or_app; left.
  now rewrite Hopts; left.
}
simpl in Hcf.
apply lap_eq_cons_nil_inv in Hcf.
destruct Hcf as (_, Hcf).
apply IHhj in Hcf.
assumption.
Qed.

End theorems.
