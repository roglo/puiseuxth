(* AlgCloCharPol.v *)

Require Import Utf8 QArith NPeano ArithRing.

Require Import Misc.
Require Import Field2.
Require Import ConvexHull.
Require Import Newton.
Require Import Fsummation.
Require Import Fpolynomial.
Require Import Puiseux_base.
Require Import Puiseux_series.
Require Import CharactPolyn.

Set Implicit Arguments.

(* euclidean division of a polynomial by (x - c) *)

Fixpoint lap_mod_div_deg_1 α (r : ring α) la c :=
  match la with
  | [] => []
  | [a₁ … la₁] => [apply_lap la c … lap_mod_div_deg_1 r la₁ c]
  end.

Definition lap_div_deg_1 α {R : ring α} la c :=
  match lap_mod_div_deg_1 R la c with
  | [] => []
  | [m … ml] => ml
  end.

Definition lap_mod_deg_1 α {R : ring α} la c :=
  match lap_mod_div_deg_1 R la c with
  | [] => 0%K
  | [m … ml] => m
  end.

Fixpoint comb n k :=
  match k with
  | 0%nat => 1%nat
  | S k₁ =>
      match n with
      | 0%nat => 0%nat
      | S n₁ => (comb n₁ k₁ + comb n₁ k)%nat
      end
  end.

Fixpoint rng_mul_nat α (r : ring α) n x :=
  match n with
  | O => 0%K
  | S n₁ => (rng_mul_nat r n₁ x + x)%K
  end.

Theorem comb_lt : ∀ n k, (n < k)%nat → comb n k = 0%nat.
Proof.
intros n k Hnk.
revert k Hnk.
induction n; intros; simpl.
 destruct k; [ exfalso; revert Hnk; apply Nat.nlt_0_r | auto ].

 destruct k; [ exfalso; revert Hnk; apply Nat.nlt_0_r | auto ].
 apply Nat.succ_lt_mono in Hnk.
 rewrite IHn; [ idtac | assumption ].
 rewrite IHn; [ reflexivity | idtac ].
 apply Nat.lt_lt_succ_r; assumption.
Qed.

Theorem comb_id : ∀ n, comb n n = 1%nat.
Proof.
intros n.
induction n; [ reflexivity | simpl ].
rewrite IHn, comb_lt; [ idtac | apply Nat.lt_succ_r; reflexivity ].
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem rng_mul_nat_1_l : ∀ α (r : ring α) a, (rng_mul_nat r 1 a = a)%K.
Proof. intros α r a; simpl; rewrite rng_add_0_l; reflexivity. Qed.

Theorem comb_0_r : ∀ i, comb i 0 = 1%nat.
Proof. intros i; destruct i; reflexivity. Qed.

Theorem comb_1_r : ∀ n, comb n 1 = n.
Proof.
intros n.
induction n; [ reflexivity | simpl ].
rewrite comb_0_r, IHn; reflexivity.
Qed.

Add Parametric Morphism α (R : ring α) : (@apply_lap _ R)
  with signature lap_eq ==> rng_eq ==> rng_eq
  as apply_lap_morph.
Proof.
intros la lb Hab x y Hxy.
unfold apply_lap.
revert lb Hab x y Hxy.
induction la as [| a]; intros; simpl.
 revert x y Hxy.
 induction lb as [| b]; intros; [ reflexivity | simpl ].
 apply lap_eq_nil_cons_inv in Hab.
 destruct Hab as (Hb, Hlb).
 rewrite Hb, rng_add_0_r.
 rewrite <- IHlb; try eassumption.
 rewrite rng_mul_0_l; reflexivity.

 destruct lb as [| b].
  apply lap_eq_cons_nil_inv in Hab.
  destruct Hab as (Ha, Hla).
  rewrite Ha, rng_add_0_r; simpl.
  rewrite IHla; try eassumption; simpl.
  rewrite rng_mul_0_l; reflexivity.

  simpl.
  apply lap_eq_cons_inv in Hab.
  destruct Hab as (Hab, Hlab).
  rewrite Hab, Hxy.
  rewrite IHla; try eassumption.
  reflexivity.
Qed.

Add Parametric Morphism α (R : ring α) : (@apply_poly _ R)
  with signature eq_poly ==> rng_eq ==> rng_eq
  as apply_poly_morph.
Proof.
intros p₁ p₂ Hpp v₁ v₂ Hvv.
unfold eq_poly in Hpp.
unfold apply_poly.
rewrite Hpp, Hvv; reflexivity.
Qed.

Theorem rng_mul_nat_add_distr_r : ∀ α (r : ring α) a m n,
  (rng_mul_nat r (m + n) a = rng_mul_nat r m a + rng_mul_nat r n a)%K.
Proof.
intros α r a m n.
revert a n.
induction m; intros; simpl.
 rewrite rng_add_0_l; reflexivity.

 rewrite IHm.
 apply rng_add_shuffle0.
Qed.

Add Parametric Morphism α (r : ring α) : (rng_mul_nat r)
  with signature eq ==> rng_eq ==> rng_eq
  as rng_mul_nat_morph.
Proof.
intros n a b Hab.
induction n; [ reflexivity | simpl ].
rewrite IHn, Hab; reflexivity.
Qed.

Theorem lap_eq_map_ext : ∀ α (r : ring α) A g h,
  (∀ a : A, (g a = h a)%K)
  → ∀ la : list A, (List.map g la = List.map h la)%lap.
Proof.
intros α r A g h Hgh la.
induction la as [| a]; [ reflexivity | simpl ].
constructor; [ apply Hgh | assumption ].
Qed.

Theorem rng_mul_nat_assoc : ∀ α (R : ring α) n a b,
  (rng_mul_nat R n a * b = rng_mul_nat R n (a * b))%K.
Proof.
intros α R n a b.
induction n; simpl.
 rewrite rng_mul_0_l; reflexivity.

 rewrite rng_mul_add_distr_r, IHn; reflexivity.
Qed.

Theorem apply_lap_add : ∀ α (r : ring α) la lb x,
  (apply_lap (lap_add la lb) x =
   apply_lap la x + apply_lap lb x)%K.
Proof.
intros α r la lb x.
revert lb x.
induction la as [| a]; intros; simpl.
 rewrite rng_add_0_l; reflexivity.

 destruct lb as [| b]; simpl.
  rewrite rng_add_0_r; reflexivity.

  rewrite IHla.
  do 2 rewrite rng_add_assoc.
  apply rng_add_compat_r.
  rewrite rng_add_shuffle0.
  rewrite rng_mul_add_distr_r; reflexivity.
Qed.

Theorem apply_lap_single : ∀ α (r : ring α) a lb x,
  (apply_lap (lap_mul [a] lb) x = a * apply_lap lb x)%K.
Proof.
intros α r a lb x.
induction lb as [| b].
 simpl; rewrite rng_mul_0_r; reflexivity.

 rewrite lap_mul_cons_r; simpl.
 rewrite summation_only_one, rng_add_0_r, IHlb.
 rewrite rng_mul_add_distr_l, rng_mul_assoc; reflexivity.
Qed.

Theorem apply_lap_mul : ∀ α (r : ring α) la lb x,
  (apply_lap (lap_mul la lb) x =
   apply_lap la x * apply_lap lb x)%K.
Proof.
intros α r la lb x.
revert lb x.
induction la as [| a]; intros; simpl.
 rewrite lap_mul_nil_l, rng_mul_0_l; reflexivity.

 destruct lb as [| b]; simpl.
  rewrite lap_mul_nil_r, rng_mul_0_r; reflexivity.

  rewrite lap_mul_cons; simpl.
  rewrite apply_lap_add; simpl.
  rewrite rng_add_0_r.
  rewrite apply_lap_add.
  rewrite IHla.
  rewrite IHla.
  simpl.
  rewrite rng_mul_0_l, rng_add_0_l.
  do 3 rewrite rng_mul_add_distr_r.
  do 2 rewrite rng_mul_add_distr_l.
  do 2 rewrite rng_mul_assoc.
  rewrite rng_add_assoc.
  apply rng_add_compat_r.
  rewrite rng_add_comm, rng_add_assoc.
  do 2 rewrite <- rng_add_assoc.
  apply rng_add_compat.
   apply rng_mul_compat_r.
   apply rng_mul_shuffle0.

   apply rng_add_compat.
    apply rng_mul_shuffle0.

    apply rng_mul_compat_r.
    apply apply_lap_single.
Qed.

Theorem apply_lap_compose : ∀ α (r : ring α) la lb x,
  (apply_lap (lap_compose la lb) x =
   apply_lap la (apply_lap lb x))%K.
Proof.
intros α r la lb x.
unfold lap_compose.
revert lb x.
induction la as [| a]; intros; [ reflexivity | simpl ].
rewrite <- IHla; clear.
rewrite apply_lap_add; simpl.
rewrite rng_mul_0_l, rng_add_0_l.
apply rng_add_compat_r.
apply apply_lap_mul.
Qed.

Theorem list_seq_app : ∀ j dj len,
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

Theorem lap_mul_const_l : ∀ α (r : ring α) a lb,
  lap_eq (lap_mul [a] lb) (List.map (rng_mul a) lb).
Proof.
intros α r a lb.
unfold lap_mul; simpl.
induction lb as [| b]; [ reflexivity | simpl ].
rewrite summation_only_one.
constructor; [ reflexivity | idtac ].
rewrite lap_convol_mul_cons_succ; assumption.
Qed.

Theorem poly_compose_compose2 : ∀ α (r : ring α) P Q,
  (P ∘ Q = poly_compose2 P Q)%pol.
Proof.
intros α r P Q.
apply lap_compose_compose2.
Qed.

Theorem nth_mul_deg_1 : ∀ α (r : ring α) a lb k,
  (List.nth (S k) (lap_mul [a; 1 … []] lb) 0 =
   a * List.nth (S k) lb 0 + List.nth k lb 0)%K.
Proof.
intros α r a lb k.
unfold lap_mul.
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
rewrite summation_split_first; [ simpl | apply le_n_S, Nat.le_0_l ].
rewrite all_0_summation_0.
 rewrite rng_mul_1_l, Nat.sub_0_r, rng_add_0_r; reflexivity.

 intros i (Hi, Hik).
 destruct i; [ exfalso; revert Hi; apply Nat.nle_succ_0 | idtac ].
 apply Nat.succ_le_mono in Hi.
 destruct i; [ exfalso; revert Hi; apply Nat.nle_succ_0 | idtac ].
 rewrite match_id, rng_mul_0_l; reflexivity.
Qed.

Theorem rng_mul_nat_mul_swap : ∀ α (r : ring α) n a b,
  (rng_mul_nat r n (a * b) = a * rng_mul_nat r n b)%K.
Proof.
intros α r n a b.
induction n; simpl.
 rewrite rng_mul_0_r; reflexivity.

 rewrite IHn, rng_mul_add_distr_l; reflexivity.
Qed.

(* *)

Fixpoint degree_plus_1_of_list α {R : ring α}
    (zerop : ∀ a, {(a = 0)%K} + {(a ≠ 0)%K}) (l : list α) :=
  match l with
  | [] => O
  | [x … l₁] =>
      match degree_plus_1_of_list zerop l₁ with
      | O => if zerop x then O else 1%nat
      | S n => S (S n)
      end
  end.

Definition degree α {R : ring α} zerop (f : polynomial α) :=
  pred (degree_plus_1_of_list zerop (al f)).

(* actually, field which is:
   - with characteristic 0 or 1
   - algebraically closed *)
Class algeb_closed_field α (ac_ring : ring α) (ac_field : field ac_ring) :=
  { ac_charac_01 : ∀ n, (rng_mul_nat ac_ring (S (S n)) 1 ≠ 0)%K;
    ac_root : polynomial α → α;
    ac_prop_root : ∀ f, degree fld_zerop f ≥ 1
      → (apply_poly f (ac_root f) = 0)%K }.

Definition ac_is_zero α {R : ring α} {K : field R}
  {acf : algeb_closed_field K} (x : α) := if fld_zerop x then True else False.

Fixpoint list_root_multiplicity
    α {r : ring α} {K : field r} (acf : algeb_closed_field K) c la d :=
  match d with
  | O => O
  | S d₁ =>
      if fld_zerop (lap_mod_deg_1 la c) then
        S (list_root_multiplicity acf c (lap_div_deg_1 la c) d₁)
      else O
  end.

Definition root_multiplicity α {r : ring α} {K : field r}
  (acf : algeb_closed_field K) c
    f :=
  list_root_multiplicity acf c (al f) (List.length (al f)).

Fixpoint list_quotient_phi_x_sub_c_pow_r α (R : ring α) la c₁ r :=
  match r with
  | O => la
  | S r₁ => list_quotient_phi_x_sub_c_pow_r R (lap_div_deg_1 la c₁) c₁ r₁
  end.

Definition quotient_phi_x_sub_c_pow_r α {R : ring α} f c₁ r :=
  (POL (list_quotient_phi_x_sub_c_pow_r R (al f) c₁ r))%pol.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Theorem list_nth_mod_div_deg_1 : ∀ la c i,
  (List.nth i (lap_mod_div_deg_1 R la c) 0 =
   apply_lap (List.skipn i la) c)%K.
Proof.
intros la c i; revert i.
induction la as [| a]; intros; simpl.
 rewrite match_id, list_skipn_nil; reflexivity.

 destruct i; [ reflexivity | apply IHla ].
Qed.

Theorem length_lap_mod_div_deg_1 : ∀ l c,
  length (lap_mod_div_deg_1 R l c) = length l.
Proof.
intros l c.
induction l; [ reflexivity | simpl ].
rewrite IHl; reflexivity.
Qed.

Theorem length_list_quotient_phi_x_sub_c_pow_r : ∀ l c r,
  length (list_quotient_phi_x_sub_c_pow_r R l c r) = (length l - r)%nat.
Proof.
intros l c r.
revert l c.
induction r; intros; simpl.
 rewrite Nat.sub_0_r; reflexivity.

 destruct l as [| x]; simpl.
  unfold lap_div_deg_1; simpl.
  rewrite IHr; reflexivity.

  unfold lap_div_deg_1; simpl.
  rewrite IHr.
  rewrite length_lap_mod_div_deg_1; reflexivity.
Qed.

Theorem root_formula : ∀ la c,
  (apply_lap la c = 0)%K
  → (la = [(- c)%K; 1%K … []] * lap_div_deg_1 la c)%lap.
Proof.
intros la c Hc.
unfold lap_div_deg_1.
remember (lap_mod_div_deg_1 R la c) as md eqn:Hmd .
symmetry in Hmd.
destruct md as [| r d].
 rewrite lap_mul_nil_r.
 destruct la as [| a]; [ reflexivity | discriminate Hmd ].

 destruct la as [| a]; [ discriminate Hmd | simpl ].
 simpl in Hmd.
 simpl in Hc.
 injection Hmd; clear Hmd; intros Hd Hr.
 subst d; clear r Hr.
 rename a into a₀.
 apply list_nth_lap_eq; intros i.
 destruct i.
  simpl.
  rewrite summation_only_one.
  destruct la as [| a₁].
   simpl.
   rewrite rng_mul_0_r.
   simpl in Hc.
   rewrite rng_mul_0_l, rng_add_0_l in Hc; assumption.

   simpl in Hc; simpl.
   remember (apply_lap la c * c + a₁)%K as v eqn:Hv .
   rewrite rng_mul_comm in Hc.
   apply rng_add_compat_r with (c := (- c * v)%K) in Hc.
   rewrite rng_add_0_l in Hc.
   rewrite rng_add_comm, rng_add_assoc in Hc.
   rewrite rng_mul_opp_l in Hc.
   rewrite rng_add_opp_l in Hc.
   rewrite rng_add_0_l in Hc.
   rewrite rng_mul_opp_l.
   assumption.

  rewrite nth_mul_deg_1; simpl.
  clear a₀ Hc.
  do 2 rewrite list_nth_mod_div_deg_1.
  revert i.
  induction la as [| a]; intros; simpl.
   rewrite match_id, list_skipn_nil; simpl.
   rewrite rng_mul_0_r, rng_add_0_l; reflexivity.

   destruct i; [ simpl | apply IHla ].
   rewrite rng_add_assoc.
   rewrite rng_mul_opp_l, rng_mul_comm.
   rewrite rng_add_opp_l, rng_add_0_l; reflexivity.
Qed.

Theorem list_root_mult_succ_if : ∀ la d c md n,
  list_root_multiplicity acf c la d = S n
  → lap_mod_div_deg_1 R la c = md
    → d ≠ O ∧ ac_is_zero (lap_mod_deg_1 la c) ∧
      list_root_multiplicity acf c (lap_div_deg_1 la c) (pred d) = n.
Proof.
intros la d c md n Hn Hmd.
destruct d; [ discriminate Hn | simpl in Hn ].
split; [ intros H; discriminate H | idtac ].
unfold ac_is_zero.
destruct (fld_zerop (lap_mod_deg_1 la c)) as [Hz| Hnz].
 split; [ constructor | idtac ].
 apply eq_add_S; assumption.

 discriminate Hn.
Qed.

Theorem list_length_shrink_le : ∀ k (l : list α),
  length (list_shrink k l) ≤ length l.
Proof.
intros k l.
unfold list_shrink.
assert (∀ cnt k₁, length (list_shrink_aux cnt k₁ l) ≤ length l) as H.
 intros cnt k₁.
 revert cnt.
 induction l as [| x]; intros; [ reflexivity | simpl ].
 destruct cnt; simpl.
  apply le_n_S, IHl.

  etransitivity; [ apply IHl | idtac ].
  apply Nat.le_succ_r; left; reflexivity.

 apply H.
Qed.

Theorem degree_plus_1_is_0 : ∀ la,
  degree_plus_1_of_list fld_zerop la = 0%nat
  → lap_eq la [].
Proof.
intros la H.
induction la as [| a]; [ reflexivity | idtac ].
simpl in H.
remember (degree_plus_1_of_list fld_zerop la) as d eqn:Hd .
symmetry in Hd.
destruct d; [ idtac | discriminate H ].
constructor; [ idtac | apply IHla; reflexivity ].
destruct (fld_zerop a); [ assumption | discriminate H ].
Qed.

Theorem lap_eq_nil_nth : ∀ la,
  lap_eq la []
  → ∀ n, (List.nth n la 0 = 0)%K.
Proof.
intros la H n.
revert n.
induction la as [| a]; intros; simpl.
 rewrite match_id; reflexivity.

 apply lap_eq_cons_nil_inv in H.
 destruct H as (Ha, Hla).
 destruct n; [ assumption | idtac ].
 apply IHla; assumption.
Qed.

Theorem all_0_shrink_0 : ∀ la cnt k,
  (∀ n, (List.nth n la 0 = 0)%K)
  → (∀ n, (List.nth n (list_shrink_aux cnt k la) 0 = 0)%K).
Proof.
intros la cnt k H n.
revert cnt k n.
induction la as [| a]; intros; [ destruct n; reflexivity | simpl ].
destruct cnt; simpl.
 destruct n; simpl.
  pose proof (H O); assumption.

  apply IHla; clear n; intros n.
  pose proof (H (S n)); assumption.

 apply IHla; clear n; intros n.
 pose proof (H (S n)); assumption.
Qed.

Theorem cpol_degree_ge_1 : ∀ f L m,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → degree fld_zerop (Φq f L) ≥ 1.
Proof.
intros f L m HL Hm.
remember (Pos.to_nat (q_of_m m (γ L))) as q eqn:Hq .
remember (ini_pt L) as jj eqn:Hj .
destruct jj as (jq, αj); simpl.
remember HL as H; clear HeqH.
apply exists_ini_pt_nat in H.
destruct H as (j, (x, Hx)).
rewrite <- Hj in Hx; injection Hx; clear Hx; intros; subst jq x.
remember HL as Hk; clear HeqHk.
apply exists_fin_pt_nat in Hk.
destruct Hk as (k, (αk, Hk)).
symmetry in Hk.
remember HL as Hdeg; clear HeqHdeg.
eapply phi_degree_is_k_sub_j_div_q in Hdeg; try eassumption.
unfold has_degree in Hdeg.
destruct Hdeg as (Hshr, (Hdeg, Hcnz)).
remember HL as Hqkj; clear HeqHqkj.
eapply q_is_factor_of_h_minus_j with (h := k) in Hqkj; try eassumption.
 destruct Hqkj as (n, Hqkj).
 destruct n.
  simpl in Hqkj.
  exfalso.
  remember HL as H; clear HeqH.
  apply j_lt_k with (j := j) (k := k) in H.
   apply Nat.sub_gt in H; contradiction.

   rewrite <- Hj; simpl.
   rewrite nat_num_Qnat; reflexivity.

   rewrite <- Hk; simpl.
   rewrite nat_num_Qnat; reflexivity.

  rewrite Hqkj in Hdeg, Hcnz.
  rewrite Nat.div_mul in Hdeg; [ idtac | subst q; apply Pos2Nat_ne_0 ].
  rewrite Nat.div_mul in Hcnz; [ idtac | subst q; apply Pos2Nat_ne_0 ].
  unfold pseudo_degree in Hdeg.
  unfold degree.
  remember (al (Φs q f L)) as la eqn:Hla .
  unfold Φs in Hla; simpl in Hla.
  rewrite Nat.sub_diag in Hla; simpl in Hla.
  rewrite <- Hj in Hla; simpl in Hla.
  rewrite nat_num_Qnat in Hla; simpl.
  rewrite Nat.sub_diag, list_pad_0.
  rewrite <- Hj; unfold fst.
  rewrite nat_num_Qnat.
  remember (order_coeff (List.nth j (al f) 0%ps)) as v eqn:Hv .
  remember (oth_pts L ++ [fin_pt L]) as pts eqn:Hpts .
  remember (List.map (term_of_point f) pts) as tl eqn:Htl .
  subst la; simpl.
  remember (make_char_pol R (S j) tl) as cf eqn:Hcf .
  remember (degree_plus_1_of_list fld_zerop cf) as d eqn:Hd .
  symmetry in Hd.
  destruct d; [ exfalso | apply le_n_S, Nat.le_0_l ].
  subst cf.
  remember (Pos.to_nat (q_of_m m (γ L))) as nq.
  remember (make_char_pol R (S j) tl) as cf.
  pose proof (list_length_shrink_le nq [v … cf]) as Hlen.
  remember [v … cf] as vcf.
  rewrite Heqvcf in Hlen at 2.
  simpl in Hlen.
  subst vcf.
  apply degree_plus_1_is_0 in Hd.
  simpl in Hcnz.
  simpl in Hdeg.
  simpl in Hlen.
  apply le_S_n in Hlen.
  apply Hcnz.
  apply all_0_shrink_0; intros p.
  apply lap_eq_nil_nth; assumption.

 apply List.in_or_app; right; left; symmetry; eassumption.
Qed.

Theorem lap_mod_deg_1_apply : ∀ la c,
  (lap_mod_deg_1 la c = 0)%K
  → (apply_lap la c = 0)%K.
Proof.
intros la c Hmod.
destruct la as [| a]; [ reflexivity | assumption ].
Qed.

Theorem list_root_mul_power_quotient : ∀ la c r len,
  list_root_multiplicity acf c la len = r
  → (la =
     [(- c)%K; 1%K … []] ^ r * list_quotient_phi_x_sub_c_pow_r R la c r)%lap.
Proof.
intros la c r len Hmult.
revert la len Hmult.
induction r; intros; simpl.
 rewrite lap_mul_1_l; reflexivity.

 rewrite <- lap_mul_assoc.
 eapply list_root_mult_succ_if in Hmult; [ idtac | reflexivity ].
 destruct Hmult as (_, (Hz, Hmult)).
 rewrite <- IHr; [ idtac | eassumption ].
 apply root_formula.
 apply lap_mod_deg_1_apply.
 unfold ac_is_zero in Hz.
 destruct (fld_zerop (lap_mod_deg_1 la c)) as [H| H].
  rewrite H; reflexivity.

  contradiction.
Qed.

Theorem list_div_x_sub_c_ne_0 : ∀ la c r len,
  not (lap_eq la [])
  → list_root_multiplicity acf c la len = r
    → length la ≤ len
      → (apply_lap (list_quotient_phi_x_sub_c_pow_r R la c r) c ≠ 0)%K.
Proof.
intros la c r len Hla Hmult Hlen.
revert la len Hla Hmult Hlen.
induction r; intros; simpl.
 intros Happ; apply Hla; clear Hla.
 revert la Hmult Hlen Happ.
 induction len; intros.
  destruct la; [ idtac | exfalso; revert Hlen; apply Nat.nle_succ_0 ].
  reflexivity.

  destruct la as [| a]; [ reflexivity | idtac ].
  simpl in Hmult.
  unfold lap_mod_deg_1 in Hmult; simpl in Hmult.
  simpl in Hlen.
  apply le_S_n in Hlen.
  simpl in Happ.
  destruct (fld_zerop (apply_lap la c * c + a)%K).
   discriminate Hmult.

   contradiction.

 destruct len.
  destruct la; [ idtac | exfalso; revert Hlen; apply Nat.nle_succ_0 ].
  exfalso; apply Hla; reflexivity.

  simpl in Hmult.
  destruct (fld_zerop (lap_mod_deg_1 la c)) as [Hz| Hnz].
   apply eq_add_S in Hmult.
   destruct la as [| a]; [ exfalso; apply Hla; reflexivity | idtac ].
   simpl in Hlen.
   apply le_S_n in Hlen.
   eapply IHr.
    intros H; apply Hla; clear Hla.
    unfold lap_div_deg_1 in H; simpl in H.
    unfold lap_mod_deg_1 in Hz; simpl in Hz.
    remember (lap_mod_div_deg_1 R la c) as md eqn:Hmd .
    symmetry in Hmd.
    assert (apply_lap la c = 0)%K as Happ.
     apply lap_mod_deg_1_apply.
     unfold lap_mod_deg_1; simpl.
     rewrite Hmd.
     destruct md as [| d]; [ reflexivity | idtac ].
     apply lap_eq_cons_nil_inv in H.
     destruct H; assumption.

     rewrite Happ in Hz.
     rewrite rng_mul_0_l, rng_add_0_l in Hz.
     constructor; [ assumption | idtac ].
     destruct len.
      destruct la; [ idtac | exfalso; revert Hlen; apply Nat.nle_succ_0 ].
      reflexivity.

      simpl in Hmult.
      unfold lap_div_deg_1 in Hmult; simpl in Hmult.
      revert Hmd H; clear; intros.
      revert md Hmd H.
      induction la as [| a]; intros; [ reflexivity | simpl ].
      constructor.
       simpl in Hmd.
       subst md.
       apply lap_eq_cons_nil_inv in H.
       destruct H as (Happ, H).
       assert (apply_lap la c = 0)%K as Haz.
        apply lap_mod_deg_1_apply.
        unfold lap_mod_deg_1.
        remember (lap_mod_div_deg_1 R la c) as md eqn:Hmd .
        symmetry in Hmd.
        destruct md as [| m]; [ reflexivity | idtac ].
        apply lap_eq_cons_nil_inv in H.
        destruct H; assumption.

        rewrite Haz, rng_mul_0_l, rng_add_0_l in Happ.
        assumption.

       simpl in Hmd.
       subst md.
       apply lap_eq_cons_nil_inv in H.
       destruct H as (Happ, H).
       eapply IHla; [ reflexivity | eassumption ].

    eassumption.

    unfold lap_div_deg_1; simpl.
    revert Hlen; clear; intros.
    revert len Hlen.
    induction la as [| a]; intros; [ apply Nat.le_0_l | simpl ].
    destruct len; [ exfalso; revert Hlen; apply Nat.nle_succ_0 | simpl ].
    simpl in Hlen.
    apply le_S_n in Hlen.
    apply le_n_S, IHla; assumption.

   discriminate Hmult.
Qed.

(* [Walker, p. 100] « If c₁ ≠ 0 is an r-fold root, r ≥ 1, of Φ(z^q) = 0,
   we have:
      Φ(z^q) = (z - c₁)^r Ψ(z), [...] » *)
Theorem phi_zq_eq_z_sub_c₁_psi : ∀ f L c₁ r Ψ,
  r = root_multiplicity acf c₁ (Φq f L)
  → Ψ = quotient_phi_x_sub_c_pow_r (Φq f L) c₁ r
    → (Φq f L = POL [(- c₁)%K; 1%K … []] ^ r * Ψ)%pol.
Proof.
intros f L c r Ψ Hr HΨ.
subst Ψ; simpl.
eapply list_root_mul_power_quotient.
symmetry; eassumption.
Qed.

(* [Walker, p. 100] « If c₁ ≠ 0 is an r-fold root, r ≥ 1, of Φ(z^q) = 0,
   we have:
      Φ(z^q) = (z - c₁)^r Ψ(z), Ψ(c₁) ≠ 0 » *)
Theorem psi_c₁_ne_0 : ∀ f L c₁ r Ψ,
  newton_segments f = Some L
  → r = root_multiplicity acf c₁ (Φq f L)
    → Ψ = quotient_phi_x_sub_c_pow_r (Φq f L) c₁ r
      → (apply_poly Ψ c₁ ≠ 0)%K.
Proof.
intros f L c r Ψ HL Hr HΨ.
remember (Φq f L) as phi eqn:Hphi .
subst Ψ; simpl.
unfold apply_poly; simpl.
unfold root_multiplicity in Hr.
remember (al phi) as la eqn:Hla .
subst phi; rewrite al_Φq in Hla.
symmetry in Hr.
eapply list_div_x_sub_c_ne_0; [ idtac | eassumption | reflexivity ].
rewrite Hla; intros H.
simpl in H.
rewrite Nat.sub_diag in H; simpl in H.
apply lap_eq_cons_nil_inv in H.
destruct H as (H, _).
remember (ini_pt L) as jj eqn:Hj .
destruct jj as (jq, αj); simpl.
remember HL as HH; clear HeqHH.
apply exists_ini_pt_nat in HH.
destruct HH as (j, (x, Hx)).
rewrite <- Hj in Hx; injection Hx; clear Hx; intros; subst jq x.
simpl in H.
revert H.
eapply ord_coeff_non_zero_in_newt_segm; [ eassumption | idtac | idtac ].
 symmetry in Hj.
 left; eassumption.

 rewrite nat_num_Qnat; reflexivity.
Qed.

End theorems.
