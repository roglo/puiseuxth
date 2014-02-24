(* Puiseux.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import ConvexHullMisc.
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
Definition x_power α (fld : field α) q := (ps_monom fld .1 fld q)%K.
Definition var_y α (fld : field α) := [.0 fld; .1 fld … []]%K.

(* pol₁(x,y₁) = x^(-β₁).pol(x,x^γ₁.(c₁ + y₁)) *)
Definition lap_pol₁ α (fld : field α) pol β₁ γ₁ c₁ :=
  lap_mul (ps_field fld) [x_power fld (- β₁)]
    (lap_compose (ps_field fld) pol
       [c_x_power fld c₁ γ₁; x_power fld γ₁ … []]).

Definition pol₁ α (fld : field α) pol β₁ γ₁ c₁ :=
  (POL (lap_pol₁ fld (al pol) β₁ γ₁ c₁))%pol.

(* *)

Definition ā_lap α (fld : field α) h la := (List.nth h la .0 fld)%ps.
Definition ā α (fld : field α) h pol := (ā_lap fld h (al pol)).

Lemma ps_monom_split_mul : ∀ α (f : field α) c pow,
  (ps_monom f c pow .= (ps_field f)
   (ps_monom f c 0 .* f ps_monom f .1 f%K pow)%ps)%K.
Proof.
intros α f c pow.
unfold ps_mul; simpl.
rewrite series_stretch_1, Z.mul_1_r.
unfold cm; simpl.
unfold ps_monom; simpl.
apply mkps_morphism; try reflexivity.
constructor; intros i; simpl.
unfold series_stretch; simpl.
unfold convol_mul; simpl.
destruct i; simpl.
 rewrite summation_only_one; simpl.
 rewrite Nat.mod_0_l; auto.
 rewrite Nat.div_0_l; auto; simpl.
 rewrite fld_mul_1_r; reflexivity.

 rewrite all_0_summation_0; [ reflexivity | idtac ].
 intros j (_, Hj).
 destruct j; simpl.
  rewrite fld_mul_0_r; reflexivity.

  apply le_S_n in Hj.
  destruct (zerop (S j mod Pos.to_nat (Qden pow))) as [H₁| H₁].
   apply Nat.mod_divides in H₁; auto.
   destruct H₁ as (d, Hd).
   rewrite Nat.mul_comm in Hd.
   rewrite Hd, Nat.div_mul; auto.
   destruct d; [ discriminate Hd | simpl ].
   rewrite fld_mul_0_l; reflexivity.

   rewrite fld_mul_0_l; reflexivity.
Qed.

Lemma lap_f₁_eq_x_min_β₁_comp : ∀ α (fld : field α) la β₁ γ₁ c₁ psf,
  psf = ps_field fld
  → lap_eq psf (lap_pol₁ fld la β₁ γ₁ c₁)
      (lap_mul psf [x_power fld (- β₁)]
         (lap_compose psf la
            (lap_mul psf
               [x_power fld γ₁]
               [c_x_power fld c₁ 0; .1 fld%ps … []]))).
Proof.
intros α fld la β₁ γ₁ c₁ psf Hpsf.
unfold lap_pol₁.
rewrite <- Hpsf.
apply lap_mul_compat; [ reflexivity | idtac ].
apply lap_compose_compat; [ reflexivity | idtac ].
unfold lap_mul; simpl.
unfold summation; simpl.
rewrite fld_mul_0_l.
do 3 rewrite fld_add_0_r.
subst psf; simpl.
constructor.
 rewrite ps_mul_comm.
 apply ps_monom_split_mul.

 constructor; [ idtac | reflexivity ].
 rewrite ps_mul_1_r; reflexivity.
Qed.

(* [Walker, p. 100] « f₁(x,y₁) = x^(-β₁).f(x,x^γ₁(c₁+y₁)) » *)
Theorem f₁_eq_x_min_β₁_comp : ∀ α (fld : field α) pol β₁ γ₁ c₁ psf,
  psf = ps_field fld
  → (pol₁ fld pol β₁ γ₁ c₁ .= psf
     POL [x_power fld (- β₁)] .* psf
     poly_compose psf pol
       (POL [x_power fld γ₁] .* psf
        POL [c_x_power fld c₁ 0; .1 fld%ps … []]))%pol.
Proof.
intros α fld pol β₁ γ₁ c₁ psf Hpsf.
apply lap_f₁_eq_x_min_β₁_comp; assumption.
Qed.

bbb.

Theorem zzz : ∀ α (fld : field α) pol ns j k β₁ γ₁ c₁ psf,
  ns ∈ newton_segments fld pol
  → j = nofq (fst (ini_pt ns))
    → k = nofq (fst (fin_pt ns))
      → psf = ps_field fld
        → (pol₁ fld pol β₁ γ₁ c₁ .= psf
           POL [x_power fld (- β₁)] .* psf
           ps_poly_summation fld pol j k
             (λ h,
              POL [(ā fld h pol .* fld x_power fld (Qnat h * γ₁))%ps] .* psf
              (POL [ps_const fld c₁; .1 fld%ps … []]) .^ psf h) .+ psf
           (POL [x_power fld (- β₁)] .* psf
            ps_poly_summation fld pol 0 (pred j)
              (λ l,
               POL [(ā fld l pol .* fld x_power fld (Qnat l * γ₁))%ps] .* psf
               (POL [ps_const fld c₁; .1 fld%ps … []]) .^ psf l) .+ psf
            POL [x_power fld (- β₁)] .* psf
            ps_poly_summation fld pol (S k) (length (al pol))
              (λ l,
               POL [(ā fld l pol .* fld x_power fld (Qnat l * γ₁))%ps] .* psf
               (POL [ps_const fld c₁; .1 fld%ps … []]) .^ psf l)))%pol.
Proof.
intros α fld pol ns j k β₁ γ₁ c₁ psf Hns Hj Hk Hpsf.
bbb.

        → (pol₁ fld f β₁ γ₁ c₁ =
           POL [x_power fld (- β₁)] *
           ps_poly_summation fld pol j k
             (λ h,
              POL [(ā fld h pol * x_power fld (Qnat h * γ₁))%ps] *
              (POL [ps_const fld c₁; .1 fld%ps … []]) ^ h) +
           (POL [x_power fld (- β₁)] *
            ps_poly_summation fld pol 0 (pred j)
              (λ l,
               POL [(ā fld l pol * x_power fld (Qnat l * γ₁))%ps] *
               (POL [ps_const fld c₁; .1 fld%ps … []]) ^ l) +
            POL [x_power fld (- β₁)] *
            ps_poly_summation fld pol (S k) (length (al pol))
              (λ l,
               POL [(ā fld l pol * x_power fld (Qnat l * γ₁))%ps] *
               (POL [ps_const fld c₁; .1 fld%ps … []]) ^ l)))%pol.
Proof.

bbb.

(* rest to be used later perhaps *)

(*
Lemma summation_fold_compat : ∀ α (f : field α) a b c d,
  (a .= f c)%pol
  → (b .= f d)%pol
    → (List.fold_right
         (λ x accu, accu .* f b .+ f {| al := [x] |}) {| al := [] |} 
         (al a) .= f
       List.fold_right
         (λ x accu, accu .* f d .+ f {| al := [x] |}) {| al := [] |} 
         (al c))%pol.
Proof.
intros α f a b c d Hac Hbd.
inversion_clear Hac.
 inversion_clear Hbd; reflexivity.

 simpl; apply poly_add_compat.
  apply poly_mul_compat; [ idtac | assumption ].
  revert l' H0.
  induction l; intros.
   inversion_clear H0; reflexivity.

   inversion_clear H0; simpl.
   apply poly_add_compat.
    apply poly_mul_compat; [ idtac | assumption ].
    apply IHl; assumption.

    constructor; [ assumption | constructor ].

  constructor; [ assumption | constructor ].
Qed.


Add Parametric Morphism α (fld : field α) : (@apply_poly_with_poly α fld)
  with signature eq_poly fld ==> eq_poly fld ==> eq_poly fld
  as apply_poly_with_poly_morph.
Proof.
intros a c Hac b d Hbd.
unfold apply_poly_with_poly, apply_poly.
rewrite summation_fold_compat; try eassumption.
reflexivity.
Qed.

(* exercise... *)

Section field.

Variable α : Type.
Variable acf : algeb_closed_field α.
Let fld := ac_field acf.

(* c.x^γ + y.x^y = (c + y).x^γ *)
Lemma x_pow_γ_mul_add_distr_r : ∀ c γ,
  (POL [ps_monom fld c γ; ps_monom fld .1 fld%K γ … []] .= 
   (ps_field fld)
   POL [ps_const fld c; .1 fld%ps … []] .* (ps_field fld)
   POL [ps_monom fld .1 fld%K γ])%pol.
Proof.
intros c γ.
constructor.
 rewrite summation_only_one.
 rewrite Nat.sub_diag; simpl.
 unfold ps_mul; simpl.
 rewrite series_stretch_1.
 rewrite Z.mul_1_r.
 unfold cm; simpl.
 unfold ps_monom.
 rewrite series_mul_1_r.
 rewrite fold_series_const.
 rewrite stretch_series_const.
 reflexivity.

 constructor; [ idtac | constructor ].
 unfold summation.
 rewrite Nat.sub_0_r.
 unfold summation_aux.
 rewrite Nat.sub_0_r; simpl.
 rewrite ps_mul_1_l.
 rewrite ps_add_0_r.
 rewrite ps_mul_0_r.
 rewrite ps_add_0_l.
 reflexivity.
Qed.

Lemma fold_eq_ps : fld_eq (ps_field fld) = eq_ps fld.
Proof. reflexivity. Qed.

Lemma pol₁_eq_f'₁ : ∀ f β₁ γ₁ c₁,
  (pol₁ fld f β₁ γ₁ c₁ .= (ps_field fld) f'₁ fld f β₁ γ₁ c₁)%pol.
Proof.
intros f β₁ γ₁ c₁.
unfold pol₁, f'₁.
remember POL [ps_monom fld .1 fld%K γ₁]%pol as p.
remember POL [ps_const fld c₁; .1 fld%ps … []]%pol as p'.
remember (p .* (ps_field fld) p')%pol as p₁; subst p p'.
remember POL [ps_monom fld c₁ γ₁; ps_monom fld .1 fld%K γ₁ … []]%pol as p₂.
assert (p₁ .= (ps_field fld) p₂)%pol as Heq.
 subst p₁ p₂.
 constructor.
  rewrite summation_only_one.
  rewrite Nat.sub_diag; simpl.
  unfold ps_mul; simpl.
  rewrite series_stretch_1.
  do 2 rewrite fold_series_const.
  rewrite stretch_series_const.
  rewrite series_mul_1_l.
  rewrite Z.add_0_r, Z.mul_1_r.
  unfold cm; simpl.
  rewrite Pos.mul_1_r.
  reflexivity.

  constructor; [ idtac | constructor ].
  remember POL [ps_monom fld .1 fld%K γ₁]%pol as p.
  remember POL [ps_const fld c₁; .1 fld%ps … []]%pol as p'.
  unfold summation, summation_aux; simpl.
  subst p p'; simpl.
  rewrite ps_mul_1_r, ps_add_0_r, ps_mul_0_l, ps_add_0_r.
  reflexivity.

 rewrite Heq; reflexivity.
Qed.

(* *)

(*
bbb.

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
