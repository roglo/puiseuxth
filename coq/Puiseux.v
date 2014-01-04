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

Set Implicit Arguments.

(* *)

Notation "'POL' l" := ({| al := l |})
  (at level 1) :
  poly_scope.
Notation ".{ f a .}" := (mkpol (ps_field f) [a])
  (at level 0, f at level 0, a at level 0) :
  poly_scope.
Notation ".{ f a + b 'Y' .}" := (mkpol (ps_field f) [a; b … []])
  (at level 0, f at level 0, a at level 0, b at level 0) :
  poly_scope.
(*
Notation "'YPOL' f a" := (polyn_of_list (ps_field f) [a])
  (at level 0, f at level 0, a at level 0) :
  ps_polyn_scope.
Notation "'YPOL' f a + b * 'Y'" := (polyn_of_list (ps_field f) [a; b … []])
  (at level 50, f at level 0, a at level 0, b at level 0) :
  ps_polyn_scope.
Notation ".{ f c * 'X^' q .}" := (ps_monom f c q)
  (at level 0, f at level 0, c at level 0, q at level 0) : ps_polyn_scope.
Notation ".< f c .>" := (ps_const f c)
  (at level 0, f at level 0, c at level 0) : ps_polyn_scope.
*)

Definition apply_poly_with_poly α (f : field α) pol :=
  apply_poly
    {| al := [] |}
    (λ pol₁ ps, poly_add f pol₁ {| al := [ps] |})
    (poly_mul f) pol.

(* f₁(x,y₁) = x^(-β₁).f(x,x^γ₁.(c₁ + y₁)) *)
Definition f₁ α (fld : field α) f β₁ γ₁ c₁ :=
  poly_mul (ps_field fld) {| al := [ps_monom fld .1 fld%F (- β₁)] |}
    (apply_poly_with_poly (ps_field fld) f
       (poly_mul (ps_field fld) {| al := [ps_monom fld .1 fld%F γ₁] |}
          {| al := [ps_const fld c₁; .1 fld%ps … []] |})).

(* f'₁(x,y₁) = x^(-β₁).f(x,c₁.x^γ₁ + x^γ.y₁) *)
Definition f'₁ α (fld : field α) f β₁ γ₁ c₁ :=
  poly_mul (ps_field fld) {| al := [ps_monom fld .1 fld%F (- β₁)] |}
    (apply_poly_with_poly (ps_field fld) f
       {| al := [ps_monom fld c₁ γ₁; ps_monom fld .1 fld%F γ₁ … []] |}).

(* *)

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
  ({| al := [ps_monom fld c γ; ps_monom fld .1 fld%F γ … []] |}
   .= (ps_field fld)
   {| al := [ps_const fld c; .1 fld%ps … []] |} .* 
   (ps_field fld) {| al := [ps_monom fld .1 fld%F γ] |})%pol.
Proof.
intros c γ.
Show.
unfold eq_poly; simpl.
bbb.
constructor; intros k; simpl.
unfold convol_mul.
unfold convol_mul; simpl.
destruct k; simpl.
 rewrite sigma_only_one; simpl.
 unfold ps_mul; simpl.
 rewrite stretch_series_1.
 rewrite series_mul_1_r.
 rewrite Z.mul_1_r.
 unfold cm; simpl.
 rewrite fold_series_const.
 rewrite stretch_series_const.
 reflexivity.

 destruct k; simpl.
  unfold sigma; simpl.
  rewrite ps_mul_1_l, ps_add_0_r.
  rewrite ps_mul_0_r, ps_add_0_l.
  reflexivity.

  destruct k; simpl.
   unfold sigma; simpl.
   rewrite ps_mul_0_r, ps_add_0_l.
   rewrite ps_mul_0_r, ps_add_0_l.
   rewrite ps_mul_0_l, ps_add_0_l.
   reflexivity.

   unfold sigma; simpl.
   rewrite ps_mul_0_r, ps_add_0_l.
   rewrite ps_mul_0_r, ps_add_0_l.
   rewrite ps_mul_0_l, ps_add_0_l.
   rewrite ps_mul_0_l, ps_add_0_l.
   rewrite all_0_sigma_aux_0; [ reflexivity | idtac ].
   intros i (Hi, Hik).
   destruct i; [ exfalso; omega | idtac ].
   destruct i; [ exfalso; omega | idtac ].
   destruct i; [ exfalso; omega | idtac ].
   rewrite ps_mul_0_l; reflexivity.
Qed.

Lemma fold_eq_ps : fld_eq (ps_field fld) = eq_ps fld.
Proof. reflexivity. Qed.

Lemma zzz : ∀ f β₁ γ₁ c₁,
  ((f₁ f β₁ γ₁ c₁:polyn (ps_field fld)) = f'₁ f β₁ γ₁ c₁)%pspol.
Proof.
intros f β₁ γ₁ c₁.
constructor; intros k; simpl.
unfold convol_mul; simpl.
rewrite <- fold_eq_ps.
apply sigma_compat; intros i (_, Hi); simpl.
apply ps_mul_compat_l.
bbb.
rewrite x_pow_γ_mul_add_distr_r.

 unfold apply_poly_with_ps_poly.
 unfold ps_pol_add; simpl.
 unfold pol_add; simpl.
 unfold ps_pol_mul; simpl.
 unfold pol_mul; simpl.
bbb.

intros f β₁ γ₁ c₁.
unfold f₁, f₁'.
do 2 f_equal.
unfold ps_pol_mul.
unfold pol_mul.
simpl.
f_equal; simpl.
 rewrite Z.mul_1_r, Z.add_0_r.
 unfold ps_monom; simpl.
 rewrite Plcm_comm, Plcm_1_l.
 do 3 f_equal.
bbb.

(* *)

(* rest to be used later perhaps *)

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
      let pol₁ := f₁ pol (β ns) (γ ns) c in
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

(* ... *)

(*
Fixpoint puiseux_comden α n cd (s : series (term α Q)) :=
  match n with
  | O => cd
  | S n₁ =>
      match s with
      | Term t ss => puiseux_comden n₁ (Plcm cd (Qden (Qred (power t)))) ss
      | End => cd
      end
  end.
*)

(*
CoFixpoint complete α (zero : α) cd p s :=
  match s with
  | Term t ns =>
      let p₁ := Qplus p (Qmake 1 cd) in
      if Qlt_le_dec p₁ (power t) then
        Term {| coeff := zero; power := p₁ |} (complete zero cd p₁ s)
      else
        Term t ns
  | End =>
      End _
  end.

CoFixpoint term_series_to_coeff_series α zero cd s : series α :=
  match s with
  | Term t ns =>
      Term (coeff t)
        (term_series_to_coeff_series α zero cd
           (complete zero cd (power t) ns))
  | End =>
      End _
  end.
*)

(*
Definition puiseux_root α acf niter (pol : polynomial (puiseux_series α)) :
    puiseux_series α :=
  let s := puiseux_loop None acf pol in
  let cd := puiseux_comden niter 1 s in
  {| ps_terms := term_series_to_coeff_series (zero (ac_field acf)) cd s;
     ps_valnum :=
       match s with
       | Term t _ => Qnum (Qred (Qmult (power t) (Qmake (Zpos cd) 1)))
       | End => 0
       end;
     ps_polord := cd |}.
*)

(* *)

(*
CoFixpoint series_series_take α n (s : series α) :=
  match n with
  | O => End _
  | S n₁ =>
      match s with
      | Term a t => Term a (series_series_take n₁ t)
      | End => End _
      end
  end.
*)

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
  list_eq (f_eq f) (list_pad n v cl) (list_pad n v [] ++ cl).
Proof.
intros n v cl.
revert v cl.
induction n; intros; simpl.
 apply list_eq_refl.

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

(*
Delimit Scope ps with puiseux_series.
Notation "x * y" := (ps_mul f x y) : ps.

Open Scope ps.
*)

Definition abar (pol : polynomial (puiseux_series α)) h :=
  List.nth h (al pol) (an pol).

Definition ps_pol_add := pol_add (add ps_f).
Definition ps_pol_mul := pol_mul (zero ps_f) (add ps_f) (mul ps_f).

Fixpoint ps_pol_power pol n :=
  match n with
  | O => {| al := []; an := one ps_f |}
  | S n₁ => ps_pol_mul pol (ps_pol_power pol n₁)
  end.

(*
Lemma normal_terms_end : ∀ n cd, normal_terms f n cd (End α) = End α.
Proof.
intros n cd.
symmetry.
rewrite series_eta.
reflexivity.
Qed.

Lemma normal_terms_0 : ∀ s, normal_terms f 0 0 s = s.
Proof.
intros s.
apply ext_eq_ser with (f := f).
revert s.
cofix IHs; intros.
destruct s as [t s| ].
 eapply eq_ser_term; [ idtac | reflexivity | reflexivity | apply IHs ].
 symmetry; rewrite series_eta; reflexivity.

 apply eq_ser_end; [ idtac | reflexivity ].
 symmetry; rewrite series_eta; reflexivity.
Qed.
*)

(*
Lemma series_add_end_l : ∀ s, series_add f (End α) s = s.
Proof.
intros s.
symmetry.
rewrite series_eta.
simpl.
destruct s; reflexivity.
Qed.
*)

(*
Lemma ps_add_0_r : ∀ ps, ps_add f ps (ps_zero α) = ps.
Proof.
intros ps.
rewrite ps_add_comm.
unfold ps_add.
rewrite Zminus_0_r.
rewrite Plcm_1_l.
rewrite Nat.div_same.
 rewrite Nat.div_1_r.
 simpl.
 rewrite Zmult_1_r.
 rewrite normal_terms_end.
 rewrite series_add_end_l.
 remember (ps_valnum ps) as v.
 symmetry in Heqv.
 destruct v as [| n| n].
  destruct ps; simpl in Heqv |- *; rewrite Heqv.
  f_equal.
  apply normal_terms_0.

  rewrite series_add_end_l.
  destruct ps; simpl in Heqv |- *; rewrite Heqv.
  rewrite normal_terms_0.
bbb.
*)

Lemma zzz : ∀ pol pts ns cpol c₁ r₁,
  pts = points_of_ps_polynom f pol
  → ns ∈ newton_segments f pol
    → cpol = characteristic_polynomial f pol ns
      → ac_root acf cpol = (c₁, r₁)
        → f₁ f pol (β ns) (γ ns) c₁
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
unfold f₁.
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

(*
Theorem has_neg_slope : ∀ pol ns cpol (c : α) r pol₁,
  ns ∈ newton_segments f pol
  → cpol = characteristic_polynomial f pol ns
    → (c, r) = ac_root acf cpol
      → pol₁ = f₁ f pol (β ns) (γ ns) c
        → ∃ ns₁, ns₁ ∈ newton_segments f pol₁ → γ ns₁ > 0.
Proof.
bbb.
*)

End field.
