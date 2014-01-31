(* AlgCloCharPol.v *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Misc.
Require Import Field.
Require Import Newton.
Require Import Fsummation.
Require Import Fpolynomial.
Require Import Puiseux_base.
Require Import Puiseux_series.
Require Import CharactPolyn.

Set Implicit Arguments.

Definition apply_polynomial α (f : field α) :=
  apply_poly (fld_zero f) (fld_add f) (fld_mul f).

(* euclidean division of a polynomial by (x - c) *)

Fixpoint list_mod_div_mono α (f : field α) c al :=
  match al with
  | [] => []
  | [a₁ … al₁] =>
      [apply_polynomial f (POL al)%pol c … list_mod_div_mono f c al₁]
  end.

Definition poly_div_mono α (f : field α) pol c :=
  match list_mod_div_mono f c (al pol) with
  | [] => POL []%pol
  | [m … ml] => POL ml%pol
  end.

Definition poly_mod_mono α (f : field α) pol c :=
  match list_mod_div_mono f c (al pol) with
  | [] => .0 f%K
  | [m … ml] => m
  end.

(* test
Load Q_field.
Definition Qtest_div cl c := poly_div_mono Q_field (POL cl)%pol c.
Definition Qtest_mod cl c := poly_mod_mono Q_field (POL cl)%pol c.
Eval vm_compute in Qtest_div [2#1; -3#1; 1#1 … []] (4#1).
Eval vm_compute in Qtest_mod [2#1; -3#1; 1#1 … []] (4#1).
Eval vm_compute in Qtest_div [-Qnat 5; -Qnat 13; Qnat 0; Qnat 4 … []] (- 1 # 2).
Eval vm_compute in Qtest_mod [-Qnat 5; -Qnat 13; Qnat 0; Qnat 4 … []] (- 1 # 2).
*)

(* trying to compute i-th derivative divided by factorial i *)

Fixpoint comb n k :=
  match n with
  | 0%nat => 0%nat
  | 1%nat => 1%nat
  | S (S _ as n₁) =>
      match (n - k)%nat with
      | 0%nat => 1%nat
      | S _ =>
          match k with
          | 0%nat => 1%nat
          | S k₁ => (comb n₁ k₁ + comb n₁ k)%nat
          end
      end
  end.

Fixpoint glop A (mul : nat → A → A) al n i :=
  match al with
  | [] => []
  | [a₁ … al₁] => [mul (comb n i) a₁ … glop mul al₁ n (S i)]
  end.

Definition nth_der_on_fact_n A (mul : nat → A → A) pol n :=
  glop mul (List.skipn n (al pol)) n 0.

(* *)

Fixpoint degree_plus_1_of_list α (is_zero : α → bool) (l : list α) :=
  match l with
  | [] => O
  | [x … l₁] =>
      match degree_plus_1_of_list is_zero l₁ with
      | O => if is_zero x then O else 1%nat
      | S n => S (S n)
      end
  end.

Definition degree α is_zero (pol : polynomial α) :=
  pred (degree_plus_1_of_list is_zero (al pol)).

Record algeb_closed_field α :=
  { ac_field : field α;
    ac_is_zero : α → bool;
    ac_root : polynomial α → α;
    ac_prop : ∀ pol, degree ac_is_zero pol ≥ 1
      → (apply_polynomial ac_field pol (ac_root pol) .= ac_field
         .0 ac_field)%K }.

Fixpoint poly_power α (f : field α) pol n :=
  match n with
  | O => .1 f%pol
  | S m => (pol .* f poly_power f pol m)%pol
  end.

Notation "a .^ f b" := (poly_power f a b) : poly_scope.

Fixpoint list_multiplicity α (acf : algeb_closed_field α) c₁ al d :=
  let f := ac_field acf in
  match d with
  | O => O
  | S d₁ =>
      match list_mod_div_mono f c₁ al with
      | [] => O
      | [m … ml] =>
          if ac_is_zero acf m then S (list_multiplicity acf c₁ ml d₁)
          else O
      end
  end.

Definition multiplicity α (acf : algeb_closed_field α) c₁ pol :=
  list_multiplicity acf c₁ (al pol) (List.length (al pol)).

Fixpoint quotient_phi_x_sub_c_pow_r α (f : field α) pol c₁ r :=
  match r with
  | O => pol
  | S r₁ => quotient_phi_x_sub_c_pow_r f (poly_div_mono f pol c₁) c₁ r₁
  end.

Definition list_apply α (f : field α) al x :=
  (List.fold_right (λ c accu : α, accu .* f x .+ f c) .0 f al)%K.

Lemma fold_list_apply : ∀ α (f : field α) al x,
  (List.fold_right (λ c accu : α, accu .* f x .+ f c) .0 f al)%K =
  list_apply f al x.
Proof. reflexivity. Qed.

Add Parametric Morphism α (f : field α) : (list_apply f)
  with signature list_eq f ==> fld_eq f ==> fld_eq f
  as list_apply_morph.
Proof.
intros la lb Hab x y Hxy.
revert lb Hab x y Hxy.
induction la as [| a]; intros; simpl.
 revert x y Hxy.
 induction lb as [| b]; intros; [ reflexivity | simpl ].
 apply list_eq_nil_cons_inv in Hab.
 destruct Hab as (Hb, Hlb).
 rewrite Hb, fld_add_0_r.
 rewrite <- IHlb; try eassumption.
 rewrite fld_mul_0_l; reflexivity.

 destruct lb as [| b].
  apply list_eq_cons_nil_inv in Hab.
  destruct Hab as (Ha, Hla).
  rewrite Ha, fld_add_0_r; simpl.
  rewrite IHla; try eassumption; simpl.
  rewrite fld_mul_0_l; reflexivity.

  simpl.
  apply list_eq_cons_inv in Hab.
  destruct Hab as (Hab, Hlab).
  unfold list_apply.
  rewrite Hab, Hxy.
  do 2 rewrite fold_list_apply.
  rewrite IHla; try eassumption.
  reflexivity.
Qed.

Add Parametric Morphism α (f : field α) : (apply_polynomial f)
  with signature eq_poly f ==> fld_eq f ==> fld_eq f
  as apply_polynomial_morph.
Proof.
intros p₁ p₂ Hpp v₁ v₂ Hvv.
unfold eq_poly in Hpp.
unfold apply_polynomial.
unfold apply_poly.
do 2 rewrite fold_list_apply.
rewrite Hpp, Hvv; reflexivity.
Qed.

Section theorems.

Variable α : Type.
Variable acf : algeb_closed_field α.
Let f := ac_field acf.

(* P(x) = P(0) + x Q(x) *)
Lemma poly_eq_add_const_mul_x_poly : ∀ c cl,
  (POL [c … cl] .= f POL [c] .+ f POL [.0 f; .1 f … []]%K .* f POL cl)%pol.
Proof.
intros c cl.
unfold eq_poly; simpl.
rewrite summation_only_one.
rewrite fld_mul_0_l, fld_add_0_r.
constructor; [ reflexivity | idtac ].
destruct cl as [| c₁]; [ reflexivity | simpl ].
constructor.
 rewrite summation_only_one_non_0 with (v := 1%nat).
  rewrite fld_mul_1_l; reflexivity.

  split; [ apply Nat.le_0_l | reflexivity ].

  intros i (_, Hi) Hin1.
  destruct i; [ rewrite fld_mul_0_l; reflexivity | simpl ].
  destruct i; [ exfalso; apply Hin1; reflexivity | idtac ].
  destruct i; rewrite fld_mul_0_l; reflexivity.

 symmetry.
 apply poly_convol_mul_x_l; reflexivity.
Qed.

Lemma apply_polynomial_add : ∀ p₁ p₂ x,
  (apply_polynomial f (p₁ .+ f p₂)%pol x .= f
   apply_polynomial f p₁ x .+ f apply_polynomial f p₂ x)%K.
Proof.
intros p₁ p₂ x.
unfold apply_polynomial, apply_poly; simpl.
remember (al p₁) as la eqn:Hla .
remember (al p₂) as lb eqn:Hlb .
clear.
revert x lb.
induction la as [| a]; intros; simpl.
 rewrite fld_add_0_l; reflexivity.

 destruct lb as [| b]; simpl; [ rewrite fld_add_0_r; reflexivity | idtac ].
 rewrite IHla.
 do 2 rewrite fld_add_assoc.
 apply fld_add_compat_r.
 rewrite fld_mul_add_distr_r.
 do 2 rewrite <- fld_add_assoc.
 apply fld_add_compat_l, fld_add_comm.
Qed.

Lemma list_fold_right_apply_compat : ∀ la lb x,
  list_eq f la lb
  → (List.fold_right (λ c accu, accu .* f x .+ f c) .0 f la .= f
     List.fold_right (λ c accu, accu .* f x .+ f c) .0 f lb)%K.
Proof.
intros la lb x Heq.
revert lb x Heq.
induction la as [| a]; intros; simpl.
 revert x.
 induction lb as [| b]; intros; [ reflexivity | simpl ].
 apply list_eq_nil_cons_inv in Heq.
 destruct Heq as (Hb, Hlb).
 rewrite Hb, fld_add_0_r.
 rewrite <- IHlb; [ idtac | assumption ].
 rewrite fld_mul_0_l; reflexivity.

 destruct lb as [| b].
  simpl.
  apply list_eq_cons_nil_inv in Heq.
  destruct Heq as (Ha, Hla).
  rewrite IHla; [ idtac | eassumption ].
  simpl.
  rewrite Ha, fld_mul_0_l, fld_add_0_r; reflexivity.

  apply list_eq_cons_inv in Heq.
  destruct Heq as (Hab, Hlab).
  simpl.
  rewrite Hab, IHla; [ reflexivity | eassumption ].
Qed.

(*
  Hlen : pred (length la + length lb) = len
  ============================
   (list_apply la x .* f list_apply lb x .= f
    list_apply (poly_convol_mul f la lb 0 len) x)%K

  Hlen : pred (length la + length lb) = S len
  ============================
   (list_apply la x .* f list_apply lb x .= f
    list_apply (poly_convol_mul f la lb 1 len) x .* f x .+ f
    List.nth 0 la .0 f .* f List.nth 0 lb .0 f)%K

  Hlen : pred (length la + length lb) = S (S len)
  ============================
   (list_apply la x .* f list_apply lb x .= f
    (list_apply (poly_convol_mul f la lb 2 len) x .* f x .+ f
     Σf (j = 0, 1)_ List.nth j la .0 f .* f List.nth (1 - j) lb .0 f) .* f x
    .+ f List.nth 0 la .0 f .* f List.nth 0 lb .0 f)%K

  Hlen : (length la + length lb)%nat = S len
  ============================
   ((list_apply f la x .* f x .+ f a) .* f (list_apply f lb x .* f x .+ f b)
    .= f
    (list_apply f (poly_convol_mul f [a … la] [b … lb] 2 len) x .* f x .+ f
     Σf (j = 0, 1)
     _ List.nth j [a … la] .0 f .* f List.nth (1 - j) [b … lb] .0 f) .* f x
    .+ f a .* f b)%K
*)

Lemma xxx : ∀ a b la lb x len,
  S (length la + length lb) = len
  → (list_apply f [a … la] x .* f list_apply f [b … lb] x .= f
     list_apply f (poly_convol_mul f [a … la] [b … lb] 0 len) x)%K.
Proof.
intros a b la lb x len Hlen; simpl.
destruct len; [ discriminate Hlen | simpl ].
rewrite summation_only_one.
apply Nat.succ_inj in Hlen.
rewrite fld_mul_add_distr_r.
do 2 rewrite fld_mul_add_distr_l.
rewrite fld_add_assoc.
apply fld_add_compat_r.
rewrite fld_mul_assoc.
rewrite fld_mul_assoc.
assert
 (list_apply f la x .* f x .* f b .= f list_apply f la x .* f b .* f x)%K
 as H.
 apply fld_mul_shuffle0.

 rewrite H; clear H.
 do 2 rewrite <- fld_mul_add_distr_r.
 apply fld_mul_compat_r.
 destruct len; simpl.
  Focus 2.
  unfold summation; simpl.
  rewrite fld_add_0_r.
  rename a into a₀.
  rename b into b₀.
  destruct la as [| a₁].
   simpl.
   Focus 2.
   destruct lb as [| b₁].
    simpl.
    Focus 2.
    simpl.
    rewrite fld_add_assoc.
    do 3 rewrite fld_mul_add_distr_r.
    rewrite fld_add_assoc, fld_add_comm, fld_add_assoc.
    apply fld_add_compat_r.
    rewrite fld_mul_add_distr_l.
    rewrite <- fld_add_assoc, fld_add_comm.
    do 2 rewrite <- fld_add_assoc.
    rewrite fld_add_comm.
    apply fld_add_compat_r.
    rewrite fld_mul_assoc.
    rewrite fld_add_assoc.
    rewrite fld_mul_add_distr_l.
    rewrite fld_mul_add_distr_l.
    rewrite fld_mul_assoc.
    rewrite fld_mul_assoc.
    rewrite fld_add_assoc.
    assert
     (list_apply f la x .* f x .* f b₀ .= f list_apply f la x .* f b₀ .* f x)%K
     as H by apply fld_mul_shuffle0.
    rewrite H; clear H.
    assert (a₁ .* f x .* f b₁ .= f a₁ .* f b₁ .* f x)%K
     as H by apply fld_mul_shuffle0.
    rewrite H; clear H.
    assert
     (list_apply f la x .* f x .* f x .* f b₁ .= f
      list_apply f la x .* f x .* f b₁ .* f x)%K as H
     by apply fld_mul_shuffle0.
    rewrite H; clear H.
    do 5 rewrite <- fld_mul_add_distr_r.
    apply fld_mul_compat_r.
    simpl in Hlen.
    rewrite Nat.add_succ_r in Hlen.
    apply Nat.succ_inj in Hlen.
bbb.

Lemma yyy : ∀ la lb x len,
  pred (length la + length lb) = len
  → (list_apply f la x .* f list_apply f lb x .= f
     list_apply f (poly_convol_mul f la lb 0 len) x)%K.
Proof.
intros la lb x len Hlen.
destruct la as [| a].
 rewrite fld_mul_0_l.
 rewrite poly_convol_mul_nil_l; reflexivity.

 destruct lb as [| b].
  rewrite fld_mul_0_r.
  rewrite poly_convol_mul_nil_r; reflexivity.

  simpl in Hlen.
  rewrite Nat.add_succ_r in Hlen.
bbb.

intros la lb x len Hlen.
destruct len.
 simpl.
 destruct la as [| a]; simpl.
  rewrite fld_mul_0_l; reflexivity.

  destruct lb as [| b]; simpl.
   rewrite fld_mul_0_r; reflexivity.

   simpl in Hlen.
   rewrite Nat.add_succ_r in Hlen; discriminate Hlen.

 simpl.
 destruct len.
  rewrite summation_only_one.
  simpl.
  rewrite fld_mul_0_l, fld_add_0_l.
  destruct la as [| a]; simpl.
   do 2 rewrite fld_mul_0_l; reflexivity.

   simpl in Hlen.
   rewrite Nat.add_comm in Hlen.
   destruct lb as [| b]; simpl.
    do 2 rewrite fld_mul_0_r; reflexivity.

    simpl in Hlen.
    apply Nat.succ_inj in Hlen.
    destruct lb; [ idtac | discriminate Hlen ].
    simpl in Hlen.
    destruct la; [ idtac | discriminate Hlen ].
    simpl.
    rewrite fld_mul_0_l, fld_add_0_l, fld_add_0_l; reflexivity.

  rewrite summation_only_one.
  remember 1%nat as z; simpl; subst z.
  destruct la as [| a].
   remember 1%nat as z; simpl; subst z.
   do 2 rewrite fld_mul_0_l.
   rewrite all_0_summation_0.
    do 2 rewrite fld_add_0_r.
    rewrite poly_convol_mul_nil_l; simpl.
    do 2 rewrite fld_mul_0_l; reflexivity.

    intros i (_, Hi).
    destruct i; rewrite fld_mul_0_l; reflexivity.

   remember 1%nat as z; remember [a … la] as ala.
   rewrite Heqala in |- * at 3.
   simpl; subst z ala.
   simpl in Hlen.
   destruct lb as [| b].
    simpl.
    do 2 rewrite fld_mul_0_r.
    rewrite poly_convol_mul_nil_r, fld_mul_0_l, fld_add_0_l.
    rewrite all_0_summation_0.
     rewrite fld_mul_0_l, fld_add_0_l; reflexivity.

     intros i (_, Hi).
     destruct i; rewrite fld_mul_0_r; reflexivity.

    rewrite Nat.add_comm in Hlen; simpl in Hlen.
    apply Nat.succ_inj in Hlen.
    rewrite Nat.add_comm in Hlen.
    remember [a … la] as ala.
    remember [b … lb] as alb.
    remember 1%nat as z.
    rewrite Heqala in |- * at 1.
    rewrite Heqala in |- * at 1.
    rewrite Heqalb in |- * at 1.
    rewrite Heqalb in |- * at 2.
    simpl; subst z ala alb.
Abort. (*
bbb.
*)

Lemma apply_polynomial_mul : ∀ p₁ p₂ x,
  (apply_polynomial f (p₁ .* f p₂)%pol x .= f
   apply_polynomial f p₁ x .* f apply_polynomial f p₂ x)%K.
Proof.
intros p₁ p₂ x.
symmetry.
unfold apply_polynomial, apply_poly; simpl.
remember (al p₁) as la eqn:Hla .
remember (al p₂) as lb eqn:Hlb .
clear.
do 3 rewrite fold_list_apply.
remember (pred (length la + length lb)) as n eqn:Hn .
symmetry in Hn.
bbb.

intros p₁ p₂ x.
unfold apply_polynomial, apply_poly; simpl.
remember (al p₁) as la eqn:Hla .
remember (al p₂) as lb eqn:Hlb .
clear.
do 3 rewrite fold_list_apply.
remember (pred (length la + length lb)) as n eqn:Hn .
symmetry in Hn.
destruct n; simpl.
 destruct la as [| a]; simpl.
  rewrite fld_mul_0_l; reflexivity.

  destruct lb as [| b]; simpl.
   rewrite fld_mul_0_r; reflexivity.

   simpl in Hn.
   rewrite Nat.add_succ_r in Hn; discriminate Hn.

 rewrite summation_only_one; simpl.
bbb.

remember (List.fold_right (λ c accu : α, accu .* f x .+ f c) .0 f)%K as g.
revert lb.
induction la as [| a]; intros; simpl.
 subst g.
 rewrite fld_mul_0_l.
 rewrite list_fold_right_apply_compat with (lb := []).
  reflexivity.

  apply poly_convol_mul_nil_l.

 induction lb as [| b].
  simpl.
  subst g.
  rewrite list_fold_right_apply_compat with (lb := []).
   simpl.
   rewrite fld_mul_0_r; reflexivity.

   apply poly_convol_mul_nil_r.

  simpl.
bbb.

(* p(c) = 0 ⇒ p = (x-c) * (p / (x-c)) *)
Lemma zzz : ∀ c p,
  (apply_polynomial f p c .= f .0 f)%K
  → (p .= f POL [(.-f c)%K; .1 f%K … []] .* f poly_div_mono f p c)%pol.
Proof.
intros c p Hz.
unfold poly_div_mono.
destruct p as (cl); simpl.
unfold eq_poly; simpl.
rewrite summation_only_one.
destruct cl as [| c₁]; simpl.
 rewrite fld_mul_0_r.
 constructor; reflexivity.

 constructor.
  rename c into x.
  rename c₁ into c.
  rename x into c₁.
  pose proof (poly_eq_add_const_mul_x_poly c cl) as Hc.
  rewrite Hc in Hz; simpl in Hz.
  rewrite apply_polynomial_add in Hz.
bbb.

(* [Walker, p. 100] « If c₁ ≠ 0 is an r-fold root, r ≥ 1, of Φ(z^q) = 0,
   we have:
      Φ(z^q) = (z - c₁)^r Ψ(z), [...] » *)
Theorem phi_zq_eq_z_sub_c₁_psy : ∀ pol ns c₁ r Ψ,
  ns ∈ newton_segments f pol
  → c₁ = ac_root acf (Φq f pol ns)
    → r = multiplicity acf c₁ (Φq f pol ns)
      → Ψ = quotient_phi_x_sub_c_pow_r f (Φq f pol ns) c₁ r
        → (Φq f pol ns .= f POL [(.- f c₁)%K; .1 f%K … []] .^ f r .* f Ψ)%pol.
Proof.
intros pol ns c₁ r Ψ Hns Hc₁ Hr HΨ.
symmetry in Hc₁, Hr.
destruct r.
 simpl.
 rewrite poly_mul_1_l.
 subst Ψ; reflexivity.

 simpl.
 destruct r; simpl.
  rewrite poly_mul_1_r.
  subst Ψ; simpl.
  unfold Φq; simpl.
  unfold poly_left_shift; simpl.
  unfold poly_div_mono; simpl.
  rewrite skipn_pad.
  rewrite Nat.sub_diag; simpl.
  remember (ini_pt ns) as jj eqn:Hj .
  destruct jj as (jq, αj); simpl.
  remember Hns as H; clear HeqH.
  apply exists_ini_pt_nat in H.
  destruct H as (j, (x, Hx)).
  rewrite <- Hj in Hx; injection Hx; clear Hx; intros; subst jq x.
  unfold nofq, Qnat; simpl; rewrite Nat2Z.id.
  symmetry in Hj.
  apply zzz.
bbb.

End theorems.
