(* Fpolynomial.v *)

(* polynomials on a field *)

Require Import Utf8.
Require Import QArith.

Require Import Misc.
Require Import Field.
Require Import Power_series.

Set Implicit Arguments.

Record polyn α (f : field α) :=
  { p_series : power_series α;
    degree_ub : nat;
    fin_prop : ∀ i, degree_ub ≤ i → (p_series .[i] .= f (.0 f))%F }.

Definition eq_polyn α (f : field α) (p₁ p₂ : polyn f) :=
  eq_series f (p_series p₁) (p_series p₂).

Lemma fin_prop_list : ∀ α (f : field α) l i,
  List.length l ≤ i
  → ({| terms i := List.nth i l (.0 f)%F |} .[i] .= f .0 f)%F.
Proof.
intros α f l i Hlen; simpl.
rewrite List.nth_overflow; [ reflexivity | assumption ].
Qed.

Definition polyn_of_list α (f : field α) l :=
  {| p_series := {| terms i := List.nth i l (.0 f)%F |};
     fin_prop := fin_prop_list f l |}.

(* addition *)

Lemma fin_prop_add : ∀ α (f : field α) (p₁ p₂ : polyn f) i,
  max (degree_ub p₁) (degree_ub p₂) ≤ i
  → ((p_series p₁ .+ f p_series p₂)%ser .[i] .= f .0 f)%F.
Proof.
intros α f p₁ p₂ i Hi; simpl.
rewrite fin_prop, fin_prop.
 rewrite fld_add_0_l; reflexivity.

 etransitivity; [ idtac | eassumption ].
 apply Max.le_max_r.

 etransitivity; [ idtac | eassumption ].
 apply Max.le_max_l.
Qed.

Definition polyn_add α (f : field α) p₁ p₂ :=
  {| p_series := (p_series p₁ .+ f p_series p₂)%ser;
     fin_prop := fin_prop_add p₁ p₂ |}.

(* multiplication *)

Lemma fin_prop_mul : ∀ α (f : field α) (p₁ p₂ : polyn f) i,
  degree_ub p₁ + degree_ub p₂ ≤ i
  → ((p_series p₁ .* f p_series p₂)%ser .[i] .= f .0 f)%F.
Proof.
intros α f p₁ p₂ i Hi.
unfold convol_mul.
apply all_0_sigma_0; intros j (_, Hj).
destruct (le_dec (degree_ub p₁) j) as [H₁| H₁].
 rewrite fin_prop; [ idtac | assumption ].
 rewrite fld_mul_0_l; reflexivity.

 destruct (le_dec (degree_ub p₂) (i - j)) as [H₂| H₂].
  rewrite fld_mul_comm.
  rewrite fin_prop; [ idtac | assumption ].
  rewrite fld_mul_0_l; reflexivity.

  exfalso; omega.
Qed.

Definition polyn_mul α (f : field α) p₁ p₂ :=
  {| p_series := (p_series p₁ .* f p_series p₂)%ser;
     fin_prop := fin_prop_mul p₁ p₂ |}.

(* application *)

(*
Fixpoint apply_polyn_loop α (f : field α) cnt i s x :=
  match cnt with
  | O => (s.[i])%F
  | S c => (s.[i] .+ f x .* f apply_polyn_loop f c (S i) s x)%F
  end.

Definition apply_polyn α (f : field α) (pol : polyn f) x :=
  apply_polyn_loop f (degree_ub pol) O (p_series pol) x.
*)

(* Horner's algorithm *)
Fixpoint apply_polyn_loop α β γ
    (zero_plus_v : β → α) (add_v_coeff : α → β → α) (mul_v_x : α → γ → α)
    cnt i (s : power_series β) (x : γ) :=
  match cnt with
  | O => zero_plus_v (terms s i)
  | S c =>
      add_v_coeff
        (mul_v_x
          (apply_polyn_loop zero_plus_v add_v_coeff mul_v_x c (S i) s x)
          x)
        (terms s i)
  end.

Fixpoint apply_polyn α β γ (f : field β)
    (zero_plus_v : β → α) (add_v_coeff : α → β → α) (mul_v_x : α → γ → α)
    (pol : polyn f) (x : γ) :=
  apply_polyn_loop zero_plus_v add_v_coeff mul_v_x
    (degree_ub pol) O (p_series pol) x.
