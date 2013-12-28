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
    deg_up_bnd : nat;
    fin_prop : ∀ i, deg_up_bnd ≤ i → (p_series .[i] .= f (.0 f))%F }.

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
  max (deg_up_bnd p₁) (deg_up_bnd p₂) ≤ i
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
  deg_up_bnd p₁ + deg_up_bnd p₂ ≤ i
  → ((p_series p₁ .* f p_series p₂)%ser .[i] .= f .0 f)%F.
Proof.
intros α f p₁ p₂ i Hi.
unfold convol_mul.
apply all_0_sigma_0; intros j (_, Hj).
destruct (le_dec (deg_up_bnd p₁) j) as [H₁| H₁].
 rewrite fin_prop; [ idtac | assumption ].
 rewrite fld_mul_0_l; reflexivity.

 destruct (le_dec (deg_up_bnd p₂) (i - j)) as [H₂| H₂].
  rewrite fld_mul_comm.
  rewrite fin_prop; [ idtac | assumption ].
  rewrite fld_mul_0_l; reflexivity.

  exfalso; omega.
Qed.

Definition polyn_mul α (f : field α) p₁ p₂ :=
  {| p_series := (p_series p₁ .* f p_series p₂)%ser;
     fin_prop := fin_prop_mul p₁ p₂ |}.

(* application *)

Fixpoint apply_polyn_loop α (f : field α) cnt deg s x :=
  match cnt with
  | O => (s.[deg])%F
  | S c => (s.[deg] .+ f x .* f apply_polyn_loop f c (S deg) s x)%F
  end.

Fixpoint polyn_degree α (f : field α) upbnd pol :=
  match upbnd with
  | O => O
  | S ub => if ah merde faut que ça soye décidable...

Definition apply_polyn α (f : field α) pol x :=
  apply_polyn_loop f (polyn_degree (deg_up_bnd pol) (p_series pol)) O
    (p_series pol) x.

(* Horner's algorithm : to be updated
Definition apply_polyn α β γ
    (zero_plus_v : β → α) (add_v_coeff : α → β → α) (mul_v_x : α → γ → α)
    (pol : polyn β) (x : γ) :=
  List.fold_right (λ c accu, add_v_coeff (mul_v_x accu x) c)
    (zero_plus_v (an pol)) (al pol).
*)
