(* Fpolynomial.v *)

(* polynomials on a field *)

Require Import Utf8.
Require Import QArith.

Require Import Misc.
Require Import Field.
Require Import Power_series.

Set Implicit Arguments.

Record polyn α (f : field α) :=
  { pseries : power_series α;
    finprop : ∃ n, ∀ m, n ≤ m → (pseries .[m] .= f (.0 f))%F }.

Definition eq_polyn α (f : field α) (p₁ p₂ : polyn f) :=
  eq_series f (pseries p₁) (pseries p₂).

Lemma finprop_list : ∀ α (f : field α) l,
  ∃ n, ∀ m, n ≤ m → ({| terms i := List.nth i l (.0 f)%F |} .[m] .= f .0 f)%F.
Proof.
intros α f l.
exists (List.length l); intros m Hm; simpl.
rewrite List.nth_overflow; [ reflexivity | assumption ].
Qed.

Definition polyn_of_list α (f : field α) l :=
  {| pseries := {| terms i := List.nth i l (.0 f)%F |};
     finprop := finprop_list f l |}.

(* addition *)

Lemma finprop_add : ∀ α (f : field α) (p₁ p₂ : polyn f),
  ∃ n, ∀ m, n ≤ m → ((pseries p₁ .+ f pseries p₂)%ser .[m] .= f .0 f)%F.
Proof.
intros α f p₁ p₂.
pose proof (finprop p₁) as P₁.
pose proof (finprop p₂) as P₂.
destruct P₁ as (n₁, Hn₁).
destruct P₂ as (n₂, Hn₂).
exists (max n₁ n₂); intros m Hnn; simpl.
rewrite Hn₁, Hn₂.
 rewrite fld_add_0_l; reflexivity.

 transitivity (max n₁ n₂); [ idtac | assumption ].
 apply Max.le_max_r.

 transitivity (max n₁ n₂); [ idtac | assumption ].
 apply Max.le_max_l.
Qed.

Definition polyn_add α (f : field α) p₁ p₂ :=
  {| pseries := (pseries p₁ .+ f pseries p₂)%ser;
     finprop := finprop_add p₁ p₂ |}.

(* multiplication *)

Lemma finprop_mul : ∀ α (f : field α) (p₁ p₂ : polyn f),
  ∃ n, ∀ m, n ≤ m → ((pseries p₁ .* f pseries p₂)%ser .[m] .= f .0 f)%F.
Proof.
intros α f p₁ p₂.
pose proof (finprop p₁) as P₁.
pose proof (finprop p₂) as P₂.
destruct P₁ as (n₁, Hn₁).
destruct P₂ as (n₂, Hn₂).
exists (n₁ + n₂)%nat; intros m Hnn; simpl.
unfold convol_mul.
apply all_0_sigma_0; intros i (_, Hi).
destruct (le_dec n₁ i) as [H₁| H₁].
 rewrite Hn₁; [ idtac | assumption ].
 rewrite fld_mul_0_l; reflexivity.

 destruct (le_dec n₂ (m - i)) as [H₂| H₂].
  rewrite Hn₂; [ idtac | assumption ].
  rewrite fld_mul_0_r; reflexivity.

  exfalso; omega.
Qed.

Definition polyn_mul α (f : field α) p₁ p₂ :=
  {| pseries := (pseries p₁ .* f pseries p₂)%ser;
     finprop := finprop_mul p₁ p₂ |}.

(* Horner's algorithm : to be updated
Definition apply_polyn α β γ
    (zero_plus_v : β → α) (add_v_coeff : α → β → α) (mul_v_x : α → γ → α)
    (pol : polyn β) (x : γ) :=
  List.fold_right (λ c accu, add_v_coeff (mul_v_x accu x) c)
    (zero_plus_v (an pol)) (al pol).
*)
