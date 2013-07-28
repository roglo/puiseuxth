(* $Id: Puiseux_series.v,v 1.49 2013-07-28 11:22:58 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Misc.
Require Import Series.

Set Implicit Arguments.

Record puiseux_series α := mkps
  { ps_terms : series α;
    ps_valnum : Z;
    ps_comden : positive }.

(* [series_head] skip the possible terms with null coefficients and return
   the sub-series of the initial series whose coefficient of the first term
   is not null. E.g.: applied to
       0+0x³+5x⁵+0x⁷+3x⁸+...
   would return
       5x⁵+0x⁷+3x⁸+... *)
Definition series_head : ∀ α, (α → Prop) → nat → series α → option (nat * α).
Proof. Admitted.

Definition valuation α fld (ps : puiseux_series α) :=
  match series_head (fld_eq fld (zero fld)) 0 (ps_terms ps) with
  | Some (n, c) =>
      Some (Qmake (Z.add (ps_valnum ps) (Z.of_nat n)) (ps_comden ps))
  | None =>
      None
  end.

Definition valuation_coeff α fld (ps : puiseux_series α) :=
  match series_head (fld_eq fld (zero fld)) 0 (ps_terms ps) with
  | Some (_, c) => c
  | None => zero fld
  end.

Definition normal_terms α (fld : field α) cd₁ s :=
  {| terms i :=
       if zerop (i mod (S cd₁)) then terms s (i / S cd₁) else zero fld;
     stop :=
       match stop s with
       | Some st => Some (st * S cd₁)%nat
       | None => None
       end |}.

Definition normal α (fld : field α) l cd ms :=
  {| ps_terms := normal_terms fld (cd - 1) (ps_terms ms);
     ps_valnum := Z.mul (ps_valnum ms) (Z.of_nat cd);
     ps_comden := l |}.

(* ps_add *)

Definition series_pad_left α (fld : field α) n s :=
  {| terms i := if lt_dec i n then zero fld else terms s (i - n)%nat;
     stop :=
       match stop s with
       | Some st => Some (st - n)%nat
       | None => None
       end |}.

Definition lcm_div α (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (ps_comden ps₁) (ps_comden ps₂) in
  NPeano.div (Pos.to_nat l) (Pos.to_nat (ps_comden ps₁)).

Definition valnum_diff_0 α (fld : field α) ps₁ ps₂ :=
  {| ps_terms := series_add fld (ps_terms ps₁) (ps_terms ps₂);
     ps_valnum := ps_valnum ps₁;
     ps_comden := ps_comden ps₁ |}.

Definition valnum_diff_pos α (fld : field α) n ps₁ ps₂ :=
  {| ps_terms :=
       series_add fld (ps_terms ps₁)
         (series_pad_left fld (Pos.to_nat n) (ps_terms ps₂));
     ps_valnum := ps_valnum ps₁;
     ps_comden := ps_comden ps₁ |}.

Definition valnum_diff_neg α (fld : field α) n ps₁ ps₂ :=
  {| ps_terms :=
       series_add fld (series_pad_left fld (Pos.to_nat n) (ps_terms ps₁))
         (ps_terms ps₂);
     ps_valnum := ps_valnum ps₂;
     ps_comden := ps_comden ps₂ |}.

Definition valnum_diff α (fld : field α) ms₁ ms₂ d :=
  match d with
  | Z0 => valnum_diff_0 fld ms₁ ms₂
  | Zpos n => valnum_diff_pos fld n ms₁ ms₂
  | Zneg n => valnum_diff_neg fld n ms₁ ms₂
  end.

Definition ps_add α fld (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (ps_comden ps₁) (ps_comden ps₂) in
  let ms₁ := normal fld l (lcm_div ps₁ ps₂) ps₁ in
  let ms₂ := normal fld l (lcm_div ps₂ ps₁) ps₂ in
  valnum_diff fld ms₁ ms₂ (Z.sub (ps_valnum ms₂) (ps_valnum ms₁)).

(* ps_mul *)

Fixpoint sum_mul_coeff α (fld : field α) i ni₁ s₁ s₂ :=
  match ni₁ with
  | O => None
  | S ni =>
      match sum_mul_coeff fld (S i) ni s₁ s₂ with
      | Some c =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (add fld (mul fld c₁ c₂) c)
              | None => Some c
              end
          | None => Some c
          end
      | None =>
          match series_nth i s₁ with
          | Some c₁ =>
              match series_nth ni s₂ with
              | Some c₂ => Some (mul fld c₁ c₂)
              | None => None
              end
          | None => None
          end
      end
  end.

Definition ps_mul_term α fld (s₁ s₂ : series α) :=
  {| terms i :=
       match sum_mul_coeff fld 0 (S i) s₁ s₂ with
       | Some c => c
       | None => zero fld
       end;
     stop :=
       match stop s₁ with
       | Some st₁ =>
           match stop s₂ with
           | Some st₂ => Some (max st₁ st₂)
           | None => None
           end
       | None => None
       end |}.

Definition ps_mul α fld (ms₁ ms₂ : puiseux_series α) :=
  let l := Plcm (ps_comden ms₁) (ps_comden ms₂) in
  let ms₁ :=
    normal fld l (NPeano.div (Pos.to_nat l) (Pos.to_nat (ps_comden ms₁))) ms₁
  in
  let ms₂ :=
    normal fld l (NPeano.div (Pos.to_nat l) (Pos.to_nat (ps_comden ms₂))) ms₂
  in
  {| ps_terms := ps_mul_term fld (ps_terms ms₁) (ps_terms ms₂);
     ps_valnum := Z.add (ps_valnum ms₁) (ps_valnum ms₂);
     ps_comden := l |}.

(* *)

Lemma Zmatch_minus : ∀ α x y (a : α) f g,
  match (x - y)%Z with
  | 0%Z => a
  | Zpos n => f n
  | Zneg n => g n
  end =
  match (y - x)%Z with
  | 0%Z => a
  | Zpos n => g n
  | Zneg n => f n
  end.
Proof.
intros α x y a f g.
remember (x - y)%Z as xy.
symmetry in Heqxy.
destruct xy.
 apply Zminus_eq in Heqxy.
 subst x; rewrite Zminus_diag; reflexivity.

 do 3 (apply Z.sub_move_l in Heqxy; symmetry in Heqxy).
 rewrite Z.sub_opp_l in Heqxy.
 rewrite Z.opp_involutive in Heqxy.
 rewrite Heqxy; reflexivity.

 do 3 (apply Z.sub_move_l in Heqxy; symmetry in Heqxy).
 rewrite Z.sub_opp_l in Heqxy.
 rewrite Z.opp_involutive in Heqxy.
 rewrite Heqxy; reflexivity.
Qed.

Lemma Zmatch_split : ∀ α x (a₁ a₂ : α) f₁ f₂ g₁ g₂,
  a₁ = a₂
  → (∀ n, f₁ n = f₂ n)
    → (∀ n, g₁ n = g₂ n)
      → match x with
        | 0%Z => a₁
        | Zpos n => f₁ n
        | Zneg n => g₁ n
        end =
        match x with
        | 0%Z => a₂
        | Zpos n => f₂ n
        | Zneg n => g₂ n
        end.
Proof.
intros α x a₁ a₂ f₁ f₂ g₁ g₂ Ha Hf Hg.
destruct x; [ assumption | apply Hf | apply Hg ].
Qed.

Inductive eq_ps α (fld : field α) ps₁ ps₂ :=
  eq_ps_norm :
    eq_series fld (ps_terms ps₁) (ps_terms ps₂)
    → ps_valnum ps₁ = ps_valnum ps₂
      → ps_comden ps₁ = ps_comden ps₂
        → eq_ps fld ps₁ ps₂.

Theorem ps_compat : ∀ α (fld : field α) ps₁ ps₂,
  eq_series fld (ps_terms ps₁) (ps_terms ps₂)
  → ps_valnum ps₁ = ps_valnum ps₂
    → ps_comden ps₁ = ps_comden ps₂
      → eq_ps fld ps₁ ps₂.
Proof.
intros α fld ps₁ ps₂ Hs Hv Hc.
constructor; assumption.
Qed.

Add Parametric Morphism α (fld : field α) : (@mkps α) with 
signature (eq_series fld) ==> eq ==> eq ==> eq_ps fld as mkps_morph.
Proof.
intros s₁ s₂ Hs v c.
constructor; [ assumption | reflexivity | reflexivity ].
Qed.

Add Parametric Morphism α (fld : field α) : (@ps_terms α) with 
signature (eq_ps fld) ==> eq_series fld as ps_terms_morph.
Proof.
intros ps₁ ps₂ Hps.
inversion Hps; assumption.
Qed.

Add Parametric Morphism α (fld : field α) : (@series_pad_left α fld) with 
signature eq ==> eq_series fld ==> eq_series fld as series_pad_morph.
Proof.
intros n s₁ s₂ H.
constructor; simpl.
 intros i.
 destruct (lt_dec i n); [ reflexivity | idtac ].
 inversion H; apply H0.

 inversion H; rewrite H1; reflexivity.
Qed.

(* *)

Lemma ps_add_comm : ∀ α (fld : field α) ps₁ ps₂,
  eq_ps fld (ps_add fld ps₁ ps₂) (ps_add fld ps₂ ps₁).
Proof.
intros α fld ps₁ ps₂.
unfold ps_add, valnum_diff; simpl.
rewrite Zmatch_minus.
rewrite Plcm_comm.
remember
 (ps_valnum ps₁ * Z.of_nat (lcm_div ps₁ ps₂) -
  ps_valnum ps₂ * Z.of_nat (lcm_div ps₂ ps₁))%Z as d.
constructor; destruct d; simpl; try rewrite series_add_comm; try reflexivity.
apply Zminus_eq; symmetry; assumption.
Qed.

Lemma Plcm_diag : ∀ a, Plcm a a = a.
Proof.
intros a.
unfold Plcm.
rewrite Z.lcm_diag.
reflexivity.
Qed.

Lemma same_comden_valnum_diff : ∀ α (fld : field α) ps₁ ps₂ d,
  ps_comden ps₁ = ps_comden ps₂
  → ps_comden (valnum_diff fld ps₁ ps₂ d) = ps_comden ps₁.
Proof.
intros α fld ps₁ ps₂ d H.
unfold valnum_diff; simpl.
destruct d; [ reflexivity | reflexivity | symmetry; assumption ].
Qed.

Axiom functional_extensionality : ∀ α β (f g : α → β),
  (∀ x, f x = g x) → f = g.

Lemma normal_terms_0 : ∀ α (fld : field α) t, normal_terms fld 0 t = t.
Proof.
intros α fld t.
unfold normal_terms.
destruct t.
f_equal.
 apply functional_extensionality.
 intros i.
 rewrite Nat.div_1_r.
 reflexivity.

 simpl.
 destruct stop.
  rewrite mult_1_r; reflexivity.

  reflexivity.
Qed.

Lemma series_pad_add_distr : ∀ α (fld : field α) s₁ s₂ n,
  eq_series fld
    (series_pad_left fld n (series_add fld s₁ s₂))
    (series_add fld (series_pad_left fld n s₁) (series_pad_left fld n s₂)).
Proof.
intros α fld s₁ s₂ n.
constructor.
 intros i.
 unfold series_add; simpl.
 destruct (lt_dec i n) as [Hlt| Hge]; [ idtac | reflexivity ].
 symmetry; apply fld_add_neutral.

 simpl.
 destruct (stop s₁) as [n₁| ]; [ idtac | reflexivity ].
 destruct (stop s₂) as [n₂| ]; [ idtac | reflexivity ].
 f_equal.
 rewrite Nat.sub_max_distr_r; reflexivity.
Qed.

Lemma zzz : ∀ α (fld : field α) ps₁ ps₂ ps₃ l,
  l = ps_comden ps₁
  → l = ps_comden ps₂
    → l = ps_comden ps₃
      → eq_ps fld
          (ps_add fld (ps_add fld ps₁ ps₂) ps₃)
          (ps_add fld ps₁ (ps_add fld ps₂ ps₃)).
Proof.
intros α fld ps₁ ps₂ ps₃ l H₁ H₂ H₃.
constructor.
 unfold ps_add; simpl.
 rewrite <- H₁, <- H₂, <- H₃.
 rewrite Plcm_diag.
 unfold lcm_div.
 rewrite <- H₁, <- H₂, <- H₃.
 rewrite Plcm_diag.
 rewrite Nat.div_same.
  simpl.
  unfold normal; simpl.
  do 3 rewrite Zmult_1_r.
  rewrite same_comden_valnum_diff; [ idtac | reflexivity ].
  rewrite same_comden_valnum_diff; [ idtac | reflexivity ].
  simpl.
  rewrite Plcm_diag.
  rewrite Nat.div_same.
   simpl.
   do 4 rewrite Zmult_1_r.
   do 5 rewrite normal_terms_0.
   remember (ps_valnum ps₂ - ps_valnum ps₁)%Z as v₂₁.
   symmetry in Heqv₂₁.
   destruct v₂₁ as [| v₂₁| v₂₁]; simpl.
    remember (ps_valnum ps₃ - ps_valnum ps₂)%Z as v₃₂.
    symmetry in Heqv₃₂.
    destruct v₃₂ as [| v₃₂| v₃₂]; simpl.
     rewrite Heqv₂₁; simpl.
     apply Zminus_eq in Heqv₃₂; rewrite Heqv₃₂, Heqv₂₁; simpl.
     apply series_add_assoc.

     rewrite Heqv₂₁; simpl.
     apply Zminus_eq in Heqv₂₁; rewrite <- Heqv₂₁, Heqv₃₂; simpl.
     apply series_add_assoc.

     apply Zminus_eq in Heqv₂₁; rewrite <- Heqv₂₁, Heqv₃₂; simpl.
     rewrite series_pad_add_distr.
     apply series_add_assoc.

    remember (ps_valnum ps₃ - ps_valnum ps₂)%Z as v₃₂.
    symmetry in Heqv₃₂.
    destruct v₃₂ as [| v₃₂| v₃₂]; simpl.
     rewrite Heqv₂₁; simpl.
     apply Zminus_eq in Heqv₃₂; rewrite Heqv₃₂, Heqv₂₁; simpl.
     rewrite series_pad_add_distr.
     apply series_add_assoc.

     rewrite Heqv₂₁; simpl.
     eapply Zplus_eq_compat in Heqv₂₁; [ idtac | eassumption ].
     rewrite Z.add_sub_assoc, Z.sub_simpl_r in Heqv₂₁.
     rewrite Heqv₂₁; simpl.
     Focus 1.
bbb.

Lemma ps_add_assoc : ∀ α (fld : field α) ps₁ ps₂ ps₃,
  eq_ps fld
    (ps_add fld (ps_add fld ps₁ ps₂) ps₂)
    (ps_add fld ps₁ (ps_add fld ps₂ ps₃)).
Proof.
intros α fld ps₁ ps₂ ps₃.
constructor.
 unfold ps_add; simpl.
 remember
  (ps_valnum ps₂ * Z.of_nat (lcm_div ps₂ ps₁) -
   ps_valnum ps₁ * Z.of_nat (lcm_div ps₁ ps₂)) as v₁.
 remember
  (ps_valnum ps₃ * Z.of_nat (lcm_div ps₃ ps₂) -
   ps_valnum ps₂ * Z.of_nat (lcm_div ps₂ ps₃)) as v₂.
bbb.
