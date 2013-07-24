(* $Id: Puiseux_series.v,v 1.20 2013-07-24 12:17:55 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.
Require Import Zerob.

Require Import Field.
Require Import Series.

Set Implicit Arguments.

Record puiseux_series α :=
  { ps_terms : series α;
    ps_valnum : Z;
    ps_comden : positive }.

(* [series_head] skip the possible terms with null coefficients and return
   the sub-series of the initial series whose coefficient of the first term
   is not null. E.g.: applied to
       0+0x³+5x⁵+0x⁷+3x⁸+...
   would return
       5x⁵+0x⁷+3x⁸+... *)
Definition series_head : ∀ α, (α → bool) → nat → series α → option (nat * α).
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

Definition normal_terms α fld n cd₁ (s : series α) :=
  {| term := λ i, if zerob (i mod n) then term s (div i n) else zero fld;
     stop :=
       match stop s with
       | Some i => Some (i * cd₁)%nat
       | None => None
       end |}.

Definition normal α (fld : field α) l cd ms :=
  {| ps_terms := normal_terms fld 0 (cd - 1) (ps_terms ms);
     ps_valnum := Z.mul (ps_valnum ms) (Z.of_nat cd);
     ps_comden := l |}.

Definition Plcm a b := Z.to_pos (Z.lcm (Zpos a) (Zpos b)).

(* ps_add *)

Definition series_nth α (fld : field α) n s :=
  match series_nth_opt n s with
  | Some v => v
  | None => zero fld
  end.

Definition series_add α (fld : field α) s₁ s₂ :=
  {| term := λ i, add fld (series_nth fld i s₁) (series_nth fld i s₂);
     stop :=
       match stop s₁ with
       | Some n₁ =>
           match stop s₂ with
           | Some n₂ => Some (max n₁ n₂)
           | None => None
           end
       | None => None
       end |}.

(*
CoFixpoint series_add α (fld : field α) s₁ s₂ :=
  match s₁ with
  | Term c₁ ss₁ =>
      match s₂ with
      | Term c₂ ss₂ => Term (add fld c₁ c₂) (series_add fld ss₁ ss₂)
      | End => s₁
      end
  | End => s₂
  end.
*)

Definition series_pad_left α (fld : field α) n s :=
  {| term := λ i, if lt_dec i n then zero fld else series_nth fld (i - n) s;
     stop :=
       match stop s with
       | Some m => Some (m + n)%nat
       | None => None
       end |}.

Definition ps_add α fld (ps₁ ps₂ : puiseux_series α) :=
  let l := Plcm (ps_comden ps₁) (ps_comden ps₂) in
  let ms₁ :=
    normal fld l (NPeano.div (Pos.to_nat l) (Pos.to_nat (ps_comden ps₁))) ps₁
  in
  let ms₂ :=
    normal fld l (NPeano.div (Pos.to_nat l) (Pos.to_nat (ps_comden ps₂))) ps₂
  in
  let v₁ := ps_valnum ms₁ in
  let v₂ := ps_valnum ms₂ in
  match Z.sub v₂ v₁ with
  | Z0 =>
      {| ps_terms := series_add fld (ps_terms ms₁) (ps_terms ms₂);
         ps_valnum := v₁;
         ps_comden := l |}
  | Zpos n =>
      {| ps_terms :=
           series_add fld (ps_terms ms₁)
             (series_pad_left fld (Pos.to_nat n) (ps_terms ms₂));
         ps_valnum := v₁;
         ps_comden := l |}
  | Zneg n =>
      {| ps_terms :=
           series_add fld (series_pad_left fld (Pos.to_nat n) (ps_terms ms₁))
             (ps_terms ms₂);
         ps_valnum := v₂;
         ps_comden := l |}
  end.

(* ps_mul *)

Fixpoint sum_mul_coeff α (fld : field α) i ni₁ s₁ s₂ :=
  match ni₁ with
  | O => None
  | S ni =>
      match sum_mul_coeff fld (S i) ni s₁ s₂ with
      | Some c =>
          match series_nth_opt i s₁ with
          | Some c₁ =>
              match series_nth_opt ni s₂ with
              | Some c₂ => Some (add fld (mul fld c₁ c₂) c)
              | None => Some c
              end
          | None => Some c
          end
      | None =>
          match series_nth_opt i s₁ with
          | Some c₁ =>
              match series_nth_opt ni s₂ with
              | Some c₂ => Some (mul fld c₁ c₂)
              | None => None
              end
          | None => None
          end
      end
  end.

Definition ps_mul_term α fld (s₁ s₂ : series α) :=
  {| term := λ i,
       match sum_mul_coeff fld 0 (S i) s₁ s₂ with
       | Some c => c
       | None => zero fld
       end;
     stop :=
       match stop s₁ with
       | Some t₁ =>
           match stop s₂ with
           | Some t₂ => Some (max t₁ t₂)
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

Lemma Plcm_comm : ∀ a b, Plcm a b = Plcm b a.
Proof.
intros a b.
unfold Plcm.
rewrite Z.lcm_comm.
reflexivity.
Qed.

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

Lemma series_add_comm : ∀ α (fld : field α) s₁ s₂,
  series_eq fld (series_add fld s₁ s₂) (series_add fld s₂ s₁).
Proof.
intros α fld s₁ s₂.
unfold series_add, series_eq; simpl.
split.
 intros i.
 apply fld_add_comm.

 destruct (stop s₁), (stop s₂); try reflexivity.
 rewrite Max.max_comm; reflexivity.
Qed.

Definition ps_eq α (fld : field α) ps₁ ps₂ :=
  series_eq fld (ps_terms ps₁) (ps_terms ps₂) ∧
  ps_valnum ps₁ = ps_valnum ps₂ ∧
  ps_comden ps₁ = ps_comden ps₂.

Lemma ps_eq_refl : ∀ α (fld : field α) ps, ps_eq fld ps ps.
Proof.
intros α fld ps.
unfold ps_eq.
split; [ apply series_eq_refl | split; reflexivity ].
Qed.

Lemma ps_add_comm : ∀ α (fld : field α) ps₁ ps₂,
  ps_eq fld (ps_add fld ps₁ ps₂) (ps_add fld ps₂ ps₁).
Proof.
intros α fld ps₁ ps₂.
unfold ps_add; simpl.
rewrite Zmatch_minus.
rewrite Plcm_comm.
remember
 (ps_valnum ps₁ *
  Z.of_nat
    (Pos.to_nat (Plcm (ps_comden ps₂) (ps_comden ps₁)) /
     Pos.to_nat (ps_comden ps₁)) -
  ps_valnum ps₂ *
  Z.of_nat
    (Pos.to_nat (Plcm (ps_comden ps₂) (ps_comden ps₁)) /
     Pos.to_nat (ps_comden ps₂)))%Z as n.
destruct n as [| n| n].
 unfold ps_eq; simpl.
 split; [ apply series_add_comm | idtac ].
 split; [ apply Zminus_eq; symmetry; assumption | reflexivity ].

 unfold ps_eq; simpl.
 split; [ apply series_add_comm | split; reflexivity ].

 unfold ps_eq; simpl.
 split; [ apply series_add_comm | split; reflexivity ].
Qed.
