(* $Id: Puiseux_series.v,v 1.13 2013-07-23 17:54:54 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.

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

CoFixpoint normal_terms α fld n cd₁ (s : series α) :=
  match s with
  | Term c ss =>
      match n with
      | O => Term c (normal_terms fld cd₁ cd₁ ss)
      | S n₁ => Term (zero fld) (normal_terms fld n₁ cd₁ s)
      end
  | End => End _
  end.

Definition normal α (fld : field α) l cd ms :=
  {| ps_terms := normal_terms fld 0 (cd - 1) (ps_terms ms);
     ps_valnum := Z.mul (ps_valnum ms) (Z.of_nat cd);
     ps_comden := l |}.

Definition Plcm a b := Z.to_pos (Z.lcm (Zpos a) (Zpos b)).

(* ps_add *)

CoFixpoint series_add α (fld : field α) s₁ s₂ :=
  match s₁ with
  | Term c₁ ss₁ =>
      match s₂ with
      | Term c₂ ss₂ => Term (add fld c₁ c₂) (series_add fld ss₁ ss₂)
      | End => s₁
      end
  | End => s₂
  end.

Fixpoint series_pad_left α (fld : field α) n s :=
  match n with
  | O => s
  | S n₁ => Term (zero fld) (series_pad_left fld n₁ s)
  end.

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
  let cofix mul_loop n₁ :=
    match sum_mul_coeff fld 0 n₁ s₁ s₂ with
    | Some c => Term c (mul_loop (S n₁))
    | None => End _
    end
  in
  mul_loop 1%nat.

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
bbb.

Lemma ps_add_comm : ∀ α (fld : field α) ps₁ ps₂,
  ps_add fld ps₁ ps₂ = ps_add fld ps₂ ps₁.
Proof.
intros α fld ps₁ ps₂.
unfold ps_add; simpl.
bbb.
