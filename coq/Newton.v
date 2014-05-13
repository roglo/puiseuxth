(* Newton.v *)

Require Import Utf8.
Require Import QArith.

Require Import ConvexHull.

Set Implicit Arguments.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Record newton_segment := mkns
  { ini_pt : (Q * Q);
    fin_pt : (Q * Q);
    oth_pts : list (Q * Q) }.

Fixpoint list_map_pairs α β (f : α → α → β) l :=
  match l with
  | [] => []
  | [x₁] => []
  | [x₁ … ([x₂ … l₂] as l₁)] => [f x₁ x₂ … list_map_pairs f l₁]
  end.

Definition newton_segment_of_pair hsj hsk :=
  mkns (vert hsj) (vert hsk) (edge hsj).

Definition γ ns :=
  (snd (ini_pt ns) - snd (fin_pt ns)) / (fst (fin_pt ns) - fst (ini_pt ns)).

Definition β ns :=
  snd (ini_pt ns) + fst (ini_pt ns) * γ ns.

Lemma list_map_pairs_length {A B} : ∀ (f : A → A → B) l₁ l₂,
  list_map_pairs f l₁ = l₂
  → List.length l₂ = pred (List.length l₁).
Proof.
intros f l₁ l₂ H.
subst l₂.
destruct l₁ as [| x]; [ reflexivity | idtac ].
revert x.
induction l₁ as [| y]; [ reflexivity | intros ].
simpl in IHl₁ |- *.
apply eq_S, IHl₁.
Qed.

Lemma list_map_pairs_cons_cons : ∀ A B (f : A → A → B) x y l,
  list_map_pairs f [x; y … l] = [f x y … list_map_pairs f [y … l]].
Proof. reflexivity. Qed.
