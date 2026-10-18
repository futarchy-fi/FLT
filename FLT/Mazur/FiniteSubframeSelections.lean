/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Set

/-!
# Unordered strict subframe selections

Choose one labeling for each subset of the required size. Permuting the ambient
frame permutes these subsets, whose number is a binomial coefficient rather than
the number of embeddings. The construction requires no division by a factorial.
-/

@[expose] public noncomputable section
namespace FLT.Mazur

/-- Unordered selections of exactly `m` labels. -/
def SubframeSelections (I : Type*) (m : ℕ) :=
  {s : Finset I // s.card = m}

namespace SubframeSelections
variable {I J : Type*} [Fintype I] [Fintype J]

instance (m : ℕ) : Fintype (SubframeSelections I m) := by
  classical
  unfold SubframeSelections
  infer_instance

/-- Count each subset once, without the factorial from its possible labelings. -/
theorem card (m : ℕ) : Fintype.card (SubframeSelections I m) =
    (Fintype.card I).choose m := by
  classical
  change Fintype.card {s : Finset I // s.card = m} = _
  rw [Fintype.card_subtype]
  simpa only [Finset.powerset_univ, Finset.powersetCard_eq_filter,
    Finset.card_univ] using Finset.card_powersetCard m (Finset.univ : Finset I)

/-- A chosen labeling of an unordered selection by the smaller frame. -/
def labeling (s : SubframeSelections I (Fintype.card J)) : J ≃ s.val :=
  Fintype.equivOfCardEq (by rw [Fintype.card_coe, s.property])

/-- The actual embedding selected by this labeling. -/
def embedding (s : SubframeSelections I (Fintype.card J)) : J ↪ I :=
  (labeling s).toEmbedding.trans (Function.Embedding.subtype _)

omit [Fintype I] in
/-- The chosen embedding has exactly the prescribed image. -/
theorem range_embedding (s : SubframeSelections I (Fintype.card J)) :
    Set.range (embedding s : J → I) = (s.val : Set I) := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    exact (labeling s j).property
  · intro hi
    refine ⟨(labeling s).symm ⟨i, hi⟩, ?_⟩
    exact congrArg Subtype.val ((labeling s).apply_symm_apply ⟨i, hi⟩)

/-- Ambient relabeling is a bijection of unordered selections. -/
def permute (m : ℕ) (σ : Equiv.Perm I) :
    SubframeSelections I m ≃ SubframeSelections I m where
  toFun s := ⟨s.val.map σ.toEmbedding, (Finset.card_map _).trans s.property⟩
  invFun s := ⟨s.val.map σ.symm.toEmbedding, (Finset.card_map _).trans s.property⟩
  left_inv s := by
    apply Subtype.ext
    ext i
    simp
  right_inv s := by
    apply Subtype.ext
    ext i
    simp

omit [Fintype I] in
/-- The chosen relabeling and the relabeled chosen embedding have the same image. -/
theorem range_permute_embedding (σ : Equiv.Perm I)
    (s : SubframeSelections I (Fintype.card J)) :
    Set.range (embedding (permute _ σ s) : J → I) =
      Set.range ((embedding s).trans σ.toEmbedding : J → I) := by
  rw [range_embedding]
  change (↑(s.val.map σ.toEmbedding) : Set I) = Set.range (σ ∘ embedding s)
  rw [Set.range_comp, range_embedding]
  exact Finset.coe_map _ _

end SubframeSelections
end FLT.Mazur
