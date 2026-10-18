/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Invariance from exchanges across a selected finite subset

An element fixed by the setwise stabilizer of a selected subset is fixed by
all permutations precisely when it is fixed by swaps of a selected and an
omitted label. These are the additional equations needed for strict subframes.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteEmbeddingExchangeInvariance
open Equiv
variable {I J M : Type*} [DecidableEq I]

/-- Swapping labels with the same membership status preserves membership. -/
theorem swap_mem_iff (S : Set I) (a b x : I) (hab : a ∈ S ↔ b ∈ S) :
    swap a b x ∈ S ↔ x ∈ S := by
  classical
  by_cases ha : x = a
  · subst x
    simpa only [swap_apply_left] using hab.symm
  by_cases hb : x = b
  · subst x
    simpa only [swap_apply_right] using hab
  rw [swap_apply_of_ne_of_ne ha hb]

/-- An internal or external swap preserves the image of a selected embedding. -/
theorem range_swap_eq (ι : J ↪ I) (a b : I)
    (hab : a ∈ Set.range ι ↔ b ∈ Set.range ι) :
    Set.range (ι.trans (swap a b).toEmbedding : J → I) = Set.range ι := by
  classical
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact (swap_mem_iff (Set.range ι) a b (ι j) hab).mpr ⟨j, rfl⟩
  · intro hx
    obtain ⟨j, hj⟩ := (swap_mem_iff (Set.range ι) a b x hab).mpr hx
    refine ⟨j, ?_⟩
    change swap a b (ι j) = x
    rw [hj, swap_apply_self]

variable [Finite I] [MulAction (Perm I) M]

/-- Setwise stabilizers and crossing exchanges generate every required invariance equation. -/
theorem fixed_of_crossing_swaps (ι : J ↪ I) (x : M)
    (hr : ∀ σ : Perm I,
      Set.range (ι.trans σ.toEmbedding : J → I) = Set.range ι → σ • x = x)
    (hs : ∀ a ∈ Set.range ι, ∀ b ∉ Set.range ι, swap a b • x = x)
    (σ : Perm I) : σ • x = x := by
  classical
  have hswap (a b : I) : swap a b • x = x := by
    by_cases ha : a ∈ Set.range ι
    · by_cases hb : b ∈ Set.range ι
      · exact hr _ (range_swap_eq ι a b (iff_of_true ha hb))
      · exact hs a ha b hb
    · by_cases hb : b ∈ Set.range ι
      · rw [swap_comm]
        exact hs b hb a ha
      · exact hr _ (range_swap_eq ι a b (iff_of_false ha hb))
  induction σ using Perm.swap_induction_on with
  | one => exact one_smul _ _
  | swap_mul σ a b _ ih => rw [mul_smul, ih, hswap]

/-- Only exchanges across the selected image remain after setwise invariance is known. -/
theorem fixed_iff_crossing_swaps (ι : J ↪ I) (x : M)
    (hr : ∀ σ : Perm I,
      Set.range (ι.trans σ.toEmbedding : J → I) = Set.range ι → σ • x = x) :
    (∀ σ : Perm I, σ • x = x) ↔
      ∀ a ∈ Set.range ι, ∀ b ∉ Set.range ι, swap a b • x = x :=
  ⟨fun h a _ b _ ↦ h (swap a b), fixed_of_crossing_swaps ι x hr⟩

end FLT.Mazur.FiniteEmbeddingExchangeInvariance
