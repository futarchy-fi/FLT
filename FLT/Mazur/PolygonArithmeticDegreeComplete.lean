/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticHomogeneousReduction

/-!
# Completeness of the actual compatible homogeneous modules

Evaluation detects adic congruence. A Cauchy sequence therefore stabilizes
at each original stage; these values assemble into its limit. No finiteness
of the compatible module is required.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundaryIntegralScalars

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n] (d : ℕ)

/-- Actual stage equality is precisely congruence by the corresponding coefficient ideal power. -/
theorem exactVeroneseDegree_smodEq (m : ℕ)
    (s t : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d) :
    s ≡ t [SMOD (ideal A π ^ (m + 1) •
      (⊤ : Submodule (A)
        (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d)))] ↔
      compatibleDegreeEval A π n h m (exactVeroneseStep A π hne hgen n h * d) s =
        compatibleDegreeEval A π n h m (exactVeroneseStep A π hne hgen n h * d) t := by
  rw [SModEq.sub_mem, ← exactVeroneseDegree_ker, LinearMap.mem_ker, map_sub, sub_eq_zero]
  rfl

/-- All original evaluations separate compatible homogeneous sections adically. -/
theorem exactVeroneseDegree_hausdorff : IsHausdorff (ideal A π)
    (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d) := by
  refine ⟨fun s hs ↦ ?_⟩
  apply Subtype.ext
  apply compatibleEval_ext A π n h
  intro m
  exact congrArg Subtype.val
    ((exactVeroneseDegree_smodEq A π hne hgen n h d m s 0).mp (hs (m + 1)))

/-- A Cauchy sequence converges by retaining its stabilized value in every original stage. -/
theorem exactVeroneseDegree_precomplete : IsPrecomplete (ideal A π)
    (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d) := by
  refine ⟨fun f hf ↦ ?_⟩
  let s := fun m ↦ 
    compatibleDegreeEval A π n h m (exactVeroneseStep A π hne hgen n h * d) (f (m + 1))
  have hs : ∀ m, boundaryIntegralDegreeTransition A π n h m
      (exactVeroneseStep A π hne hgen n h * d) (s (m + 1)) = s m := by
    intro m
    dsimp only [s]
    rw [compatibleDegreeEval_adjacent]
    exact ((exactVeroneseDegree_smodEq A π hne hgen n h d m _ _).mp
      (hf (Nat.le_succ (m + 1)))).symm
  refine ⟨compatibleDegreeOfAdjacent A π n h (exactVeroneseStep A π hne hgen n h * d) s hs, ?_⟩
  intro m
  cases m with
  | zero => simpa only [pow_zero, one_smul] using SModEq.top
  | succ m =>
    apply (exactVeroneseDegree_smodEq A π hne hgen n h d m _ _).mpr
    apply Subtype.ext
    exact (compatibleDegreeOfAdjacent_eval A π n h _ s hs m).symm

/-- The actual inverse-limit homogeneous module is complete over the original integral base. -/
theorem exactVeroneseDegree_complete : IsAdicComplete (ideal A π)
    (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d) where
  toIsHausdorff := exactVeroneseDegree_hausdorff A π hne hgen n h d
  toIsPrecomplete := exactVeroneseDegree_precomplete A π hne hgen n h d

end FLT.Mazur.PolygonArithmeticStages
