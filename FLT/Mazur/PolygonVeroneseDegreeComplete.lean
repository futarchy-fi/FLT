/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseHomogeneousReduction

/-!
# Completeness of the actual compatible homogeneous modules

Evaluation detects adic congruence. A Cauchy sequence therefore stabilizes
at each original stage; these values assemble into its limit. No finiteness
of the compatible module is required.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (d : ℕ)

/-- Actual stage equality is precisely congruence by the corresponding coefficient ideal power. -/
theorem exactVeroneseDegree_smodEq (m : ℕ)
    (s t : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d) :
    s ≡ t [SMOD (parameterIdeal K ^ (m + 1) •
      (⊤ : Submodule (PowerSeries K)
        (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d)))] ↔
      compatibleDegreeEval K n h m (exactVeroneseStep K n h * d) s =
        compatibleDegreeEval K n h m (exactVeroneseStep K n h * d) t := by
  rw [SModEq.sub_mem, ← exactVeroneseDegree_ker, LinearMap.mem_ker, map_sub, sub_eq_zero]
  rfl

/-- All original evaluations separate compatible homogeneous sections adically. -/
theorem exactVeroneseDegree_hausdorff : IsHausdorff (parameterIdeal K)
    (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d) := by
  refine ⟨fun s hs ↦ ?_⟩
  apply Subtype.ext
  apply compatibleEval_ext K n h
  intro m
  exact congrArg Subtype.val ((exactVeroneseDegree_smodEq K n h d m s 0).mp (hs (m + 1)))

/-- A Cauchy sequence converges by retaining its stabilized value in every original stage. -/
theorem exactVeroneseDegree_precomplete : IsPrecomplete (parameterIdeal K)
    (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d) := by
  refine ⟨fun f hf ↦ ?_⟩
  let s := fun m ↦ compatibleDegreeEval K n h m (exactVeroneseStep K n h * d) (f (m + 1))
  have hs : ∀ m, boundarySeriesDegreeTransition K n h m
      (exactVeroneseStep K n h * d) (s (m + 1)) = s m := by
    intro m
    dsimp only [s]
    rw [compatibleDegreeEval_adjacent]
    exact ((exactVeroneseDegree_smodEq K n h d m _ _).mp (hf (Nat.le_succ (m + 1)))).symm
  refine ⟨compatibleDegreeOfAdjacent K n h (exactVeroneseStep K n h * d) s hs, ?_⟩
  intro m
  cases m with
  | zero => simpa only [pow_zero, one_smul] using SModEq.top
  | succ m =>
    apply (exactVeroneseDegree_smodEq K n h d m _ _).mpr
    apply Subtype.ext
    exact (compatibleDegreeOfAdjacent_eval K n h _ s hs m).symm

/-- The actual inverse-limit homogeneous module is complete without a finiteness hypothesis. -/
theorem exactVeroneseDegree_complete : IsAdicComplete (parameterIdeal K)
    (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d) where
  toIsHausdorff := exactVeroneseDegree_hausdorff K n h d
  toIsPrecomplete := exactVeroneseDegree_precomplete K n h d

end FLT.Mazur.PolygonInfinitesimalStages
