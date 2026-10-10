/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFiniteGenerationLifting
public import FLT.Mazur.PolygonBoundaryDegreeFinite
public import FLT.Mazur.PolygonVeroneseDegreeComplete

/-!
# Finite compatible homogeneous modules over the complete base

The original closed-stage sections are finite by properness. Their exact
reduction comparison and the proved separation of the compatible module
lift finite generation to the actual inverse limit.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (d : ℕ)

/-- The closed adic quotient is finite by its actual comparison with original stage sections. -/
theorem exactVeroneseDegree_closed_finite : Module.Finite (PowerSeries K)
    (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d ⧸
      (parameterIdeal K • (⊤ : Submodule (PowerSeries K)
        (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d)))) := by
  let _ := boundarySeriesDegree_finite K n h 0 (exactVeroneseStep K n h * d)
  exact Module.Finite.equiv ((exactVeroneseDegreeReduction K n h d 0).symm.trans
    (Submodule.quotEquivOfEq _ _ (by rw [Nat.zero_add, pow_one])))

/-- Each actual compatible Veronese degree is finite, without assuming finiteness of a limit. -/
theorem exactVeroneseDegree_finite : Module.Finite (PowerSeries K)
    (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d) := by
  let _ := exactVeroneseDegree_hausdorff K n h d
  let _ := exactVeroneseDegree_closed_finite K n h d
  exact AdicFiniteGenerationLifting.finite_of_closed (parameterIdeal K) _

/-- Finite original compatible sections generate a degree simultaneously at every stage. -/
theorem exactVeroneseDegree_finiteGenerators : ∃ r : ℕ,
    ∃ f : (Fin r → PowerSeries K) →ₗ[PowerSeries K]
      compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d,
      Function.Surjective f ∧ ∀ m,
        Function.Surjective ((compatibleDegreeEval K n h m
          (exactVeroneseStep K n h * d)).comp f) := by
  let _ := exactVeroneseDegree_finite K n h d
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' (PowerSeries K)
    (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d)
  exact ⟨r, f, hf, fun m ↦ (exactVeroneseDegree_surjective K n h d m).comp hf⟩

end FLT.Mazur.PolygonInfinitesimalStages
