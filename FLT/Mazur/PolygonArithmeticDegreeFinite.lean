/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AdicFiniteGenerationLifting
public import FLT.Mazur.PolygonArithmeticDegreeFiniteStage
public import FLT.Mazur.PolygonArithmeticDegreeComplete

/-!
# Finite compatible homogeneous modules over the complete base

The original closed-stage sections are finite by properness. Their exact
reduction comparison and the proved separation of the compatible module
lift finite generation to the actual inverse limit.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n] (d : ℕ)

/-- The closed adic quotient is finite by its actual comparison with original stage sections. -/
theorem exactVeroneseDegree_closed_finite : Module.Finite (A)
    (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d ⧸
      (ideal A π • (⊤ : Submodule (A)
        (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d)))) := by
  let _ := boundaryIntegralDegree_finite A π n h 0 (exactVeroneseStep A π hne hgen n h * d) hgen
  exact Module.Finite.equiv ((exactVeroneseDegreeReduction A π hne hgen n h d 0).symm.trans
    (Submodule.quotEquivOfEq _ _ (by rw [Nat.zero_add, pow_one])))

/-- Each actual compatible Veronese degree is finite, without assuming finiteness of a limit. -/
theorem exactVeroneseDegree_finite [IsAdicComplete (ideal A π) A] : Module.Finite (A)
    (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d) := by
  let _ := exactVeroneseDegree_hausdorff A π hne hgen n h d
  let _ := exactVeroneseDegree_closed_finite A π hne hgen n h d
  exact AdicFiniteGenerationLifting.finite_of_closed (ideal A π) _

variable [IsAdicComplete (ideal A π) A]

/-- Finite original compatible sections generate a degree simultaneously at every stage. -/
theorem exactVeroneseDegree_finiteGenerators : ∃ r : ℕ,
    ∃ f : (Fin r → A) →ₗ[A]
      compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d,
      Function.Surjective f ∧ ∀ m,
        Function.Surjective ((compatibleDegreeEval A π n h m
          (exactVeroneseStep A π hne hgen n h * d)).comp f) := by
  let _ := exactVeroneseDegree_finite A π hne hgen n h d
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' (A)
    (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d)
  exact ⟨r, f, hf, fun m ↦ (exactVeroneseDegree_surjective A π hne hgen n h d m).comp hf⟩

end FLT.Mazur.PolygonArithmeticStages
