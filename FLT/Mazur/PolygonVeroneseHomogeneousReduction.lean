/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseDegreeExactness
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Actual adic reduction isomorphisms in each retained homogeneous degree

The proved evaluation kernels are the action of the actual complete-base
ideal powers. The first isomorphism theorem identifies these adic quotients
with the original homogeneous stage modules, retaining every evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual homogeneous evaluation kernel is the complete-base ideal power acting on it. -/
theorem exactVeroneseDegree_ker (d m : ℕ) :
    LinearMap.ker (compatibleDegreeEval K n h m (exactVeroneseStep K n h * d)) =
      parameterIdeal K ^ (m + 1) •
        (⊤ : Submodule (PowerSeries K)
          (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d)) := by
  ext s
  rw [LinearMap.mem_ker, parameterIdeal, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul]
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  exact exactVeroneseDegree_kernel K n h d m s

/-- Actual reduction modulo the coefficient ideal power recovers each original retained degree. -/
def exactVeroneseDegreeReduction (d m : ℕ) :
    (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d ⧸
      (parameterIdeal K ^ (m + 1) • ⊤ : Submodule (PowerSeries K)
        (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d))) ≃ₗ[PowerSeries K]
      boundarySeriesDegree K n h m (exactVeroneseStep K n h * d) :=
  (Submodule.quotEquivOfEq _ _ (exactVeroneseDegree_ker K n h d m).symm).trans
    ((compatibleDegreeEval K n h m (exactVeroneseStep K n h * d)).quotKerEquivOfSurjective
      (exactVeroneseDegree_surjective K n h d m))

/-- The reduction isomorphism is the original stage evaluation on every representative. -/
theorem exactVeroneseDegreeReduction_mk (d m : ℕ)
    (s : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d) :
    exactVeroneseDegreeReduction K n h d m (Submodule.Quotient.mk s) =
      compatibleDegreeEval K n h m (exactVeroneseStep K n h * d) s := by
  rw [exactVeroneseDegreeReduction, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ s

/-- Adjacent homogeneous reductions retain the original transition maps on all representatives. -/
theorem exactVeroneseDegreeReduction_adjacent (d m : ℕ)
    (s : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d) :
    boundarySeriesDegreeTransition K n h m (exactVeroneseStep K n h * d)
      (exactVeroneseDegreeReduction K n h d (m + 1) (Submodule.Quotient.mk s)) =
      exactVeroneseDegreeReduction K n h d m (Submodule.Quotient.mk s) := by
  rw [exactVeroneseDegreeReduction_mk, exactVeroneseDegreeReduction_mk]
  exact compatibleDegreeEval_adjacent K n h m _ s

end FLT.Mazur.PolygonInfinitesimalStages
