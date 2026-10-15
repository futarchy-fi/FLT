/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticVeroneseExactness
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Actual adic reduction isomorphisms in each retained homogeneous degree

The proved evaluation kernels are the action of the actual integral-base
ideal powers. The first isomorphism theorem identifies these adic quotients
with the original homogeneous stage modules, retaining every evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

include hne hgen in
/-- The actual homogeneous evaluation kernel is the integral-base ideal power acting on it. -/
theorem exactVeroneseDegree_ker (d m : ℕ) :
    LinearMap.ker (compatibleDegreeEval A π n h m (exactVeroneseStep A π hne hgen n h * d)) =
      ideal A π ^ (m + 1) •
        (⊤ : Submodule A
          (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d)) := by
  ext s
  rw [LinearMap.mem_ker, ideal, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul]
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  exact exactVeroneseDegree_kernel A π hne hgen n h d m s

/-- Actual reduction modulo the coefficient ideal power recovers each original retained degree. -/
def exactVeroneseDegreeReduction (d m : ℕ) :
    (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d ⧸
      (ideal A π ^ (m + 1) • ⊤ : Submodule A
        (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d))) ≃ₗ[A]
      boundaryIntegralDegree A π n h m (exactVeroneseStep A π hne hgen n h * d) :=
  (Submodule.quotEquivOfEq _ _ (exactVeroneseDegree_ker A π hne hgen n h d m).symm).trans
    ((compatibleDegreeEval A π n h m
      (exactVeroneseStep A π hne hgen n h * d)).quotKerEquivOfSurjective
      (exactVeroneseDegree_surjective A π hne hgen n h d m))

/-- The reduction isomorphism is the original stage evaluation on every representative. -/
theorem exactVeroneseDegreeReduction_mk (d m : ℕ)
    (s : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d) :
    exactVeroneseDegreeReduction A π hne hgen n h d m (Submodule.Quotient.mk s) =
      compatibleDegreeEval A π n h m (exactVeroneseStep A π hne hgen n h * d) s := by
  rw [exactVeroneseDegreeReduction, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ s

/-- Adjacent homogeneous reductions retain the original transition maps on all representatives. -/
theorem exactVeroneseDegreeReduction_adjacent (d m : ℕ)
    (s : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d) :
    boundaryIntegralDegreeTransition A π n h m (exactVeroneseStep A π hne hgen n h * d)
      (exactVeroneseDegreeReduction A π hne hgen n h d (m + 1) (Submodule.Quotient.mk s)) =
      exactVeroneseDegreeReduction A π hne hgen n h d m (Submodule.Quotient.mk s) := by
  rw [exactVeroneseDegreeReduction_mk, exactVeroneseDegreeReduction_mk]
  exact compatibleDegreeEval_adjacent A π n h m _ s

end FLT.Mazur.PolygonArithmeticStages
