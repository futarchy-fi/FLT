/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredPoleLeadingCoefficient
public import FLT.Mazur.PolygonCompletePointMonomialBasis

/-!
# The cubic relation of the original pole functions

The square of the original pole-three function expands in the original
sixth pole space. Its x³ coefficient is nonzero because its exact order is
six, while the other five basis monomials have order at most five.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve Module
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The original y², regarded as a vector in the sixth pole space. -/
def completeCartesianPointYSquare (i : Fin n) :
    divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1 6 :=
  ⟨(completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)) ^ 2, by
    rw [mem_divisorPoleSubmodule]
    simpa only [pow_zero, one_mul] using
      completeCartesianPoint_monomial_mem K n h L s p q hs i 0 2⟩

/-- The cubic coefficients are the actual unique coordinates of the original y². -/
def completeCartesianPointCubicCoefficients (i : Fin n) : Fin 6 → L :=
  (completeCartesianPointMonomialBasis K n h L s p q hs i 6).repr
    (completeCartesianPointYSquare K n h L s p q hs i)

/-- Original monomials equipped with the actual base-field scalar action. -/
def completeCartesianPointMonomialVector (i : Fin n) (j : ℕ) :
    divisorComplementModule q (completeCartesianMarking K n h s p q hs i).ker :=
  completeCartesianPointMonomial K n h L s p q hs i j

/-- The original functions satisfy their actual degree-six basis expansion. -/
theorem completeCartesianPoint_cubic_sum (i : Fin n) :
    ∑ j : Fin 6, completeCartesianPointCubicCoefficients K n h L s p q hs i j •
      completeCartesianPointMonomialVector K n h L s p q hs i j =
      (completeCartesianPointYSquare K n h L s p q hs i :
        divisorComplementModule q (completeCartesianMarking K n h s p q hs i).ker) := by
  have he := FilteredPoleBasis.sum_repr_coe _
    (completeCartesianPointMonomialBasis K n h L s p q hs i 6)
    (completeCartesianPointYSquare K n h L s p q hs i)
  simpa only [completeCartesianPointMonomialBasis_apply,
    completeCartesianPointMonomialVector, completeCartesianPointCubicCoefficients] using he

/-- The coefficient of x³ is nonzero on every original retained field square. -/
theorem completeCartesianPointCubicCoefficients_last_ne_zero (i : Fin n) :
    completeCartesianPointCubicCoefficients K n h L s p q hs i (Fin.last 5) ≠ 0 := by
  apply FilteredPoleBasis.last_repr_ne_zero
    (divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1)
    (completeCartesianPointMonomialBasis K n h L s p q hs i 6)
  · intro j
    rw [completeCartesianPointMonomialBasis_apply]
    exact divisorPoleSubmodule_mono q _ (WeightedPoleMonomials.order_le 5 j)
      (completeCartesianPointMonomial_mem K n h L s p q hs i j)
  · rw [mem_divisorPoleSubmodule]
    simpa only [completeCartesianPointYSquare, pow_zero, one_mul] using
      completeCartesianPoint_monomial_not_mem K n h L s p q hs i 0 2 (by decide)

end FLT.Mazur.PolygonInfinitesimalStages
