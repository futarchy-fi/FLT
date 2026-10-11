/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCoordinateInjective
public import FLT.Mazur.WeierstrassAffineEvaluationRange

/-!
# The coordinate image is exactly the finite-pole subspace

Every original bounded pole space lies in the actual coordinate image.
Conversely every evaluated coordinate-ring element has a finite pole
bound. Thus surjectivity is precisely exhaustion of complement functions
by the original pole spaces, rather than an assumed coordinate property.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- Coordinate evaluation with the original bundled field-linear target. -/
def completeCartesianPointCoordinateLinear (i : Fin n) :
    (completeCartesianPointWeierstrass K n h L s p q hs i).toAffine.CoordinateRing →ₗ[L]
      divisorComplementModule q (completeCartesianMarking K n h s p q hs i).ker :=
  WeierstrassAffineEquationEvaluation.evaluationLinear
    (S := Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤)) _ _ _ _
    (completeCartesianPoint_weierstrassEquation K n h L s p q hs i)

/-- The actual image of the affine coordinate ring as a field-linear subspace. -/
def completeCartesianPointCoordinateRange (i : Fin n) :
    Submodule L (divisorComplementModule q (completeCartesianMarking K n h s p q hs i).ker) :=
  (completeCartesianPointCoordinateLinear K n h L s p q hs i).range

/-- All original monomials are recovered by undoing the nonzero normalization scalar. -/
theorem completeCartesianPointMonomial_mem_coordinateRange (i : Fin n) (j : ℕ) :
    completeCartesianPointMonomial K n h L s p q hs i j ∈
      completeCartesianPointCoordinateRange K n h L s p q hs i :=
  WeierstrassAffineEquationEvaluation.originalMonomial_mem_evaluation_range _ _ _ _ _
    (completeCartesianPointCubicCoefficients_last_ne_zero K n h L s p q hs i)
    (completeCartesianPoint_weierstrassEquation K n h L s p q hs i) j

/-- Every bounded original pole function is the evaluation of an actual coordinate element. -/
theorem completeCartesianPointPole_le_coordinateRange (i : Fin n) (m : ℕ) :
    divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m ≤
      completeCartesianPointCoordinateRange K n h L s p q hs i := by
  intro z hz
  have hz' := divisorPoleSubmodule_mono q
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1 (Nat.le_succ m) hz
  have he := FilteredPoleBasis.sum_repr_coe _
    (completeCartesianPointMonomialBasis K n h L s p q hs i (m + 1)) ⟨z, hz'⟩
  change _ = z at he
  rw [← he]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  rw [completeCartesianPointMonomialBasis_apply]
  exact completeCartesianPointMonomial_mem_coordinateRange K n h L s p q hs i j

/-- Normalization preserves the pole bound of each ordered monomial. -/
theorem completeCartesianPointNormalizedMonomial_mem (i : Fin n) (j : ℕ) :
    WeightedPoleMonomials.monomial
      (completeCartesianPointNormalize K n h L s p q hs i
        (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide)))
      (completeCartesianPointNormalize K n h L s p q hs i
        (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide))) j ∈
      divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1
        (WeightedPoleMonomials.order j) := by
  rw [completeCartesianPointNormalize, completeCartesianPointNormalize,
    WeightedPoleMonomials.monomial_mul_coordinates, ← map_pow]
  exact Submodule.smul_mem _ _ (completeCartesianPointMonomial_mem K n h L s p q hs i j)

/-- No coordinate expression acquires an infinite pole bound. -/
theorem completeCartesianPointCoordinateRange_le_poles (i : Fin n) :
    completeCartesianPointCoordinateRange K n h L s p q hs i ≤
      ⨆ m, divisorPoleSubmodule q
        (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m := by
  let _ := Module.compHom
    Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤)
    (completeCartesianPointScalar K n h L s p q hs i)
  rw [completeCartesianPointCoordinateRange, completeCartesianPointCoordinateLinear,
    WeierstrassAffineEquationEvaluation.evaluationLinear_range
      (A := Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤))]
  apply Submodule.span_le.mpr
  rintro _ ⟨ab, rfl⟩
  have hm := completeCartesianPointNormalizedMonomial_mem K n h L s p q hs i
    (WeightedPoleMonomials.normalIndex ab)
  rw [WeightedPoleMonomials.monomial_normalIndex] at hm
  exact (le_iSup (fun m ↦ divisorPoleSubmodule q
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m) _) hm

/-- The coordinate image equals exactly the union of all original pole spaces. -/
theorem completeCartesianPointCoordinateRange_eq_poles (i : Fin n) :
    completeCartesianPointCoordinateRange K n h L s p q hs i =
      ⨆ m, divisorPoleSubmodule q
        (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m :=
  le_antisymm (completeCartesianPointCoordinateRange_le_poles K n h L s p q hs i)
    (iSup_le (completeCartesianPointPole_le_coordinateRange K n h L s p q hs i))

end FLT.Mazur.PolygonInfinitesimalStages
