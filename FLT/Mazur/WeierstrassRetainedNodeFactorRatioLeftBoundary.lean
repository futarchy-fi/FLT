/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioMap

/-!
# The outgoing retained boundary keeps its full thickness and correction

The outgoing left coordinate contains a₁⁻²(s/π), the Laurent generator,
and the inverse full correction unit. If s/π is a unit, this gives an exact
factorization through the corrected target left branch.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
local notation "a" => zeroInitialTangentUnit W ha
local notation "V" => retainedFactorCorrectionUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6
local notation "E" => leftLaurentMap π
local notation "L" => R[T;T⁻¹]
variable (d : R)
local notation "q" => (↑a⁻¹ : R) ^ 2 * d

/-- The outgoing boundary parameter retains the actual thickness and full correction unit. -/
def retainedLeftFactorParameter : L :=
  algebraMap R L q * LaurentPolynomial.T 1 *
    E (↑(V)⁻¹ : ChartRing π)
local notation "p" => retainedLeftFactorParameter W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d
attribute [local irreducible] retainedFactorCorrectionUnit
variable (hd : s = π * d)
local notation "τ" => initialTangentSmoothing W ha s
local notation "F" => retainedFactorRatioEvaluation W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd

/-- The entire outgoing left coordinate has the exact parameter, including s/π. -/
theorem retainedFactorRatioEvaluation_left_boundary : E (F (leftCoordinate τ)) = p := by
  rw [retainedFactorRatioEvaluation_left]
  simp only [retainedLeftFactorParameter, map_mul, AlgHom.commutes, leftLaurentMap_left]

/-- The entire outgoing right coordinate retains the original smoothing π and the full unit. -/
theorem retainedFactorRatioEvaluation_left_boundary_right :
    E (F (rightCoordinate τ)) =
      LaurentPolynomial.C π * LaurentPolynomial.T (-1) * E (V : ChartRing π) := by
  rw [retainedFactorRatioEvaluation_right, map_mul, leftLaurentMap_right]

variable (hu : IsUnit d)

include hu in
/-- Unit thickness gives an actual invertible outgoing parameter without dropping corrections. -/
theorem retainedLeftFactorParameter_isUnit : IsUnit p :=
  (((((a)⁻¹.isUnit.pow 2).mul hu).map (algebraMap R L)).mul
    (LaurentPolynomial.isUnit_T 1)).mul (((V)⁻¹.isUnit).map E)

/-- Unit thickness gives the full outgoing puncture through the corrected left edge. -/
@[reassoc] theorem retainedFactorRatioChart_left_boundary :
    leftBranchOpen R π ≫
      retainedFactorRatioChart W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd =
        Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R)
          (retainedLeftFactorParameter_isUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hu).unit
            ).toRingHom) ≫ leftBranchOpen R τ := by
  rw [leftBranchOpen_eq_spec, retainedFactorRatioChart, ← Spec.map_comp]
  apply boundary_leftBranchOpen τ ((E).comp F)
  rw [AlgHom.comp_apply, retainedFactorRatioEvaluation_left_boundary, IsUnit.unit_spec]

end FLT.Mazur.WeierstrassModificationX
