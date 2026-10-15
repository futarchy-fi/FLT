/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveNilpotentBranch
public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# Original incidence functions on adjacent Laurent boundaries

The right boundary uses its original coordinate. The older left boundary
uses the inverse edge coordinate, as required by the polygon atlas.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonSmoothing
variable {R : Type*} [CommRing R] (π : R)

/-- The original right boundary evaluation on the incidence algebra. -/
def rightIncidenceLaurent : SuccessiveIncidence.Coordinate π →ₐ[R] R[T;T⁻¹] :=
  ((leftLaurentMap π).comp (branchSwapMap π)).comp (SuccessiveIncidence.toPolygon π)

/-- The original left boundary, expressed in the next chart's right coordinate. -/
def inverseLeftIncidenceLaurent : SuccessiveIncidence.Coordinate π →ₐ[R] R[T;T⁻¹] :=
  LaurentPolynomial.invert.toAlgHom.comp
    ((leftLaurentMap π).comp (SuccessiveIncidence.toPolygon π))

/-- On the next right boundary, the first incidence coordinate is π/z. -/
@[simp] theorem rightIncidenceLaurent_t :
    rightIncidenceLaurent π (SuccessiveIncidence.t π) =
      LaurentPolynomial.C π * LaurentPolynomial.T (-1) := by
  simp [rightIncidenceLaurent]

/-- On the next right boundary, the second incidence coordinate is z. -/
@[simp] theorem rightIncidenceLaurent_u :
    rightIncidenceLaurent π (SuccessiveIncidence.u π) = LaurentPolynomial.T 1 := by
  simp [rightIncidenceLaurent]

/-- The older left boundary has inverse first coordinate. -/
@[simp] theorem inverseLeftIncidenceLaurent_t :
    inverseLeftIncidenceLaurent π (SuccessiveIncidence.t π) = LaurentPolynomial.T (-1) := by
  simp [inverseLeftIncidenceLaurent]

/-- The older second coordinate is π times the next right coordinate. -/
@[simp] theorem inverseLeftIncidenceLaurent_u :
    inverseLeftIncidenceLaurent π (SuccessiveIncidence.u π) =
      LaurentPolynomial.C π * LaurentPolynomial.T 1 := by
  simp [inverseLeftIncidenceLaurent]

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The actual adjacent coefficient division preserves the Laurent linear slope coefficient. -/
theorem adjacentLaurent_linear :
    inverseLeftIncidenceLaurent π (nodeSlopeLinear W π (π * b3)) =
      rightIncidenceLaurent π (nodeSlopeLinear W π b3) := by
  simp only [nodeSlopeLinear, map_add, map_mul, AlgHom.commutes,
    inverseLeftIncidenceLaurent_t, rightIncidenceLaurent_t]
  simp only [← LaurentPolynomial.C_eq_algebraMap]
  ring

/-- The actual adjacent coefficient division preserves the entire Laurent constant term. -/
theorem adjacentLaurent_constant :
    inverseLeftIncidenceLaurent π (nodeSlopeConstant W s π (π * b4) (π ^ 2 * b6)) =
      rightIncidenceLaurent π (nodeSlopeConstant W (s * π) π b4 b6) := by
  simp only [nodeSlopeConstant, map_add, map_mul, map_pow, AlgHom.commutes,
    inverseLeftIncidenceLaurent_t, inverseLeftIncidenceLaurent_u,
    rightIncidenceLaurent_t, rightIncidenceLaurent_u]
  simp only [← LaurentPolynomial.C_eq_algebraMap]
  ring

end FLT.Mazur.WeierstrassSuccessiveX
