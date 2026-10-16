/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioGeometry
public import FLT.Mazur.NodalFiberTangentMobiusBoundary

/-!
# Full polygon evaluation of the corrected arithmetic factor-ratio chart

The polygon evaluation retains the entire corrected map. Both coordinates
therefore retain the full original arithmetic corrections on every boundary.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "L" => PolynomialNodeOpen W s
local notation "M" => NodalFiber.TangentOpen τ (-1 : R)
local notation "N" => NodalFiber.Coordinate τ
local notation "F" => polynomialFactorRatioMap W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "C" => polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- Every polygon function pulls back by the full corrected factor-ratio map. -/
def polynomialFactorRatioEvaluation : PolygonSmoothing.ChartRing τ →ₐ[R] L :=
  NodalFiber.unitNormalizedEvaluation τ τ 1 (by simp)
    ((F).comp (Algebra.algHom R N M))

local notation "E" => polynomialFactorRatioEvaluation W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- The polygon first coordinate is exactly the corrected normalized node coordinate. -/
theorem polynomialFactorRatioEvaluation_left :
    E (PolygonSmoothing.leftCoordinate τ) = F (NodalFiber.tangentP τ (-1 : R)) := by
  rw [polynomialFactorRatioEvaluation, NodalFiber.unitNormalizedEvaluation_left]
  simp only [inv_one, Units.val_one, map_one, one_mul]
  rfl

/-- The polygon second coordinate is the full original factor ratio. -/
theorem polynomialFactorRatioEvaluation_right :
    E (PolygonSmoothing.rightCoordinate τ) = F (NodalFiber.tangentQ τ (-1 : R)) := by
  rw [polynomialFactorRatioEvaluation, NodalFiber.unitNormalizedEvaluation_right]
  rfl

/-- The full polygon evaluation defines the actual corrected open immersion. -/
theorem polynomialFactorRatioChart_eq_spec :
    C = Spec.map (CommRingCat.ofHom (E).toRingHom) := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
