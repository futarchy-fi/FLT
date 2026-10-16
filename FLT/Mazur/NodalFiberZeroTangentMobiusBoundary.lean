/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberZeroTangentMobiusGeometry
public import FLT.Mazur.NodalFiberUnitScalingBoundary
public import FLT.Mazur.PolygonSmoothingOverlapGraph

/-!
# Boundary evaluation of the full fractional zero-node chart

The fractional chart divides the first parameter by the tangent unit and
sends the second to q/(q+a). On the original retained puncture q vanishes,
so the original inverse Laurent parameter is preserved exactly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (a : Rˣ)
local notation "N" => Coordinate (0 : R)
local notation "L" => ZeroTangentOpen (a : R)
local notation "M" => ZeroTangentOpen (-1 : R)

/-- Pullback of all polygon functions along the full fractional chart. -/
def zeroTangentMobiusEvaluation : PolygonSmoothing.ChartRing (0 : R) →ₐ[R] L :=
  unitNormalizedEvaluation 0 0 1 (by simp)
    ((zeroTangentMobiusForward a).comp (Algebra.algHom R N M))

@[simp] theorem zeroTangentMobiusEvaluation_left :
    zeroTangentMobiusEvaluation a (PolygonSmoothing.leftCoordinate 0) =
      algebraMap R L (↑a⁻¹ : R) * zeroTangentP (a : R) := by
  rw [zeroTangentMobiusEvaluation, unitNormalizedEvaluation_left]
  simp only [inv_one, Units.val_one, map_one, one_mul]
  exact zeroTangentMobiusForward_p a

@[simp] theorem zeroTangentMobiusEvaluation_right :
    zeroTangentMobiusEvaluation a (PolygonSmoothing.rightCoordinate 0) =
      zeroTangentFraction (a : R) := by
  rw [zeroTangentMobiusEvaluation, unitNormalizedEvaluation_right]
  exact zeroTangentMobiusForward_q a

/-- The coordinate evaluation describes the actual open immersion. -/
theorem zeroTangentMobiusChart_eq_spec :
    zeroTangentMobiusChart a =
      Spec.map (CommRingCat.ofHom (zeroTangentMobiusEvaluation a).toRingHom) := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

variable (ev : ZeroTangentOpen (a : R) →ₐ[R] LaurentPolynomial R)
  (hp : ev (zeroTangentP (a : R)) = LaurentPolynomial.T (-1) * LaurentPolynomial.C (a : R))
  (hq : ev (zeroTangentQ (a : R)) = 0)

include ev hp hq in
/-- Exact evaluation on the retained branch of the original full zero node. -/
theorem zeroTangentMobiusEvaluation_boundary :
    ev.comp (zeroTangentMobiusEvaluation a) =
      LaurentPolynomial.invert.toAlgHom.comp (PolygonSmoothing.leftLaurentMap (0 : R)) := by
  apply PolygonSmoothing.chartRing_hom_ext 0
  · simp only [AlgHom.comp_apply, zeroTangentMobiusEvaluation_left, map_mul, AlgHom.commutes]
    rw [hp, mul_left_comm, ← LaurentPolynomial.C_eq_algebraMap, ← map_mul,
      Units.inv_mul, map_one, mul_one]
    simp
  · simp only [AlgHom.comp_apply, zeroTangentMobiusEvaluation_right,
      zeroTangentFraction, map_mul, hq, zero_mul]
    simp

include ev hp hq in
/-- The actual full open immersion retains the original inverse Laurent boundary. -/
@[reassoc] theorem zeroTangentMobiusChart_boundary :
    Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ zeroTangentMobiusChart a =
      (PolygonSmoothing.edgeInversion R).hom ≫ PolygonSmoothing.leftBranchOpen R 0 := by
  rw [zeroTangentMobiusChart_eq_spec, PolygonSmoothing.leftBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
    (zeroTangentMobiusEvaluation_boundary a ev hp hq)

end FLT.Mazur.NodalFiber
