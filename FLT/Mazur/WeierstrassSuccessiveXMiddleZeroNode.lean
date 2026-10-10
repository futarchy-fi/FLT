/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeOrigin
public import FLT.Mazur.NodalFiberNodeComparison
public import FLT.Mazur.PolygonNodePresentation

/-!
# The full middle attachment node at zero conic constant

The localization denominator is one, so the entire original node open is the
standard split node. The comparison preserves its parameter, horizontal
coordinate, and original origin evaluation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R]
local notation "B" => SuccessiveIncidence.Coordinate (0 : R)
local notation "N" => MiddleNodeOpen (0 : R)
local notation "A" => PolygonNodeEqualizer.A (R := R)

/-- At zero conic constant localization preserves the complete original incidence algebra. -/
def middleZeroBaseEquiv : B ≃ₐ[R] N :=
  AlgEquiv.restrictScalars R (IsLocalization.atUnit B N (middleNodeDenominator (0 : R))
    (by simp only [middleNodeDenominator, map_zero, zero_mul, sub_zero, isUnit_one]))

/-- The forward equivalence is exactly the original localization map. -/
theorem middleZeroBaseEquiv_apply (x : B) :
    middleZeroBaseEquiv x = algebraMap B N x :=
  (IsLocalization.atUnit B N (middleNodeDenominator (0 : R))
    (by simp only [middleNodeDenominator, map_zero, zero_mul, sub_zero, isUnit_one])).commutes x

/-- The inverse localization sends each original function to itself. -/
theorem middleZeroBaseEquiv_symm_base (x : B) :
    middleZeroBaseEquiv.symm (algebraMap B N x) = x := by
  rw [← middleZeroBaseEquiv_apply, AlgEquiv.symm_apply_apply]

/-- The full attachment node is the polynomial-pair split node, with no branch removed. -/
def middleZeroNodeEquiv : N ≃ₐ[R] A :=
  middleZeroBaseEquiv.symm.trans NodalFiber.polygonNodeEquiv

/-- The original retained parameter is the first node coordinate. -/
@[simp] theorem middleZeroNodeEquiv_z :
    middleZeroNodeEquiv (middleNodeZ (0 : R)) = PolygonNodeLocalization.x := by
  change NodalFiber.polygonNodeEquiv
    (middleZeroBaseEquiv.symm (algebraMap B N (SuccessiveIncidence.t 0))) = _
  rw [middleZeroBaseEquiv_symm_base]
  exact NodalFiber.polygonNodeEquiv_p

/-- The original horizontal function is the second node coordinate. -/
@[simp] theorem middleZeroNodeEquiv_u :
    middleZeroNodeEquiv (middleNodeU (0 : R)) = PolygonNodeLocalization.y := by
  change NodalFiber.polygonNodeEquiv
    (middleZeroBaseEquiv.symm (algebraMap B N (SuccessiveIncidence.u 0))) = _
  rw [middleZeroBaseEquiv_symm_base]
  exact NodalFiber.polygonNodeEquiv_q

/-- The comparison also retains the original scheme-theoretic origin. -/
theorem middleZeroNodeEquiv_origin :
    PolygonNodePresentation.aEval.comp middleZeroNodeEquiv.toAlgHom = middleNodeOrigin (0 : R) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (middleNodeDenominator (0 : R)))
  apply SuccessiveIncidence.hom_ext 0
  · change PolygonNodePresentation.aEval (middleZeroNodeEquiv (middleNodeZ (0 : R))) =
      middleNodeOrigin 0 (middleNodeZ 0)
    rw [middleZeroNodeEquiv_z]
    rw [middleNodeOrigin_z]
    simp [PolygonNodePresentation.aEval]
  · change PolygonNodePresentation.aEval (middleZeroNodeEquiv (middleNodeU (0 : R))) =
      middleNodeOrigin 0 (middleNodeU 0)
    rw [middleZeroNodeEquiv_u]
    rw [middleNodeOrigin_u]
    simp [PolygonNodePresentation.aEval]

/-- The same full comparison applies to any conic constant proved zero. -/
def middleNodeEquivOfZero (c : R) (hc : c = 0) : MiddleNodeOpen c ≃ₐ[R] A := by
  subst c
  exact middleZeroNodeEquiv

/-- Constant transport preserves the first original node coordinate. -/
@[simp] theorem middleNodeEquivOfZero_z (c : R) (hc : c = 0) :
    middleNodeEquivOfZero c hc (middleNodeZ c) = PolygonNodeLocalization.x := by
  subst c
  exact middleZeroNodeEquiv_z

/-- Constant transport preserves the second original node coordinate. -/
@[simp] theorem middleNodeEquivOfZero_u (c : R) (hc : c = 0) :
    middleNodeEquivOfZero c hc (middleNodeU c) = PolygonNodeLocalization.y := by
  subst c
  exact middleZeroNodeEquiv_u

/-- Constant transport preserves the entire original origin evaluation. -/
theorem middleNodeEquivOfZero_origin (c : R) (hc : c = 0) :
    PolygonNodePresentation.aEval.comp (middleNodeEquivOfZero c hc).toAlgHom =
      middleNodeOrigin c := by
  subst c
  exact middleZeroNodeEquiv_origin

end FLT.Mazur.WeierstrassSuccessiveX
