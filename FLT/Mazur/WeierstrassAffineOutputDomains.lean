/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinarySchemeLift
public import FLT.Mazur.WeierstrassOrdinaryGlobalDomains

/-!
# Ordinary replacement on every affine-output addition domain

All four affine-input addition charts have a canonical ordinary replacement
when their output lies in the affine chart. The replacement preserves the
morphism into the true curve product, hence also the actual global addition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (W : WeierstrassCurve R)

/-- The global input domain of any of the four affine-input addition laws. -/
def additionGlobalDomain (i : AdditionChartIndex) :
    Spec (additionChartRing W i) ⟶ integralCurveProduct W :=
  additionChartInclusion W i ≫ integralCurveProductChart W false false

instance additionGlobalDomain_isOpenImmersion (i : AdditionChartIndex) :
    IsOpenImmersion (additionGlobalDomain W i) := by
  unfold additionGlobalDomain
  infer_instance

/-- Choose the secant or tangent ordinary family underlying an affine addition domain. -/
def additionOrdinaryChoice : AdditionChartIndex → Bool
  | .secant | .verticalSecant => false
  | .tangent | .verticalTangent => true

/-- The chart morphism into an ordinary domain on the affine-output locus. -/
def additionAffineOutputScheme (i : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W i))
    (hz : IsUnit (specSectionHom f
      (additionChartAlgOutput W i (coord W (additionChartOutput i) 2)))) :
    X ⟶ Spec (additionChartRing W (ordinaryIndex (additionOrdinaryChoice i))) := by
  cases i with
  | secant => exact f
  | tangent => exact f
  | verticalSecant => exact reciprocalAffineOrdinaryScheme W false f hz
  | verticalTangent => exact reciprocalAffineOrdinaryScheme W true f hz

/-- Ordinary replacement preserves the original map into the true product. -/
theorem additionAffineOutputScheme_inputs (i : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W i))
    (hz : IsUnit (specSectionHom f
      (additionChartAlgOutput W i (coord W (additionChartOutput i) 2)))) :
    additionAffineOutputScheme W i f hz ≫
        ordinaryGlobalDomain W (additionOrdinaryChoice i) =
      f ≫ additionGlobalDomain W i := by
  cases i with
  | secant => rfl
  | tangent => rfl
  | verticalSecant =>
    change reciprocalAffineOrdinaryScheme W false f hz ≫
      additionChartInclusion W (ordinaryIndex false) ≫ _ = _
    rw [← Category.assoc, reciprocalAffineOrdinaryScheme_inputs, Category.assoc]
    rfl
  | verticalTangent =>
    change reciprocalAffineOrdinaryScheme W true f hz ≫
      additionChartInclusion W (ordinaryIndex true) ≫ _ = _
    rw [← Category.assoc, reciprocalAffineOrdinaryScheme_inputs, Category.assoc]
    rfl

end FLT.Mazur.WeierstrassIntegralChart
