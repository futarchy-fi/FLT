/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearConicParameters
public import FLT.Mazur.WeierstrassConicZeroAffineParameter

/-!
# The origins of full coefficient conic parameters

The entire affine parameter at zero constant retains the actual incidence
marking, including its tangent order, in any target scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S : Type u} [Field S] (a c : S) (ha : IsUnit a) (hc : c = 0)
  {X : Scheme.{u}} (f : Spec (.of (ConicCoordinate a c)) ⟶ X)

/-- The full first affine conic parameter starts at the first original incidence point. -/
@[reassoc] theorem coefficientConicFirstParameter_affine_origin :
    ProjectiveLine.chartZero S ≫ (conicZeroAffineIso c hc).hom ≫
        coefficientConicFirstParameter a c ha f =
      Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) ≫ f := by
  rw [conicZeroAffineIso_origin_assoc, coefficientConicFirstParameter,
    conicFirstParameterIso_origin_assoc]

/-- The full opposite affine conic parameter starts at the opposite incidence point. -/
@[reassoc] theorem coefficientConicSecondParameter_affine_origin :
    ProjectiveLine.chartZero S ≫ (conicZeroAffineIso c hc).hom ≫
        coefficientConicSecondParameter a c ha f =
      Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom) ≫ f := by
  rw [conicZeroAffineIso_origin_assoc, coefficientConicSecondParameter,
    conicSecondParameterIso_origin_assoc]

end FLT.Mazur.WeierstrassDividedDepth
