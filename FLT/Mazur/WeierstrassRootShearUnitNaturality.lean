/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRootShearUnitAddition

/-!
# Root-sheared unit inputs commute with arbitrary algebra maps

The actual smooth input retains every Laurent function when the test algebra
changes. No field or reducedness restriction is needed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (W : WeierstrassCurve R) (r : R) (a : Rˣ)
  (ha : (a : R) = W.a₁ + 2 * r) (hr : r ^ 2 + W.a₁ * r - W.a₂ = 0)
  (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)

/-- Every algebra map transports the full original smooth input by its mapped tangent unit. -/
theorem rootShearSmoothUnitInput_natural (f : A →ₐ[R] B) (p : Aˣ) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        (rootShearSmoothUnitInput W r a ha hr h3 h4 h6 p).left =
      (rootShearSmoothUnitInput W r a ha hr h3 h4 h6
        (Units.map f.toMonoidHom p)).left := by
  rw [rootShearSmoothUnitInput_parameter, rootShearSmoothUnitInput_parameter,
    ← Spec.map_comp_assoc]
  apply congrArg (· ≫ (rootShearTorusSmoothIso W r a ha hr h3 h4 h6).hom)
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (LaurentUnitPoints.evalUnit_natural f p)

end FLT.Mazur.WeierstrassIntegralChart
