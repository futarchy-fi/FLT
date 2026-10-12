/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicCoefficientTransport
public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry
public import FLT.Mazur.WeierstrassCoefficientShearConicParameters

/-!
# Transport of the complete incidence equation and its conic parameters

Equal tangent coefficients identify the entire incidence fiber, preserving
both full conic parameters rather than only their Laurent restrictions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
variable {K : Type*} [CommRing K] {a b : K} (c : K) (h : a = b)

/-- Transport the entire incidence equation along an equality of tangents. -/
def fiberCoefficientTransport : FiberCoordinate a c ≃ₐ[K] FiberCoordinate b c := by
  subst b
  exact AlgEquiv.refl

/-- Tangent transport preserves the incidence coordinate. -/
theorem fiberCoefficientTransport_t :
    fiberCoefficientTransport c h (fiberT a c) = fiberT b c := by
  subst b
  rfl

/-- Tangent transport preserves the original slope coordinate. -/
theorem fiberCoefficientTransport_v :
    fiberCoefficientTransport c h (fiberV a c) = fiberV b c := by
  subst b
  rfl

/-- The full conic immersion commutes with transport of the ambient incidence equation. -/
@[reassoc] theorem fiberConicImmersion_coefficientTransport :
    fiberConicImmersion b c ≫
        Spec.map (CommRingCat.ofHom (fiberCoefficientTransport c h).toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom (conicCoefficientTransport c h).toAlgHom.toRingHom) ≫
        fiberConicImmersion a c := by
  subst b
  simp [fiberCoefficientTransport, conicCoefficientTransport]

variable (ha : IsUnit a) (hb : IsUnit b)

/-- The entire first conic parameter is unchanged by equal tangent coefficients. -/
@[reassoc] theorem conicFirstParameter_coefficientTransport :
    (conicFirstParameterIso b c hb).inv ≫ conicFirstOpenImmersion b c ≫
        Spec.map (CommRingCat.ofHom (conicCoefficientTransport c h).toAlgHom.toRingHom) =
      (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c := by
  subst b
  simp [conicCoefficientTransport]

/-- The entire opposite conic parameter retains its original sign under transport. -/
@[reassoc] theorem conicSecondParameter_coefficientTransport :
    (conicSecondParameterIso b c hb).inv ≫ conicSecondOpenImmersion b c ≫
        Spec.map (CommRingCat.ofHom (conicCoefficientTransport c h).toAlgHom.toRingHom) =
      (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c := by
  subst b
  simp [conicCoefficientTransport]

end FLT.Mazur.WeierstrassModificationX
