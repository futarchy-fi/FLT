/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeGeneralizedComparison

/-!
# Coefficient base change of full smooth generalized Weierstrass curves

The coefficient comparison extends to the whole curve and its action. It
retains the original group map and works for arbitrary coefficient homomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A : Type} [CommRing R] [CommRing A]
  (W : WeierstrassCurve R) (hW : IsUnit W.Δ) (f : R →+* A)

include hW in
/-- The specialized long equation stays smooth over every coefficient algebra. -/
theorem coefficientEquation_discriminant : IsUnit (W.map f).Δ := by
  rw [map_Δ]
  exact hW.map f

/-- The coefficient map compares the actual groups of the two full models. -/
def coefficientModelGroupIso :
    (integralGeneralizedEllipticCurve (W.map f) (coefficientEquation_discriminant W hW f)).group ≅
      ((integralGeneralizedEllipticCurve W hW).baseChange
        (Spec.map (CommRingCat.ofHom f))).group := by
  letI : Algebra R A := f.toAlgebra
  exact (CommGrp.forget (Over (Spec (.of A)))).mapIso
    (integralCurveCoefficientGroupIso W hW (coefficientEquation_discriminant W hW f))

instance coefficientModelGroupIso_isMonHom :
    IsMonHom (coefficientModelGroupIso W hW f).hom := by
  let _ : Algebra R A := f.toAlgebra
  change IsMonHom (integralCurveCoefficientGroupIso W hW
    (coefficientEquation_discriminant W hW f)).hom.hom.hom.hom
  infer_instance

/-- Specializing coefficients gives the original full generalized curve pullback. -/
def coefficientModelIso :
    integralGeneralizedEllipticCurve (W.map f) (coefficientEquation_discriminant W hW f) ≅
      (integralGeneralizedEllipticCurve W hW).baseChange
        (Spec.map (CommRingCat.ofHom f)) := by
  letI : Algebra R A := f.toAlgebra
  let _ : Smooth (integralGeneralizedEllipticCurve (W.map f)
      (coefficientEquation_discriminant W hW f)).curve.hom :=
    integralCurveStructure_smooth (W.map f) (coefficientEquation_discriminant W hW f)
  let _ := WeierstrassChangeParameter.modelBaseChange_smooth W hW (A := A)
  exact isoOfSmoothGroup _ _ (coefficientModelGroupIso W hW f)

/-- Extending to the whole curve preserves exactly the original coefficient group map. -/
theorem coefficientModelIso_group :
    (coefficientModelIso W hW f).hom.group = (coefficientModelGroupIso W hW f).hom := rfl

end FLT.Mazur.WeierstrassIntegralChart
