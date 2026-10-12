/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassProjectiveCoefficientSquare
public import FLT.Mazur.WeierstrassIntegralProjectiveClosed
public import FLT.Mazur.ProjectiveCoefficientFunctor

/-!
# Composition of proper coefficient maps with equation transports

The actual proper coefficient maps compose under arbitrary ring homomorphisms.
Named specialized equations retain their equality transports throughout.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S A : Type} [CommRing R] [CommRing S] [CommRing A]

/-- The actual proper coefficient map for a named specialized equation. -/
def properCoefficientMap (W : WeierstrassCurve R) (V : WeierstrassCurve S)
    (f : R →+* S) (h : V = W.map f) : integralCurve V ⟶ integralCurve W := by
  letI : Algebra R S := f.toAlgebra
  exact eqToHom (congrArg integralCurve h) ≫ integralCoefficientMorphism W

/-- Equation transport retains the original closed projective embedding. -/
@[reassoc] theorem integralProjectiveMap_congr (W V : WeierstrassCurve R) (h : W = V) :
    eqToHom (congrArg integralCurve h) ≫ integralProjectiveMap V =
      integralProjectiveMap W := by
  subst V
  exact Category.id_comp _

/-- Proper coefficient change retains its ambient projective coefficient map. -/
@[reassoc] theorem properCoefficientMap_projective
    (W : WeierstrassCurve R) (V : WeierstrassCurve S)
    (f : R →+* S) (h : V = W.map f) :
    properCoefficientMap W V f h ≫ integralProjectiveMap W =
      integralProjectiveMap V ≫ ProjectiveSpace.coefficientMap f (Fin 3) := by
  let _ : Algebra R S := f.toAlgebra
  change (eqToHom _ ≫ integralCoefficientMorphism W) ≫ _ = _
  rw [Category.assoc, integralProjectiveMap_coefficient]
  exact integralProjectiveMap_congr_assoc V (W.map f) h _

/-- The actual proper map is functorial in the original coefficient homomorphisms. -/
@[reassoc] theorem properCoefficientMap_comp
    (W : WeierstrassCurve R) (V : WeierstrassCurve S) (Z : WeierstrassCurve A)
    (f : R →+* S) (g : S →+* A) (hV : V = W.map f) (hZ : Z = V.map g)
    (h : Z = W.map (g.comp f)) :
    properCoefficientMap V Z g hZ ≫ properCoefficientMap W V f hV =
      properCoefficientMap W Z (g.comp f) h := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  rw [Category.assoc, properCoefficientMap_projective,
    properCoefficientMap_projective_assoc, properCoefficientMap_projective,
    ProjectiveSpace.coefficientMap_comp]

/-- Proper coefficient change lies over the original map of coefficient spectra. -/
@[reassoc] theorem properCoefficientMap_structure
    (W : WeierstrassCurve R) (V : WeierstrassCurve S)
    (f : R →+* S) (h : V = W.map f) :
    properCoefficientMap W V f h ≫ integralCurveStructure W =
      integralCurveStructure V ≫ Spec.map (CommRingCat.ofHom f) := by
  subst V
  let _ : Algebra R S := f.toAlgebra
  change (𝟙 _ ≫ integralCoefficientMorphism W) ≫ _ = _
  rw [Category.id_comp]
  exact integralCoefficientMorphism_structure W

end FLT.Mazur.WeierstrassIntegralChart
