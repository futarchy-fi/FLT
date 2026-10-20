/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassProperCoefficientComposition
public import FLT.Mazur.OneGonSmoothEquationProjection
public import FLT.Mazur.WeierstrassSmoothCoefficientCartesian

/-!
# Smooth coefficient maps with named equations compose

The full smooth comparison is functorial for arbitrary ring homomorphisms.
Equality transports are retained, so this applies to the actual adic quotients.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S A : Type} [CommRing R] [CommRing S] [CommRing A]

/-- The actual smooth coefficient map to a named specialized equation. -/
def smoothCoefficientMapTo (W : WeierstrassCurve R) (V : WeierstrassCurve S)
    (f : R →+* S) (h : V = W.map f) :
    (integralSmoothOpen V).toScheme ⟶ (integralSmoothOpen W).toScheme := by
  letI : Algebra R S := f.toAlgebra
  exact eqToHom (congrArg (fun U => (integralSmoothOpen U).toScheme) h) ≫
    originalSmoothCoefficientMap S W

/-- Smooth coefficient change retains the original whole-curve coefficient map. -/
@[reassoc] theorem smoothCoefficientMapTo_inclusion
    (W : WeierstrassCurve R) (V : WeierstrassCurve S)
    (f : R →+* S) (h : V = W.map f) :
    smoothCoefficientMapTo W V f h ≫ (integralSmoothOpen W).ι =
      (integralSmoothOpen V).ι ≫ properCoefficientMap W V f h := by
  subst V
  let _ : Algebra R S := f.toAlgebra
  change (𝟙 _ ≫ originalSmoothCoefficientMap S W) ≫ _ =
    _ ≫ (𝟙 _ ≫ integralCoefficientMorphism W)
  simp only [Category.id_comp]
  exact originalSmoothCoefficientMap_inclusion S W

/-- The smooth projection lies over the actual coefficient map of bases. -/
@[reassoc] theorem smoothCoefficientMapTo_structure
    (W : WeierstrassCurve R) (V : WeierstrassCurve S)
    (f : R →+* S) (h : V = W.map f) :
    smoothCoefficientMapTo W V f h ≫ integralSmoothStructure W =
      integralSmoothStructure V ≫ Spec.map (CommRingCat.ofHom f) := by
  change _ ≫ (integralSmoothOpen W).ι ≫ integralCurveStructure W = _
  rw [smoothCoefficientMapTo_inclusion_assoc, properCoefficientMap_structure]
  rfl

/-- Direct and iterated smooth coefficient maps agree, with all equation transports. -/
@[reassoc] theorem smoothCoefficientMapTo_comp
    (W : WeierstrassCurve R) (V : WeierstrassCurve S) (Z : WeierstrassCurve A)
    (f : R →+* S) (g : S →+* A) (hV : V = W.map f) (hZ : Z = V.map g)
    (h : Z = W.map (g.comp f)) :
    smoothCoefficientMapTo V Z g hZ ≫ smoothCoefficientMapTo W V f hV =
      smoothCoefficientMapTo W Z (g.comp f) h := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [Category.assoc, smoothCoefficientMapTo_inclusion,
    smoothCoefficientMapTo_inclusion_assoc, smoothCoefficientMapTo_inclusion,
    properCoefficientMap_comp]

/-- Equal coefficient homomorphisms give the same smooth morphism. -/
theorem smoothCoefficientMapTo_congr
    (W : WeierstrassCurve R) (V : WeierstrassCurve S)
    {f g : R →+* S} (e : f = g) (hf : V = W.map f) (hg : V = W.map g) :
    smoothCoefficientMapTo W V f hf = smoothCoefficientMapTo W V g hg := by
  subst g
  rfl

end FLT.Mazur.WeierstrassIntegralChart
