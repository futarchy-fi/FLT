/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralBaseChange
public import FLT.Mazur.WeierstrassRelativeSmoothOpen
public import FLT.Mazur.WeierstrassIntegralTripleFlat
public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusBaseChange

/-!
# Coefficient extension preserves the actual Weierstrass smooth open

The geometric smooth-locus base-change theorem applies to the proved Cartesian
coefficient square of the flat finitely presented integral cubic.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The coefficient map pulls the smooth open back to the smooth open of the extended cubic. -/
theorem integralCoefficientMorphism_preimage_smooth :
    integralCoefficientMorphism (S := S) W ⁻¹ᵁ integralSmoothOpen W =
      integralSmoothOpen (W.map (algebraMap R S)) := by
  calc
    _ = (integralCurveCoefficientBaseChangeIso (S := S) W).hom ⁻¹ᵁ
        (pullback.fst (integralCurveStructure W)
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⁻¹ᵁ integralSmoothOpen W) := by
      rw [← Scheme.Hom.comp_preimage, integralCurveCoefficientBaseChangeIso_fst]
    _ = (integralCurveCoefficientBaseChangeIso (S := S) W).hom ⁻¹ᵁ
        (pullback.snd (integralCurveStructure W)
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).smoothLocus := by
      rw [integralSmoothOpen, Scheme.Hom.preimage_smoothLocus_baseChange]
    _ = _ := by
      rw [Scheme.Hom.preimage_smoothLocus_eq]
      congr 1
      exact integralCurveCoefficientBaseChangeIso_snd W

end FLT.Mazur.WeierstrassIntegralChart
