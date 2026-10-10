/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowProductOpenGluing
public import FLT.Mazur.SurjectiveDominantEpi
public import FLT.Mazur.WeierstrassAffineChartDense

/-!
# The affine chart detects morphisms from the whole cubic

Regularity of Z makes the infinity overlap schematically dense. Equality on
the affine chart therefore extends to the whole original cubic for a separated
target over the base, even when the coefficient ring has nilpotents.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The infinity overlap is schematically dense over every coefficient ring. -/
theorem infinityOverlap_schematicallyDense :
    IsSchemeTheoreticallyDominant (overlapInclusion W 1 2) :=
  SurjectiveDominantEpi.spec_schematic (overlapRestriction W 1 2).toRingHom
    (infinityOverlapRestriction_injective W)

/-- Equality on the actual affine chart determines the entire morphism to a separated target. -/
theorem integralCurve_hom_ext_affine {X S : Scheme.{u}} (s : X ⟶ S) [IsSeparated s]
    (f g : integralCurve W ⟶ X) (hb : f ≫ s = g ≫ s)
    (ha : integralCurveChart W 2 ≫ f = integralCurveChart W 2 ≫ g) : f = g := by
  apply (integralCurveTwoChartCover W).hom_ext
  intro b
  cases b with
  | false => exact ha
  | true =>
    change integralCurveChart W 1 ≫ f = integralCurveChart W 1 ≫ g
    let _ := infinityOverlap_schematicallyDense W
    apply Chow.schematicallyDense_ext s
      (by simpa only [Category.assoc] using congrArg (integralCurveChart W 1 ≫ ·) hb)
      (overlapInclusion W 1 2)
    simpa only [← Category.assoc, ← integralCurve_output_transition] using
      congrArg (Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) ≫ ·) ha

end FLT.Mazur.WeierstrassIntegralChart
