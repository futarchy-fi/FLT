/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineMorphismExt
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# A closed subcurve containing the affine cubic is the whole cubic

The infinity overlap is schematically dense over any coefficient ring.
A closed immersion through which the affine chart factors consequently has
zero kernel on both charts. This includes nonreduced coefficient bases.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- A closed immersion containing a schematically dense map has zero kernel. -/
theorem closedImmersion_isIso_of_schematicFactor {X Y T : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] (j : T ⟶ X) (k : T ⟶ Y)
    [IsSchemeTheoreticallyDominant k] (h : j ≫ f = k) : IsIso f := by
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  apply le_bot_iff.mp
  calc
    f.ker ≤ (j ≫ f).ker := Scheme.Hom.le_ker_comp j f
    _ = ⊥ := by rw [h, k.ker_eq_bot]

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A closed immersion containing the actual affine chart is the entire integral cubic. -/
theorem integralCurve_closedImmersion_isIso_of_affineFactor {X : Scheme.{u}}
    (f : X ⟶ integralCurve W) [IsClosedImmersion f]
    (j : chartScheme W 2 ⟶ X) (hj : j ≫ f = integralCurveChart W 2) : IsIso f := by
  rw [← MorphismProperty.isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_openCover
    (P := MorphismProperty.isomorphisms Scheme) (integralCurveTwoChartCover W)]
  intro b
  cases b with
  | false =>
    change IsIso (pullback.snd f (integralCurveChart W 2))
    let t := pullback.lift j (𝟙 _) (by simpa using hj)
    exact closedImmersion_isIso_of_schematicFactor _ t (𝟙 _) (by simp [t])
  | true =>
    change IsIso (pullback.snd f (integralCurveChart W 1))
    let k := overlapInclusion W 1 2
    let a := Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) ≫ j
    have ha : a ≫ f = k ≫ integralCurveChart W 1 := by
      dsimp only [a]
      rw [Category.assoc, hj]
      exact integralCurve_output_transition W 1 2
    let t := pullback.lift a k ha
    let _ := infinityOverlap_schematicallyDense W
    exact closedImmersion_isIso_of_schematicFactor _ t k (by simp [t])

end FLT.Mazur.WeierstrassIntegralChart
