/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNegationIntersection
public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# Global regular negation of the integral cubic

The affine involution and the normalized infinity formula agree on their
actual intersection. They glue to a regular morphism over the coefficient
scheme that fixes zero, for arbitrary coefficients and without good reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Both negation formulas, viewed as morphisms to the common glued curve. -/
def negationCurveLocal (b : Bool) : negationCoverScheme W b ⟶ integralCurve W :=
  match b with
  | false => Spec.map (CommRingCat.ofHom (affineNegation W).toRingHom) ≫ integralCurveChart W 2
  | true => Spec.map (CommRingCat.ofHom (infinityNegationChart W).toRingHom) ≫
      integralCurveChart W 1

/-- The local formulas agree on every common scheme with the same global input. -/
theorem negationCurveLocal_commonScheme (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ negationCoverScheme W b) (g : X ⟶ negationCoverScheme W c)
    (h : f ≫ negationCoverInclusion W b = g ≫ negationCoverInclusion W c) :
    f ≫ negationCurveLocal W b = g ≫ negationCurveLocal W c := by
  cases b <;> cases c
  · have he : f = g := (cancel_mono (negationCoverInclusion W false)).mp h
    rw [he]
  · exact (negation_commonScheme W g f h.symm).symm
  · exact negation_commonScheme W f g h
  · have he : f = g := (cancel_mono (negationCoverInclusion W true)).mp h
    rw [he]

/-- The regular global negation morphism of the actual integral cubic. -/
def integralCurveNegation : integralCurve W ⟶ integralCurve W :=
  (negationCover W).glueMorphisms (negationCurveLocal W)
    (fun b c => negationCurveLocal_commonScheme W b c _ _ pullback.condition)

/-- Gluing retains both original local negation formulas. -/
theorem negationCoverInclusion_negation (b : Bool) :
    negationCoverInclusion W b ≫ integralCurveNegation W = negationCurveLocal W b :=
  (negationCover W).ι_glueMorphisms _ _ b

/-- On the affine chart, global negation is the explicit affine algebra involution. -/
theorem integralCurveChart_negation_affine :
    integralCurveChart W 2 ≫ integralCurveNegation W =
      Spec.map (CommRingCat.ofHom (affineNegation W).toRingHom) ≫ integralCurveChart W 2 :=
  negationCoverInclusion_negation W false

/-- On its entire infinity neighborhood, global negation is the normalized Y formula. -/
theorem integralCurveChart_negation_infinity :
    infinityNegationInclusion W ≫ integralCurveChart W 1 ≫ integralCurveNegation W =
      Spec.map (CommRingCat.ofHom (infinityNegationChart W).toRingHom) ≫
        integralCurveChart W 1 := by
  exact (Category.assoc _ _ _).symm.trans (negationCoverInclusion_negation W true)

/-- Negation preserves the actual structure morphism to the coefficient spectrum. -/
theorem integralCurveNegation_structure :
    integralCurveNegation W ≫ integralCurveStructure W = integralCurveStructure W := by
  apply (negationCover W).hom_ext
  intro b
  change negationCoverInclusion W b ≫ (integralCurveNegation W ≫
    integralCurveStructure W) = negationCoverInclusion W b ≫ integralCurveStructure W
  rw [← Category.assoc, negationCoverInclusion_negation]
  cases b
  · change (Spec.map _ ≫ integralCurveChart W 2) ≫ integralCurveStructure W =
      integralCurveChart W 2 ≫ integralCurveStructure W
    rw [Category.assoc, integralCurveChart_structure, chartStructure, specAlgHom_structure]
  · change (Spec.map _ ≫ integralCurveChart W 1) ≫ integralCurveStructure W =
      (infinityNegationInclusion W ≫ integralCurveChart W 1) ≫ integralCurveStructure W
    rw [Category.assoc, Category.assoc, integralCurveChart_structure, chartStructure,
      specAlgHom_structure]
    exact (specAlgHom_structure (infinityNegationRestriction W)).symm

/-- The infinity neighborhood really contains the original scheme-valued zero section. -/
theorem infinityNegationZero_spec :
    Spec.map (CommRingCat.ofHom (infinityNegationZero W).toRingHom) ≫
      infinityNegationInclusion W =
        Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := R) W).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (infinityNegationZero_restriction W)

/-- Global negation fixes the actual zero section over the whole base. -/
theorem integralCurveZero_negation :
    integralCurveZero W ≫ integralCurveNegation W = integralCurveZero W := by
  rw [integralCurveZero, ← infinityNegationZero_spec, Category.assoc, Category.assoc,
    integralCurveChart_negation_infinity, ← Category.assoc, ← Spec.map_comp]
  have h := congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (infinityNegationZero_chart W)
  change Spec.map (CommRingCat.ofHom
    ((infinityNegationZero W).comp (infinityNegationChart W)).toRingHom) ≫
      integralCurveChart W 1 = _
  rw [h, infinityNegationZero_spec]

end FLT.Mazur.WeierstrassIntegralChart
