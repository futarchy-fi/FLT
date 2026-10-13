/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NeronPolygonDihedralRelations
public import FLT.Mazur.PolygonActionTranslation
public import FLT.Mazur.ProjectiveLineScaledReversalConjugation

/-!
# Reflection reverses the actual scalar and translation parameters

These identities hold on the entire reducible curve, including the original
normalization coordinates and node maps. Scaling is a translation, so these
are identities of curve automorphisms, not pointed group automorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] {n : ℕ} [NeZero n]

/-- Reflection inverts the original scalar on each complete normalization component. -/
@[reassoc] theorem componentsScaling_reflection (a : Kˣ) :
    componentsScaling K (n := n) a ≫ componentsReflection K =
      componentsReflection K ≫ componentsScaling K a⁻¹ := by
  have he : ProjectiveLine.scalingOver K a ≫
      (ProjectiveLine.endpointReversalOverIso K).hom =
        (ProjectiveLine.endpointReversalOverIso K).hom ≫
          ProjectiveLine.scalingOver K a⁻¹ := by
    apply Over.OverMorphism.ext
    exact ProjectiveLine.scaling_endpointReversal K a
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ _ = componentι K n i ≫ _
  simp only [componentι_scaling_assoc, componentι_reflection,
    componentι_reflection_assoc, componentι_scaling]
  simp only [← Category.assoc, he]

variable (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The original whole-curve reflection conjugates scaling to inverse scaling. -/
@[reassoc] theorem polygonScaling_reflection (a : Kˣ) :
    polygonScaling K hn p q h a ≫ polygonReflection K hn p q h =
      polygonReflection K hn p q h ≫ polygonScaling K hn p q h a⁻¹ := by
  apply h.hom_ext
  · simp only [components_polygonScaling_assoc, components_polygonReflection,
      components_polygonReflection_assoc, components_polygonScaling]
    rw [← Category.assoc, ← Category.assoc, componentsScaling_reflection]
  · simp

/-- Both scalar and cyclic parameters reverse for the actual full-curve translation. -/
@[reassoc] theorem translation_reflection (a : Kˣ) (b : ZMod n) :
    PolygonActionTranslation.translation K n hn p q h a b ≫
        polygonReflection K hn p q h =
      polygonReflection K hn p q h ≫
        PolygonActionTranslation.translation K n hn p q h a⁻¹ (-b) := by
  simp only [PolygonActionTranslation.translation_eq, Category.assoc]
  rw [polygonRotation_reflection, polygonScaling_reflection_assoc]

/-- Conjugating the actual translation retains the inverse unit and negative index. -/
theorem reflection_conjugate_translation (a : Kˣ) (b : ZMod n) :
    polygonReflection K hn p q h ≫
        PolygonActionTranslation.translation K n hn p q h a b ≫
          polygonReflection K hn p q h =
      PolygonActionTranslation.translation K n hn p q h a⁻¹ (-b) := by
  rw [translation_reflection, polygonReflection_involutive_assoc]

end FLT.Mazur.PolygonPinching
