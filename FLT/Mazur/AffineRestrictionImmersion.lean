/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Affine restrictions and stalk surjectivity

Surjective pullback of sections between affine opens gives a closed immersion.
Stalk surjectivity on an open source chart passes to the original morphism at
all points of that chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AffineRestrictionImmersion
variable {X Y Z : Scheme.{u}}

/-- The scheme restriction of a surjective affine section map is a closed immersion. -/
lemma closed_restriction (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    [IsAffine U.toScheme] [IsAffine V.toScheme] (e : U ≤ f ⁻¹ᵁ V)
    (hs : Function.Surjective (f.appLE V U e)) : IsClosedImmersion (f.resLE V U e) := by
  apply IsClosedImmersion.of_surjective_of_isAffine
  change Function.Surjective ((f.resLE V U e).app ⊤)
  rw [Scheme.Hom.resLE_app_top]
  exact ((ConcreteCategory.bijective_of_isIso U.topIso.inv).2.comp hs).comp
    (ConcreteCategory.bijective_of_isIso V.topIso.hom).2

/-- The same restricted map, viewed in the whole target, is an immersion. -/
lemma immersion (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    [IsAffine U.toScheme] [IsAffine V.toScheme] (e : U ≤ f ⁻¹ᵁ V)
    (hs : Function.Surjective (f.appLE V U e)) : IsImmersion (U.ι ≫ f) := by
  have := closed_restriction f U V e hs
  rw [← Scheme.Hom.resLE_comp_ι f e]
  infer_instance

/-- An open source chart with surjective stalk maps proves surjectivity at its image. -/
lemma stalkMap_surjective (j : Z ⟶ X) [IsOpenImmersion j] (f : X ⟶ Y)
    [SurjectiveOnStalks (j ≫ f)] (z : Z) : Function.Surjective (f.stalkMap (j z)) := by
  have hs := (j ≫ f).stalkMap_surjective z
  rw [Scheme.Hom.stalkMap_comp] at hs
  intro b
  obtain ⟨a, ha⟩ := hs (j.stalkMap z b)
  exact ⟨a, (ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1 ha⟩

end FLT.Mazur.AffineRestrictionImmersion
