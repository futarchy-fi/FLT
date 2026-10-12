/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Ranges of full open charts under isomorphisms

Seal the point-set bookkeeping for chart comparisons before substituting
large recursively glued schemes and their isomorphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.SchemeOpenChartRange
variable {A B X Y Z : Scheme}

/-- A cartesian open chart covers exactly the preimage of the original chart. -/
theorem range_of_isPullback (a : A ⟶ B) (b : A ⟶ X) (c : B ⟶ Y) (d : X ⟶ Y)
    [IsOpenImmersion b] [IsOpenImmersion c] (H : IsPullback a b c d) :
    Set.range b = d ⁻¹' Set.range c := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H ⊤
  simpa using congrArg SetLike.coe h

/-- Precomposing a chart with an isomorphism leaves its entire image unchanged. -/
theorem range_iso_comp (e : A ≅ B) (c : B ⟶ X) : Set.range (e.hom ≫ c) = Set.range c := by
  change Set.range (c ∘ e.hom) = _
  rw [Set.range_comp]
  have h : Set.range e.hom = Set.univ := (Scheme.homeoOfIso e).surjective.range_eq
  rw [h, Set.image_univ]

/-- A chart range equality transports through an actual target inverse-image equality. -/
theorem range_iso_comp_preimage (e : A ≅ B) (c : B ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Scheme.Opens Y) (j : Scheme.Opens Z)
    (hc : Set.range c = f ⁻¹' (i : Set Y)) (hg : g ⁻¹ᵁ j = i) :
    Set.range (e.hom ≫ c) = (f ≫ g) ⁻¹' (j : Set Z) := by
  rw [range_iso_comp, hc]
  change f ⁻¹' (i : Set Y) = f ⁻¹' (g ⁻¹' (j : Set Z))
  exact congrArg (fun s : Set Y => f ⁻¹' s) (congrArg SetLike.coe hg).symm

end FLT.Mazur.SchemeOpenChartRange
