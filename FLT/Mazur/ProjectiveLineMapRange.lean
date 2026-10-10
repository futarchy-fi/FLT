/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineEndpointReversal

/-!
# Images of complete projective-line maps

The two original affine charts give the entire image. Reversing endpoints
preserves it, so cyclic orientation does not discard any part of a component.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.ProjectiveLine
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The image of a map from the projective line is exactly the union of both chart images. -/
theorem map_range (f : scheme K ⟶ X) :
    Set.range f = Set.range (left K ≫ f) ∪ Set.range (right K ≫ f) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rcases charts_cover K y with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact Or.inl ⟨z, rfl⟩
    · exact Or.inr ⟨z, rfl⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨left K y, rfl⟩
    · exact ⟨right K y, rfl⟩

/-- Reversing endpoints preserves the entire image of the original component. -/
theorem endpointReversal_map_range (f : scheme K ⟶ X) :
    Set.range (endpointReversal K ≫ f) = Set.range f :=
  (endpointReversalIso K).hom.homeomorph.surjective.range_comp f

/-- The image statement also applies to component maps over the field. -/
theorem endpointReversalOver_map_range {X : Over (Spec (.of K))}
    (f : PolygonPinching.component K ⟶ X) :
    Set.range (((endpointReversalOverIso K).hom ≫ f).left) = Set.range f.left :=
  endpointReversal_map_range f.left

end FLT.Mazur.ProjectiveLine
