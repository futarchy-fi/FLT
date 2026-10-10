/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineMapRange
public import FLT.Mazur.ProjectiveLineEndpointCover

/-!
# Complete images from one affine chart and the missing endpoint

These formulas retain every scheme point, without an algebraic closure assumption.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.ProjectiveLine
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A full projective image is its left affine image together with infinity. -/
theorem map_range_left_infinity (f : scheme K ⟶ X) :
    Set.range f = Set.range (left K ≫ f) ∪ Set.range (infinity K ≫ f) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rcases torus_or_endpoints K y with ⟨z, rfl⟩ | ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact Or.inl ⟨overlapLeft K z, rfl⟩
    · exact Or.inl ⟨chartZero K z, rfl⟩
    · exact Or.inr ⟨z, rfl⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨left K y, rfl⟩
    · exact ⟨infinity K y, rfl⟩

/-- A full projective image is its right affine image together with zero. -/
theorem map_range_right_zero (f : scheme K ⟶ X) :
    Set.range f = Set.range (right K ≫ f) ∪ Set.range (zero K ≫ f) := by
  have h := map_range_left_infinity (endpointReversal K ≫ f)
  rw [endpointReversal_map_range, left_endpointReversal_assoc,
    infinity_endpointReversal_assoc] at h
  exact h

end FLT.Mazur.ProjectiveLine
