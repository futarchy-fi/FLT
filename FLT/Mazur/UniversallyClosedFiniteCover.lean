/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
/-!
# Universal closedness from a finite open cover

Images of closed sets are finite unions of the closed chart images. Apply the
same argument to the pulled-back cover for every base change.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace FLT.Mazur.UniversallyClosedFiniteCover
/-- Closedness of a map can be tested on a finite covering family of chart maps. -/
theorem closedMap {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.OpenCover.{v}) [Finite U.I₀]
    (h : ∀ i, IsClosedMap (U.f i ≫ f)) : IsClosedMap f := by
  intro s hs
  have he : f '' s = ⋃ i, (U.f i ≫ f) '' ((U.f i) ⁻¹' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, z, rfl⟩ := U.exists_eq x
      exact Set.mem_iUnion.mpr ⟨i, z, hx, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, z, hz, rfl⟩
      exact ⟨U.f i z, hz, rfl⟩
  rw [he]
  exact isClosed_iUnion_of_finite fun i ↦ h i _ (hs.preimage (U.f i).continuous)
/-- Universally closed chart maps in a finite open cover give universal closedness. -/
theorem universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.OpenCover.{v}) [Finite U.I₀]
    (h : ∀ i, UniversallyClosed (U.f i ≫ f)) : UniversallyClosed f := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have : Finite (U.pullback₁ i₁).I₀ := inferInstanceAs (Finite U.I₀)
  apply closedMap f' (U.pullback₁ i₁)
  intro i
  have := h i
  have hp := (IsPullback.of_hasPullback i₁ (U.f i)).paste_horiz H
  exact UniversallyClosed.universally_isClosedMap _ _ _ hp
end FLT.Mazur.UniversallyClosedFiniteCover
