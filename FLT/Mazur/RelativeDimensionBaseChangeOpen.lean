/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Relative dimension after base change from neighborhoods of the image

Relative-dimension opens around every image point pull back to an open cover
of the actual base change. No dimension hypothesis outside that image is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.RelativeDimensionBaseChangeOpen

set_option backward.isDefEq.respectTransparency false

universe u

/-- Relative-dimension neighborhoods of every image point determine the actual base change. -/
theorem of_exists_open {X S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S) (d : ℕ)
    (h : ∀ z : ↥(pullback f b), ∃ V : X.Opens, pullback.fst f b z ∈ V ∧
      SmoothOfRelativeDimension d (V.ι ≫ f)) :
    SmoothOfRelativeDimension d (pullback.snd f b) := by
  choose V hx hd using h
  have hcover : (⨆ z, pullback.fst f b ⁻¹ᵁ V z) = ⊤ := by
    apply top_le_iff.mp
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hx z⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d)
    (fun z ↦ pullback.fst f b ⁻¹ᵁ V z) hcover
  intro z
  exact MorphismProperty.of_isPullback
    ((isPullback_morphismRestrict (pullback.fst f b) (V z)).paste_vert
      (IsPullback.of_hasPullback f b)) (hd z)

end FLT.Mazur.RelativeDimensionBaseChangeOpen
