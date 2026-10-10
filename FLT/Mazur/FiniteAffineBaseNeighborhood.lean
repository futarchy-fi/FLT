/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelativeFiberNeighborhood

/-!
# Shrinking a finite morphism to an affine base neighborhood

Finiteness persists under a smaller target restriction. Consequently the
neighborhood obtained from a finite base fiber can always be chosen affine.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.Approximation

/-- Finiteness on a target open persists on every smaller target open. -/
theorem finite_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Opens} (hUV : U ≤ V) [IsFinite (f ∣_ V)] : IsFinite (f ∣_ U) := by
  have h : IsFinite (f ∣_ V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U))).mp inferInstance
  rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr hUV] at h

/-- A finite restriction over a base neighborhood can be shrunk to an affine neighborhood. -/
theorem exists_affine_finite_neighborhood {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (s : S) (V : S.Opens) (hs : s ∈ V)
    [IsFinite (f ∣_ (g ⁻¹ᵁ V))] :
    ∃ U : S.Opens, s ∈ U ∧ IsAffineOpen U ∧ U ≤ V ∧
      IsFinite (f ∣_ (g ⁻¹ᵁ U)) := by
  obtain ⟨U, hU, hsU, hUV⟩ := exists_isAffineOpen_mem_and_subset hs
  exact ⟨U, hsU, hU, hUV, finite_morphismRestrict_of_le f (g.preimage_mono hUV)⟩

/-- A finite actual base fiber spreads to finiteness over an affine neighborhood. -/
theorem exists_affine_finite_neighborhood_of_fiber {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [IsProper (f ≫ g)] [IsSeparated g] (s : S)
    [IsFinite (RelativeFiber.map f g s)] :
    ∃ U : S.Opens, s ∈ U ∧ IsAffineOpen U ∧ IsFinite (f ∣_ (g ⁻¹ᵁ U)) := by
  obtain ⟨V, hsV, hV⟩ := RelativeFiber.exists_finite_neighborhood f g s
  obtain ⟨U, hsU, hU, _, hf⟩ := exists_affine_finite_neighborhood f g s V hsV
  exact ⟨U, hsU, hU, hf⟩

end FLT.Mazur.Approximation
