/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionDivisors

/-!
# Cartier descent from an open containing the full support

A regular equation only needs to be checked along the closed subscheme.
An open immersion containing its full support therefore detects the Cartier
condition; outside that support the equation is the unit section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} (I : Y.IdealSheafData) (j : X ⟶ Y) [IsOpenImmersion j]

/-- An open containing the entire closed family detects the effective Cartier condition. -/
theorem effectiveCartier_of_comap_of_support_subset
    (hs : Set.range I.subschemeι ⊆ Set.range j)
    (hI : EffectiveCartier (I.comap j)) : EffectiveCartier I := by
  rw [effectiveCartier_iff_on_support]
  intro x hx
  change x ∈ (I.support : Set Y) at hx
  have hx' : x ∈ Set.range I.subschemeι := by
    simpa only [I.range_subschemeι] using hx
  obtain ⟨y, rfl⟩ := hs hx'
  obtain ⟨U, hy, hU⟩ := hI y
  exact ⟨⟨j ''ᵁ U, U.2.image_of_isOpenImmersion j⟩, ⟨y, hy, rfl⟩,
    (cartierChart_comap_iff I j U).mp hU⟩

/-- Restricting to a support-containing open preserves and detects the Cartier condition. -/
theorem effectiveCartier_comap_iff_of_support_subset
    (hs : Set.range I.subschemeι ⊆ Set.range j) :
    EffectiveCartier (I.comap j) ↔ EffectiveCartier I :=
  ⟨effectiveCartier_of_comap_of_support_subset I j hs,
    fun h ↦ h.comap_of_isOpenImmersion j⟩

end FLT.Mazur.FCurve
