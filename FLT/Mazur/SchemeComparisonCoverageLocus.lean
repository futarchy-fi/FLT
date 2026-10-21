/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# An original open locus of full comparison coverage

Remove the closure of the image of all points missed by a comparison.
The resulting original open has surjective restricted comparison. When the
missing image is closed, fiberwise coverage constructs membership in this
open; no selected component or reduced relation replaces the comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeComparisonCoverageLocus
variable {D K Z : Scheme.{0}} (k : D ⟶ K) (m : K ⟶ Z)

/-- Original image points obstructed by the closure of the entire missed comparison locus. -/
def badImage : Set Z := closure (m '' (Set.range k)ᶜ)

/-- The constructed open on which no full kernel-pair point is missed. -/
def goodOpen : Z.Opens := ⟨(badImage k m)ᶜ, isClosed_closure.isOpen_compl⟩

/-- Every target point over this open is in the actual comparison image. -/
theorem preimage_goodOpen_subset_range :
    (m ⁻¹ᵁ goodOpen k m : Set K) ⊆ Set.range k := by
  intro z hz
  by_contra hmiss
  exact hz (subset_closure ⟨z, hmiss, rfl⟩)

/-- The comparison restricted over the constructed original open is surjective. -/
theorem restrict_surjective : Surjective (k ∣_ (m ⁻¹ᵁ goodOpen k m)) := by
  constructor
  intro z
  obtain ⟨d, hd⟩ := preimage_goodOpen_subset_range k m z.property
  refine ⟨⟨d, ?_⟩, ?_⟩
  · change k d ∈ m ⁻¹ᵁ goodOpen k m
    rw [hd]
    exact z.property
  · apply Subtype.ext
    exact (morphismRestrict_base_coe k _ _).trans hd

/-- A closed missed image turns actual fiber coverage into an original open neighborhood. -/
theorem mem_goodOpen_iff_of_isClosed
    (hc : IsClosed (m '' (Set.range k)ᶜ)) (z : Z) :
    z ∈ goodOpen k m ↔ ∀ w : K, m w = z → w ∈ Set.range k := by
  change z ∉ closure (m '' (Set.range k)ᶜ) ↔ _
  rw [hc.closure_eq]
  constructor
  · intro hz w hw
    by_contra hmiss
    exact hz ⟨w, hmiss, hw⟩
  · rintro h ⟨w, hmiss, hw⟩
    exact hmiss (h w hw)

/-- A closed comparison image obstruction supplies a neighborhood with full coverage. -/
theorem exists_neighborhood_of_fiber_coverage
    (hc : IsClosed (m '' (Set.range k)ᶜ)) (z : Z)
    (hz : ∀ w : K, m w = z → w ∈ Set.range k) :
    ∃ U : Z.Opens, z ∈ U ∧ Surjective (k ∣_ (m ⁻¹ᵁ U)) :=
  ⟨goodOpen k m, (mem_goodOpen_iff_of_isClosed k m hc z).mpr hz,
    restrict_surjective k m⟩

end FLT.Mazur.SchemeComparisonCoverageLocus
