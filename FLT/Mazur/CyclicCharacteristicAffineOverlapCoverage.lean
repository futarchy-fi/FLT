/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineOverlapArrows

/-!
# The full refined comparison scheme covers the actual quotient overlap

The image of the restricted original arrow scheme is exactly the intersection
of the descended affine-source opens, including overlaps between characteristics.
This is coverage by actual arrows, not yet descent of the span to a scheme graph.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i j : InvariantAffineIndex n)

/-- The original source endpoint projects to exactly the full quotient overlap. -/
theorem affineOverlap_projection_range :
    Set.range ((affineLocallyRingedProjection n i).base ∘ affineOverlapSource n i j) =
      (affineOrbitOpen n i ⊓ affineOrbitOpen n j : Set (Orbit n)) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    constructor
    · rw [Function.comp_apply, affineLocallyRingedProjection_base]
      exact ⟨_, ⟨affineOverlapSource n i j a, rfl⟩, rfl⟩
    · have he := congrArg (fun f => f.base a) (affineOverlap_projection_condition n i j)
      change (affineLocallyRingedProjection n i).base (affineOverlapSource n i j a) =
        (affineLocallyRingedProjection n j).base (affineOverlapTarget n i j a) at he
      rw [Function.comp_apply, he, affineLocallyRingedProjection_base]
      exact ⟨_, ⟨affineOverlapTarget n i j a, rfl⟩, rfl⟩
  · rintro ⟨hi, hj⟩
    obtain ⟨x, hx, hxi⟩ := hi
    obtain ⟨y, hy, hyj⟩ := hj
    obtain ⟨a, ha, ht⟩ := (chartProjection_eq_iff n i.1 j.1 x y).mp (hxi.trans hyj.symm)
    have hmem : a ∈ affineOverlapDomain n i j := by
      constructor
      · change productArrowSource n i.1 j.1 a ∈ Set.range (invariantAffineInclusion n i)
        rwa [ha]
      · change productArrowTarget n i.1 j.1 a ∈ Set.range (invariantAffineInclusion n j)
        rwa [ht]
    refine ⟨⟨a, hmem⟩, ?_⟩
    rw [Function.comp_apply, affineLocallyRingedProjection_base]
    have hs := congrArg (fun f => f ⟨a, hmem⟩) (affineOverlapSource_inclusion n i j)
    change invariantAffineInclusion n i (affineOverlapSource n i j ⟨a, hmem⟩) =
      productArrowSource n i.1 j.1 a at hs
    rw [hs, ha]
    exact hxi

end FLT.Mazur.CyclicCharacteristicOrbit
