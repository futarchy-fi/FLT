/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineOrbitCover

/-!
# The affine sources have the actual quotient topology

The map from each original affine parameter scheme to its full orbit image is
surjective and detects open sets. All full same-chart comparisons are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- The original affine parameter map, with codomain its actual quotient open. -/
def affineOrbitProjection :
    (invariantAffineChart n i).toTopCat ⟶
      (Opens.toTopCat (space n)).obj (affineOrbitOpen n i) :=
  TopCat.ofHom ⟨fun x => ⟨chartProjection n i.1 (invariantAffineInclusion n i x),
    ⟨_, ⟨x, rfl⟩, rfl⟩⟩,
    ((chartProjection_continuous n i.1).comp
      (invariantAffineInclusion n i).continuous).subtype_mk _⟩

/-- Every point of the descended open has an original affine representative. -/
theorem affineOrbitProjection_surjective : Function.Surjective (affineOrbitProjection n i) := by
  intro z
  obtain ⟨x, hx⟩ := (Set.ext_iff.mp (affineOrbitOpen_range n i) z.val).mpr z.property
  exact ⟨x, Subtype.ext hx⟩

/-- The selected-chart preimage of a subset is its affine preimage included in the chart. -/
theorem affineOrbitProjection_preimage_image (S : Set (affineOrbitOpen n i)) :
    chartProjection n i.1 ⁻¹' (Subtype.val '' S) =
      invariantAffineInclusion n i '' (affineOrbitProjection n i ⁻¹' S) := by
  ext x
  constructor
  · rintro ⟨z, hz, he⟩
    have hx : x ∈ chartProjection n i.1 ⁻¹' (affineOrbitOpen n i : Set _) := by
      change chartProjection n i.1 x ∈ affineOrbitOpen n i
      rw [← he]
      exact z.property
    rw [affineOrbitOpen_preimage] at hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    have hy : affineOrbitProjection n i y = z := Subtype.ext he.symm
    change affineOrbitProjection n i y ∈ S
    rwa [hy]
  · rintro ⟨y, hy, rfl⟩
    exact ⟨affineOrbitProjection n i y, hy, rfl⟩

/-- The original affine map detects exactly the topology on the full quotient open. -/
theorem affineOrbitProjection_isQuotientMap : IsQuotientMap (affineOrbitProjection n i) := by
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen (fun S => ?_),
    affineOrbitProjection_surjective n i⟩
  constructor
  · intro h
    apply (Opens.isOpenEmbedding (X := space n)
      (affineOrbitOpen n i)).isOpen_iff_image_isOpen.mpr
    apply (chartProjection_isOpen_iff n i.1 (Subtype.val '' S) ?_).mpr
    · exact (affineOrbitProjection_preimage_image n i S).symm ▸
        (invariantAffineInclusion n i).isOpenMap _ h
    · rintro _ ⟨z, _, rfl⟩
      exact affineOrbitOpen_le n i z.property
  · intro h
    exact h.preimage (affineOrbitProjection n i).hom.continuous

end FLT.Mazur.CyclicCharacteristicOrbit
