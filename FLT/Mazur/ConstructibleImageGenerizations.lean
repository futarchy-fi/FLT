/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Actual generizations witnessing scalar image closures

Compactness in the constructible topology supplies an actual source point
above a generization of every point of the image closure. No closedness of
the image, finite presentation, or Noetherianity of the target is required.
-/

@[expose] public noncomputable section
open TopologicalSpace Topology
namespace FLT.Mazur.ConstructibleImageGenerizations
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A constructibly compact source set has actual witnesses for every image-closure point. -/
theorem mem_closure_image_iff [PrespectralSpace Y] (f : X → Y) (hf : IsSpectralMap f)
    {Z : Set X} (hZ : @IsCompact X (constructibleTopology X) Z) (y : Y) :
    y ∈ closure (f '' Z) ↔ ∃ x ∈ Z, f x ⤳ y := by
  constructor
  · intro hy
    let I := {U : Set Y // IsOpen U ∧ IsCompact U ∧ y ∈ U}
    have hc : ∀ U : I, IsClosed[constructibleTopology X] (f ⁻¹' U.val) := fun U ↦
      IsCompact.isClosed_constructibleTopology_of_isOpen
        (hf.isCompact_preimage_of_isOpen U.property.1 U.property.2.1)
        (U.property.1.preimage hf.continuous)
    have hn : ∀ a : Finset I, (Z ∩ ⋂ U ∈ a, f ⁻¹' U.val).Nonempty := by
      intro a
      have ho : IsOpen (⋂ U ∈ a, U.val) :=
        isOpen_biInter_finset fun U _ ↦ U.property.1
      have hym : y ∈ ⋂ U ∈ a, U.val :=
        Set.mem_iInter₂.mpr fun U _ ↦ U.property.2.2
      obtain ⟨z, hz, x, hx, hfx⟩ := mem_closure_iff.mp hy _ ho hym
      refine ⟨x, hx, Set.mem_iInter₂.mpr fun U hU ↦ ?_⟩
      change f x ∈ U.val
      rw [hfx]
      exact Set.mem_iInter₂.mp hz U hU
    have hw : (Z ∩ ⋂ U : I, f ⁻¹' U.val).Nonempty := by
      let _ : TopologicalSpace X := constructibleTopology X
      exact hZ.inter_iInter_nonempty _ hc hn
    obtain ⟨x, hxZ, hx⟩ := hw
    refine ⟨x, hxZ, specializes_iff_forall_open.mpr ?_⟩
    intro V hV hyV
    obtain ⟨U, hU, hyU, hUV⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyV hV
    exact hUV (Set.mem_iInter.mp hx ⟨U, hU.1, hU.2, hyU⟩)
  · rintro ⟨x, hx, hxy⟩
    exact hxy.mem_closed isClosed_closure (subset_closure ⟨x, hx, rfl⟩)

/-- Closed constructible subsets of a spectral space satisfy the required compactness. -/
theorem compact_of_constructibly_closed [CompactSpace X] [QuasiSober X]
    [PrespectralSpace X] [QuasiSeparatedSpace X] {Z : Set X}
    (hZ : IsClosed[constructibleTopology X] Z) :
    @IsCompact X (constructibleTopology X) Z := by
  let τ := constructibleTopology X
  have : CompactSpace (WithTopology X τ) := inferInstance
  let _ : TopologicalSpace X := τ
  let _ : CompactSpace X := Function.Surjective.compactSpace
    (WithTopology.continuous_ofTopology (X := X) (t := τ))
    (WithTopology.ofTopology_surjective τ)
  exact hZ.isCompact

end FLT.Mazur.ConstructibleImageGenerizations
