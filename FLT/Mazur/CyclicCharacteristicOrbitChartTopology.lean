/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitChartImage

/-!
# Quotient topology from a single normalized characteristic chart

The fppf transition covers detect openness on the opposite component. Thus a
subset of a characteristic orbit open is open exactly when its inverse image
in that original normalized chart is open. No finite relabeling orbit relation
is substituted for the full comparison relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Inverse images on the opposite chart are images along actual transition sources. -/
theorem chartProjection_preimage_transition (b : Bool) (S : Set (Orbit n))
    (hS : S ⊆ (integerOpen n (chartInteger (!b))).carrier) :
    chartProjection n b ⁻¹' S =
      ⋃ i, transitionSource n b i ''
        ((chartProjection n (!b) ∘ transitionTarget n b i) ⁻¹' S) := by
  ext x
  constructor
  · intro hx
    have hxO : x ∈ transitionOpen n b :=
      (mem_integerOpen_iff n (chartInteger (!b)) b x).mp (hS hx)
    obtain ⟨i, y, hy⟩ := (transitionSource_covers n b x).mpr hxO
    refine Set.mem_iUnion.mpr ⟨i, y, ?_, hy⟩
    change chartProjection n (!b) (transitionTarget n b i y) ∈ S
    rw [chartProjection_transition, hy]
    exact hx
  · intro hx
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    change chartProjection n b (transitionSource n b i y) ∈ S
    rwa [← chartProjection_transition]

/-- Transition sources are open, so openness on one chart propagates to the other. -/
theorem chartProjection_opposite_isOpen (b : Bool) (S : Set (Orbit n))
    (hS : S ⊆ (integerOpen n (chartInteger (!b))).carrier)
    (hO : IsOpen (chartProjection n (!b) ⁻¹' S)) :
    IsOpen (chartProjection n b ⁻¹' S) := by
  rw [chartProjection_preimage_transition n b S hS]
  apply isOpen_iUnion
  intro i
  exact (transitionSource n b i).isOpenMap _
    (hO.preimage (transitionTarget n b i).continuous)

/-- The original normalized chart detects the topology of its full orbit open. -/
theorem chartProjection_isOpen_iff (b : Bool) (S : Set (Orbit n))
    (hS : S ⊆ (integerOpen n (chartInteger b)).carrier) :
    IsOpen S ↔ IsOpen (chartProjection n b ⁻¹' S) := by
  refine ⟨fun h => h.preimage (chartProjection_continuous n b), fun h => ?_⟩
  apply (projection_isQuotientMap n).isOpen_preimage.mp
  have he : projection n ⁻¹' S =
      ⋃ c, normalizedDisjointInclusion n c '' (chartProjection n c ⁻¹' S) := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, y, rfl⟩ := normalizedDisjointSource_covers n x
      exact Set.mem_iUnion.mpr ⟨c, y, hx, rfl⟩
    · intro hx
      obtain ⟨c, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact hy
  rw [he]
  apply isOpen_iUnion
  intro c
  apply (normalizedDisjointInclusion n c).isOpenMap
  by_cases hc : c = b
  · subst c
    exact h
  · have hb : b = !c := by cases b <;> cases c <;> simp_all
    subst b
    exact chartProjection_opposite_isOpen n c S hS h

/-- The selected chart surjects with exactly the subspace quotient topology. -/
theorem chartToIntegerOpen_isQuotientMap (b : Bool) :
    IsQuotientMap (chartToIntegerOpen n b) := by
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen (fun S => ?_),
    chartToIntegerOpen_surjective n b⟩
  have he : chartProjection n b ⁻¹' (Subtype.val '' S) =
      chartToIntegerOpen n b ⁻¹' S := by
    ext x
    change (chartToIntegerOpen n b x).val ∈ Subtype.val '' S ↔ chartToIntegerOpen n b x ∈ S
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (Subtype.ext hxy) ▸ hy
    · intro hx
      exact ⟨_, hx, rfl⟩
  rw [← he]
  refine (chartProjection_isOpen_iff n b (Subtype.val '' S) ?_).symm.trans
    (Opens.isOpenEmbedding (X := space n)
      (integerOpen n (chartInteger b))).isOpen_iff_image_isOpen.symm
  rintro _ ⟨x, _, rfl⟩
  exact x.property

end FLT.Mazur.CyclicCharacteristicOrbit
