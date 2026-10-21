/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeComparisonClosedObstruction

/-!
# Full comparison coverage from a locally closed obstruction

A missed image need only be closed over one original image neighborhood.
Full coverage of a fiber then gives a smaller original open with surjective
comparison; the original target and its entire fibers are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeComparisonCoverageLocus
set_option backward.isDefEq.respectTransparency false
variable {D K Z : Scheme.{0}} (k : D ⟶ K) (m : K ⟶ Z) (U : Z.Opens)
set_option quotPrecheck false
local notation "kU" => k ∣_ (m ⁻¹ᵁ U)
local notation "mU" => m ∣_ U

/-- Restriction preserves exactly the original comparison image over the chosen open. -/
theorem mem_restricted_range_iff (w : (m ⁻¹ᵁ U).toScheme) :
    w ∈ Set.range kU ↔ w.val ∈ Set.range k := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d.val, (morphismRestrict_base_coe k _ d).symm.trans (congrArg Subtype.val hd)⟩
  · rintro ⟨d, hd⟩
    refine ⟨⟨d, ?_⟩, ?_⟩
    · change k d ∈ m ⁻¹ᵁ U
      rw [hd]
      exact w.property
    · apply Subtype.ext
      exact (morphismRestrict_base_coe k _ _).trans hd

/-- The local good open defines a genuine smaller open of the original image. -/
def localGoodOpen : Z.Opens := U.ι ''ᵁ goodOpen kU mU

/-- The constructed original open stays inside the supplied geometry neighborhood. -/
theorem localGoodOpen_le : localGoodOpen k m U ≤ U := U.ι_image_le _

/-- The entire original comparison is surjective over the constructed smaller open. -/
theorem localGoodOpen_surjective : Surjective (k ∣_ (m ⁻¹ᵁ localGoodOpen k m U)) := by
  constructor
  intro w
  have hw : m w.val ∈ localGoodOpen k m U := w.property
  obtain ⟨z, hz, heq⟩ := hw
  have hwU : m w.val ∈ U := heq ▸ z.property
  let wU : (m ⁻¹ᵁ U).toScheme := ⟨w.val, hwU⟩
  have hm : mU wU = z := by
    apply Subtype.ext
    exact (morphismRestrict_base_coe m U wU).trans heq.symm
  have hcov := preimage_goodOpen_subset_range kU mU (show mU wU ∈ goodOpen kU mU by
    rw [hm]; exact hz)
  obtain ⟨d, hd⟩ := (mem_restricted_range_iff k m U wU).mp hcov
  refine ⟨⟨d, ?_⟩, ?_⟩
  · change k d ∈ m ⁻¹ᵁ localGoodOpen k m U
    rw [hd]
    exact w.property
  · apply Subtype.ext
    exact (morphismRestrict_base_coe k _ _).trans hd

/-- Local closedness and full original fiber coverage produce a smaller coverage neighborhood. -/
theorem exists_neighborhood_of_local_fiber_coverage
    (hc : IsClosed (mU '' (Set.range kU)ᶜ)) (z : Z) (hzU : z ∈ U)
    (hz : ∀ w : K, m w = z → w ∈ Set.range k) :
    ∃ V : Z.Opens, V ≤ U ∧ z ∈ V ∧ Surjective (k ∣_ (m ⁻¹ᵁ V)) := by
  refine ⟨localGoodOpen k m U, localGoodOpen_le k m U, ?_,
    localGoodOpen_surjective k m U⟩
  refine ⟨⟨z, hzU⟩, ?_, rfl⟩
  apply (mem_goodOpen_iff_of_isClosed kU mU hc ⟨z, hzU⟩).mpr
  intro w hw
  apply (mem_restricted_range_iff k m U w).mpr
  apply hz w.val
  exact (morphismRestrict_base_coe m U w).symm.trans (congrArg Subtype.val hw)

end FLT.Mazur.SchemeComparisonCoverageLocus
