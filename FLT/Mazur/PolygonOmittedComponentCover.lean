/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedFiberIdeal
public import FLT.Mazur.ProjectiveLineEndpointCover

/-!
# The omitted complete components cover the collapsed fiber

Both retained endpoints belong to neighboring omitted components. Hence the
whole fiber support is the finite union of those complete component images,
including when a two-gon leaves just one projective line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonOmittedComponentCover
open PolygonCyclicAtlas PolygonOneGonContraction PolygonCollapsedFiberIdeal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)
local notation "p" => normalization K n h
local notation "q" => nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "F" => fiberIdeal K n (by omega) p q hp i

/-- The exact support is the union of the original omitted complete component images. -/
theorem support_eq : ((F).support : Set (polygon K n h).left) =
    ⋃ j : {j : Fin n // j ≠ i}, Set.range (componentMap K n h j.val) := by
  let _ : NeZero n := ⟨by omega⟩
  ext x
  constructor
  · intro hx
    obtain ⟨j, z, hz⟩ := PolygonComponentImages.cover K n (by omega) p q hp x
    rw [componentι_normalization] at hz
    change componentMap K n h j z = x at hz
    subst x
    by_cases hj : j = i
    · subst j
      rcases ProjectiveLine.torus_or_endpoints K z with ⟨t, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [fiberIdeal_support, componentι_normalization] at hx
        exact (hx ⟨t, Scheme.Hom.comp_apply _ _ _⟩).elim
      · refine Set.mem_iUnion.mpr ⟨⟨finRotate n i,
          (PolygonCyclicNormalizationPullback.successor_ne n h i).symm⟩, ?_⟩
        refine ⟨ProjectiveLine.infinity K a, ?_⟩
        change (ProjectiveLine.infinity K ≫ componentMap K n h (finRotate n i)) a =
          (ProjectiveLine.zero K ≫ componentMap K n h i) a
        rw [infinity_componentMap, zero_componentMap, Equiv.symm_apply_apply]
      · refine Set.mem_iUnion.mpr ⟨⟨(finRotate n).symm i, prev_ne h i⟩, ?_⟩
        refine ⟨ProjectiveLine.zero K a, ?_⟩
        change (ProjectiveLine.zero K ≫ componentMap K n h ((finRotate n).symm i)) a =
          (ProjectiveLine.infinity K ≫ componentMap K n h i) a
        rw [zero_componentMap, infinity_componentMap]
    · exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, z, rfl⟩
  · rintro hx
    obtain ⟨j, z, rfl⟩ := Set.mem_iUnion.mp hx
    have hz : z ∈ ((F).comap (componentMap K n h j.val)).support := by
      rw [component_omitted K n h i j.property]
      trivial
    rw [Scheme.IdealSheafData.support_comap] at hz
    exact hz

/-- The finite union of omitted images is closed in the original polygon. -/
theorem omittedUnion_isClosed :
    IsClosed (⋃ j : {j : Fin n // j ≠ i}, Set.range (componentMap K n h j.val)) := by
  rw [← support_eq K n h i]
  exact (F).support.isClosed

end FLT.Mazur.PolygonOmittedComponentCover
