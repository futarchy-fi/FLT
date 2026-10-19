/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSubgroupOverlap

/-!
# Cartesian coefficient-base squares for the concrete subgroup overlaps

Pasting the subgroup pullback with the full comparison pullback retains the
actual original coefficient-base maps, ready for relative scheme gluing.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {A B : Type} [CommRing A] [CommRing B]
  (b c : Bool) (q : Spec (.of A) ⟶ normalizedLocus n b)
  (r : Spec (.of A) ⟶ normalizedLocus n c)
  (q' : Spec (.of B) ⟶ normalizedLocus n b) (r' : Spec (.of B) ⟶ normalizedLocus n c)
  (f : A →+* B) (hq : q' = Spec.map (CommRingCat.ofHom f) ≫ q)
  (hr : r' = Spec.map (CommRingCat.ofHom f) ≫ r)
local notation "m" => affineComparisonOverlapMap n b c q r q' r' f hq hr
local notation "i" => affineSubgroupInclusion n b c q r
local notation "i'" => affineSubgroupInclusion n b c q' r'
local notation "s" => affineComparisonStructure n b c q r
local notation "s'" => affineComparisonStructure n b c q' r'
local notation "k" => Spec.map (CommRingCat.ofHom f)

/-- The existing full comparison refinement is cartesian over the coefficient base. -/
theorem affineComparisonOverlap_isPullback : IsPullback s' m k s :=
  IsPullback.of_iso_pullback
    ⟨(affineComparisonOverlapMap_structure n b c q r q' r' f hq hr).symm⟩
    (affineComparisonOverlapIso n b c q r q' r' f hq hr)
    (affineComparisonOverlapIso_fst n b c q r q' r' f hq hr) rfl

/-- The concrete closed inclusion retains the coefficient-base structure. -/
@[reassoc] theorem affineSubgroupInclusion_structure :
    i ≫ s = affineSubgroupStructure n b c q r := rfl

/-- The subgroup overlaps commute with their original coefficient-base maps. -/
@[reassoc] theorem affineSubgroupOverlapMap_structure :
    affineSubgroupOverlapMap n b c q r q' r' f hq hr ≫
      affineSubgroupStructure n b c q r =
        affineSubgroupStructure n b c q' r' ≫ k := by
  rw [← affineSubgroupInclusion_structure, affineSubgroupOverlapMap_inclusion_assoc,
    affineComparisonOverlapMap_structure, ← Category.assoc,
    affineSubgroupInclusion_structure]

/-- The actual subgroup overlaps are cartesian over the original affine coefficient bases. -/
theorem affineSubgroupOverlap_base_isPullback :
    IsPullback (affineSubgroupStructure n b c q' r')
      (affineSubgroupOverlapMap n b c q r q' r' f hq hr) k
      (affineSubgroupStructure n b c q r) :=
  (affineSubgroupOverlap_isPullback n b c q r q' r' f hq hr).paste_horiz
    (affineComparisonOverlap_isPullback n b c q r q' r' f hq hr)

end FLT.Mazur.CyclicCharacteristicAtlas
