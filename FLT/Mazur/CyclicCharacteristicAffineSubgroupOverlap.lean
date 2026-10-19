/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineOriginalSubgroupOverlap

/-!
# The concrete closed subgroup schemes on named affine overlaps

The original-family identification gives the scheme pullback for the
previously constructed concrete subgroup schemes, retaining both projections.
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
local notation "j" => affineOriginalSubgroupInclusion n b c q r
local notation "a" => affineOriginalSubgroupLocusIso n b c q r
local notation "a'" => affineOriginalSubgroupLocusIso n b c q' r'

/-- The concrete closed subgroup scheme on a named refinement is the actual scheme pullback. -/
def affineSubgroupOverlapIso : affineSubgroupScheme n b c q' r' ≅ pullback m i :=
  a' ≪≫ affineOriginalSubgroupOverlapIso n b c q r q' r' f hq hr ≪≫
    asIso (pullback.map m j m i (𝟙 _) (a).inv (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp])
      (by
        rw [Category.comp_id]
        apply (Iso.eq_inv_comp _).mpr
        exact affineOriginalSubgroupLocusIso_inclusion n b c q r))

/-- The pullback identification keeps the existing refined closed immersion. -/
@[reassoc] theorem affineSubgroupOverlapIso_fst :
    (affineSubgroupOverlapIso n b c q r q' r' f hq hr).hom ≫ pullback.fst _ _ = i' := by
  simp only [affineSubgroupOverlapIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.map, pullback.lift_fst, Category.comp_id]
  rw [affineOriginalSubgroupOverlapIso_fst, affineOriginalSubgroupLocusIso_inclusion]

/-- The named affine comparison overlap restricts to the actual closed subgroup schemes. -/
def affineSubgroupOverlapMap :
    affineSubgroupScheme n b c q' r' ⟶ affineSubgroupScheme n b c q r :=
  (affineSubgroupOverlapIso n b c q r q' r' f hq hr).hom ≫ pullback.snd _ _

/-- Restriction retains the full comparison parameter and the original closed immersions. -/
@[reassoc] theorem affineSubgroupOverlapMap_inclusion :
    affineSubgroupOverlapMap n b c q r q' r' f hq hr ≫ i = i' ≫ m := by
  rw [affineSubgroupOverlapMap, Category.assoc, ← pullback.condition,
    ← Category.assoc, affineSubgroupOverlapIso_fst]

/-- The constructed closed subgroup overlap is a pullback on arbitrary scheme tests. -/
theorem affineSubgroupOverlap_isPullback :
    IsPullback i' (affineSubgroupOverlapMap n b c q r q' r' f hq hr) m i :=
  IsPullback.of_iso_pullback
    ⟨(affineSubgroupOverlapMap_inclusion n b c q r q' r' f hq hr).symm⟩
    (affineSubgroupOverlapIso n b c q r q' r' f hq hr)
    (affineSubgroupOverlapIso_fst n b c q r q' r' f hq hr) rfl

end FLT.Mazur.CyclicCharacteristicAtlas
