/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicRingedCoequalizer

/-!
# Local rings on the explicit invariant orbit space

The invariant sheaf has local stalks, by the proved ringed comparison with the
locally ringed coequalizer. Thus the original orbit carrier and invariant sheaf
together form the actual locally ringed quotient, still without affine charts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- Every stalk of the explicitly constructed invariant sheaf is a local ring. -/
theorem invariantStalk_isLocalRing (x : Orbit n) :
    IsLocalRing (TopCat.Presheaf.stalk (C := CommRingCat) (invariantSheaf n).obj x) := by
  let i := SheafedSpace.forgetToPresheafedSpace.mapIso
    (locallyRingedOrbitRingedIso n).symm
  apply @RingEquiv.isLocalRing _ _ _
    ((locallyRingedQuotient n).isLocalRing (i.hom.base x))
  exact (PresheafedSpace.stalkMap.stalkIso i x).commRingCatIsoToRingEquiv

/-- The actual orbit carrier with invariant functions is a locally ringed space. -/
def invariantLocallyRingedSpace : LocallyRingedSpace where
  toSheafedSpace := ringedSpace n
  isLocalRing := invariantStalk_isLocalRing n

/-- The explicit invariant locally ringed space agrees with the abstract coequalizer. -/
def invariantLocallyRingedIso :
    locallyRingedQuotient n ≅ invariantLocallyRingedSpace n :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (locallyRingedOrbitRingedIso n)

/-- The original source maps to the explicit invariant locally ringed quotient. -/
def invariantLocallyRingedProjection :
    (U).toLocallyRingedSpace ⟶ invariantLocallyRingedSpace n :=
  locallyRingedProjection n ≫ (invariantLocallyRingedIso n).hom

/-- This locally ringed morphism has the already constructed ringed projection. -/
theorem invariantLocallyRingedProjection_toShHom :
    (invariantLocallyRingedProjection n).toShHom = toRingedSpace n :=
  locallyRingedProjection_ringedIso n

/-- Its continuous map is the actual orbit projection. -/
theorem invariantLocallyRingedProjection_base :
    (invariantLocallyRingedProjection n).base = quotientMap n :=
  congrArg (fun k ↦ k.hom.base) (invariantLocallyRingedProjection_toShHom n)

end FLT.Mazur.CyclicCharacteristicOrbit
