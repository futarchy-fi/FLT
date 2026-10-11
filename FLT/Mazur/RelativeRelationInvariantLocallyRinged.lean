/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationQuotientSheaf

/-!
# Local rings on the explicit invariant orbit space

The invariant sheaf has local stalks, by the proved ringed comparison with the
locally ringed coequalizer. Thus the original orbit carrier and invariant sheaf
together form the actual locally ringed quotient, still without affine charts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- Every stalk of the explicitly constructed invariant sheaf is a local ring. -/
theorem invariantStalk_isLocalRing (x : Orbit e) :
    IsLocalRing (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invariantSheaf e).obj x) := by
  let i := SheafedSpace.forgetToPresheafedSpace.mapIso
    (locallyRingedOrbitRingedIso e).symm
  apply @RingEquiv.isLocalRing _ _ _
    ((locallyRingedQuotient (p := p) (q := q)).isLocalRing (i.hom.base x))
  exact (PresheafedSpace.stalkMap.stalkIso i x).commRingCatIsoToRingEquiv

/-- The actual orbit carrier with invariant functions is a locally ringed space. -/
def invariantLocallyRingedSpace : LocallyRingedSpace.{u} where
  toSheafedSpace := ringedSpace e
  isLocalRing := invariantStalk_isLocalRing e

/-- The explicit invariant locally ringed space agrees with the abstract coequalizer. -/
def invariantLocallyRingedIso :
    locallyRingedQuotient (p := p) (q := q) ≅ invariantLocallyRingedSpace e :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (locallyRingedOrbitRingedIso e)

/-- The original source maps to the explicit invariant locally ringed quotient. -/
def invariantLocallyRingedProjection :
    U.left.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace e :=
  locallyRingedProjection ≫ (invariantLocallyRingedIso e).hom

/-- This locally ringed morphism has the already constructed ringed projection. -/
theorem invariantLocallyRingedProjection_toShHom :
    (invariantLocallyRingedProjection e).toShHom = toRingedSpace e :=
  locallyRingedProjection_ringedIso e

/-- Its continuous map is the actual orbit projection. -/
theorem invariantLocallyRingedProjection_base :
    (invariantLocallyRingedProjection e).base = quotientMap e :=
  congrArg (fun k ↦ k.hom.base) (invariantLocallyRingedProjection_toShHom e)

/-- The invariant quotient retains the original relative base. -/
def invariantLocallyRingedBaseMap : invariantLocallyRingedSpace e ⟶
    S.toLocallyRingedSpace :=
  (invariantLocallyRingedIso e).inv ≫ locallyRingedBaseMap

/-- The actual original structural morphism factors through this explicit quotient. -/
theorem invariantLocallyRingedProjection_baseMap :
    invariantLocallyRingedProjection e ≫ invariantLocallyRingedBaseMap e =
      U.hom.toLRSHom := by
  dsimp only [invariantLocallyRingedProjection, invariantLocallyRingedBaseMap]
  rw [← Category.assoc, Category.assoc locallyRingedProjection,
    Iso.hom_inv_id, Category.comp_id, locallyRingedProjection_baseMap]

end FLT.Mazur.RelativeRelationOrbit
