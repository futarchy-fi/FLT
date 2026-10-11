/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationRingedCoequalizer

/-!
# The quotient structure sheaf is the invariant sheaf

Transport along the canonical orbit homeomorphism identifies the locally ringed
quotient's structure sheaf with invariant regular functions. The comparison
also identifies pullback to the original source scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- The ringed comparison has the already constructed canonical orbit homeomorphism as base. -/
theorem locallyRingedOrbitRingedIso_base :
    (locallyRingedOrbitRingedIso e).hom.hom.base = (locallyRingedOrbitIso e).hom := by
  ext z
  obtain ⟨x, rfl⟩ := locallyRingedProjection_surjective e z
  exact (congrArg (fun k ↦ k.hom.base x) (locallyRingedProjection_ringedIso e)).trans
    (congrArg (fun k ↦ k x) (locallyRingedProjection_orbitIso e)).symm

/-- The quotient's actual structure sheaf transported to the orbit space. -/
def quotientOrbitSheaf : (space e).Sheaf CommRingCat.{u} :=
  (TopCat.Sheaf.pushforward _ (locallyRingedOrbitRingedIso e).hom.hom.base).obj
    (locallyRingedQuotient (p := p) (q := q)).toSheafedSpace.sheaf

/-- Invariant regular functions are the transported locally ringed structure sheaf. -/
def invariantSheafIsoQuotient : invariantSheaf e ≅ quotientOrbitSheaf e :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (PresheafedSpace.sheafIsoOfIso
      (SheafedSpace.forgetToPresheafedSpace.mapIso (locallyRingedOrbitRingedIso e)))

/-- Pullback from the transported quotient structure sheaf to the original source. -/
def quotientOrbitSource : quotientOrbitSheaf e ⟶ sourceSheaf e :=
  ⟨(TopCat.Presheaf.pushforward _ (locallyRingedOrbitRingedIso e).hom.hom.base).map
      (locallyRingedProjection (p := p) (q := q)).c ≫
    (TopCat.Presheaf.pushforwardEq
      (congrArg (fun k ↦ k.hom.base) (locallyRingedProjection_ringedIso e))
      U.left.presheaf).hom⟩

/-- The structure-sheaf comparison respects the original regular-function pullback. -/
theorem invariantSheafIsoQuotient_source :
    (invariantSheafIsoQuotient e).hom ≫ quotientOrbitSource e = invariantInclusion e := by
  apply (TopCat.Sheaf.forget _ _).map_injective
  apply NatTrans.ext
  funext W
  have h := PresheafedSpace.congr_app
    (congrArg (fun k ↦ k.hom) (locallyRingedProjection_ringedIso e)) W
  change (locallyRingedOrbitRingedIso e).hom.hom.c.app W ≫
      (locallyRingedProjection (p := p) (q := q)).c.app _ =
    (invariantInclusion e).hom.app W ≫ U.left.presheaf.map (eqToHom _) at h
  change (locallyRingedOrbitRingedIso e).hom.hom.c.app W ≫
    (locallyRingedProjection (p := p) (q := q)).c.app _ ≫
      (TopCat.Presheaf.pushforwardEq
        (congrArg (fun k ↦ k.hom.base) (locallyRingedProjection_ringedIso e))
        U.left.presheaf).hom.app W = _
  rw [TopCat.Presheaf.pushforwardEq_hom_app, ← Category.assoc, h,
    Category.assoc, ← Functor.map_comp]
  simp only [eqToHom_trans, eqToHom_refl]
  erw [U.left.presheaf.map_id]
  exact Category.comp_id ((invariantInclusion e).hom.app W)

/-- The same structure-sheaf comparison along the original carrier comparison. -/
def invariantSheafIsoCanonicalQuotient : invariantSheaf e ≅
    (TopCat.Sheaf.pushforward _ (locallyRingedOrbitIso e).hom).obj
      (locallyRingedQuotient (p := p) (q := q)).toSheafedSpace.sheaf :=
  invariantSheafIsoQuotient e ≪≫ eqToIso (by
    unfold quotientOrbitSheaf
    rw [locallyRingedOrbitRingedIso_base])

end FLT.Mazur.RelativeRelationOrbit
