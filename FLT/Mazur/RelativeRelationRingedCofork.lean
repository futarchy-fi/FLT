/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationOrbitCoequalizer

/-!
# The invariant ringed orbit cofork

The orbit projection identifies the two original relation morphisms as maps of
ringed spaces, including their regular-function maps. The invariant inclusion
remains an equalizer after pushforward to any target space.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- Changing only the continuous map's equality does not change a presheaf morphism. -/
theorem pushforwardEq_comp_heq {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (h : f = g) (F : X.Presheaf CommRingCat.{u}) {G : Y.Presheaf CommRingCat.{u}}
    (a : G ⟶ (TopCat.Presheaf.pushforward _ f).obj F) :
    HEq (a ≫ (TopCat.Presheaf.pushforwardEq h F).hom) a := by
  subst h
  apply heq_of_eq
  simp only [TopCat.Presheaf.pushforwardEq, TopologicalSpace.Opens.mapIso_refl,
    Iso.refl_symm, NatIso.op_refl, isoWhiskerRight_refl, Iso.refl_hom]
  exact Category.comp_id a

/-- The invariant orbit projection coequalizes the actual ringed relation maps. -/
theorem toRingedSpace_condition :
    p.left.toShHom ≫ toRingedSpace e = q.left.toShHom ≫ toRingedSpace e := by
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  apply PresheafedSpace.hext _ _ (relation_quotientMap e)
  have h := congrArg (fun k ↦ k.hom) (invariantInclusion_condition e)
  change (invariantInclusion e).hom ≫
      (TopCat.Presheaf.pushforward _ (quotientMap e)).map p.left.toPshHom.c =
    (invariantInclusion e).hom ≫
      (TopCat.Presheaf.pushforward _ (quotientMap e)).map q.left.toPshHom.c ≫
        (TopCat.Presheaf.pushforwardEq (relation_quotientMap e).symm
          A.left.presheaf).hom at h
  rw [← Category.assoc] at h
  exact (heq_of_eq h).trans
    (pushforwardEq_comp_heq (relation_quotientMap e).symm A.left.presheaf
      ((invariantInclusion e).hom ≫
        (TopCat.Presheaf.pushforward _ (quotientMap e)).map q.left.toPshHom.c))

/-- The actual orbit ringed space, with its quotient projection, is a cofork. -/
def ringedCofork : Cofork p.left.toShHom q.left.toShHom :=
  Cofork.ofπ (toRingedSpace e) (toRingedSpace_condition e)

/-- The invariant inclusion is also a limiting fork of underlying presheaves. -/
def invariantPresheafIsLimit : IsLimit
    (Fork.ofι (invariantInclusion e).hom
      (congrArg (fun k ↦ k.hom) (invariantInclusion_condition e))) :=
  isLimitForkMapOfIsLimit (TopCat.Sheaf.forget _ _) (equalizer.condition _ _)
    (equalizerIsEqualizer (firstRestriction e) (secondRestriction e))

/-- Pushing invariant functions forward preserves their equalizer description. -/
def pushInvariantIsLimit {T : TopCat.{u}} (d : space e ⟶ T) : IsLimit
    (Fork.ofι (f := (TopCat.Presheaf.pushforward _ d).map (firstRestriction e).hom)
      (g := (TopCat.Presheaf.pushforward _ d).map (secondRestriction e).hom)
      ((TopCat.Presheaf.pushforward _ d).map (invariantInclusion e).hom)
      (by rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg ((TopCat.Presheaf.pushforward _ d).map)
            (congrArg (fun k ↦ k.hom) (invariantInclusion_condition e)))) :=
  by
    let _ : PreservesLimits (TopCat.Presheaf.pushforward CommRingCat.{u} d) :=
      inferInstanceAs (PreservesLimits ((whiskeringLeft _ _ _).obj
        (TopologicalSpace.Opens.map d).op))
    exact isLimitForkMapOfIsLimit (TopCat.Presheaf.pushforward _ d) _
      (invariantPresheafIsLimit e)

end FLT.Mazur.RelativeRelationOrbit
