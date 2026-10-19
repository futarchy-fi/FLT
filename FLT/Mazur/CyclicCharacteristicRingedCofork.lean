/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitCoequalizer

/-!
# The invariant ringed orbit cofork

The orbit projection identifies the two original relation morphisms as maps of
ringed spaces, including their regular-function maps. The invariant inclusion
remains an equalizer after pushforward to any target space.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- Changing only the continuous map's equality does not change a presheaf morphism. -/
theorem pushforwardEq_comp_heq {X Y : TopCat} {f g : X ⟶ Y}
    (h : f = g) (F : X.Presheaf CommRingCat) {G : Y.Presheaf CommRingCat}
    (a : G ⟶ (TopCat.Presheaf.pushforward _ f).obj F) :
    HEq (a ≫ (TopCat.Presheaf.pushforwardEq h F).hom) a := by
  subst h
  apply heq_of_eq
  simp only [TopCat.Presheaf.pushforwardEq, TopologicalSpace.Opens.mapIso_refl,
    Iso.refl_symm, NatIso.op_refl, isoWhiskerRight_refl, Iso.refl_hom]
  exact Category.comp_id a

/-- The invariant orbit projection coequalizes the actual ringed relation maps. -/
theorem toRingedSpace_condition :
    (src).toShHom ≫ toRingedSpace n = (tgt).toShHom ≫ toRingedSpace n := by
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  apply PresheafedSpace.hext _ _ (relation_quotientMap n)
  have h := congrArg (fun k ↦ k.hom) (invariantInclusion_condition n)
  change (invariantInclusion n).hom ≫
      (TopCat.Presheaf.pushforward _ (quotientMap n)).map (src).toPshHom.c =
    (invariantInclusion n).hom ≫
      (TopCat.Presheaf.pushforward _ (quotientMap n)).map (tgt).toPshHom.c ≫
        (TopCat.Presheaf.pushforwardEq (relation_quotientMap n).symm
          (A).presheaf).hom at h
  rw [← Category.assoc] at h
  exact (heq_of_eq h).trans
    (pushforwardEq_comp_heq (relation_quotientMap n).symm (A).presheaf
      ((invariantInclusion n).hom ≫
        (TopCat.Presheaf.pushforward _ (quotientMap n)).map (tgt).toPshHom.c))

/-- The actual orbit ringed space, with its quotient projection, is a cofork. -/
def ringedCofork : Cofork (src).toShHom (tgt).toShHom :=
  Cofork.ofπ (toRingedSpace n) (toRingedSpace_condition n)

/-- The invariant inclusion is also a limiting fork of underlying presheaves. -/
def invariantPresheafIsLimit : IsLimit
    (Fork.ofι (invariantInclusion n).hom
      (congrArg (fun k ↦ k.hom) (invariantInclusion_condition n))) :=
  isLimitForkMapOfIsLimit (TopCat.Sheaf.forget _ _) (equalizer.condition _ _)
    (equalizerIsEqualizer (firstRestriction n) (secondRestriction n))

/-- Pushing invariant functions forward preserves their equalizer description. -/
def pushInvariantIsLimit {T : TopCat} (d : space n ⟶ T) : IsLimit
    (Fork.ofι (f := (TopCat.Presheaf.pushforward _ d).map (firstRestriction n).hom)
      (g := (TopCat.Presheaf.pushforward _ d).map (secondRestriction n).hom)
      ((TopCat.Presheaf.pushforward _ d).map (invariantInclusion n).hom)
      (by rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg ((TopCat.Presheaf.pushforward _ d).map)
            (congrArg (fun k ↦ k.hom) (invariantInclusion_condition n)))) :=
  by
    let _ : PreservesLimits (TopCat.Presheaf.pushforward CommRingCat d) :=
      inferInstanceAs (PreservesLimits ((whiskeringLeft _ _ _).obj
        (TopologicalSpace.Opens.map d).op))
    exact isLimitForkMapOfIsLimit (TopCat.Presheaf.pushforward _ d) _
      (invariantPresheafIsLimit n)

end FLT.Mazur.CyclicCharacteristicOrbit
