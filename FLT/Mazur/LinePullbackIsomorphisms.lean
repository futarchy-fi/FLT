/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LinePullbackAdjunction

/-!
# Descent of actual isomorphisms between pulled base lines

The inverse maps descend along the same adjunction. Faithfulness proves
the inverse laws on the original base, retaining the given total-space map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.LinePullbackAdjunction
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsIso (StructureDirectImage.unitMap f)]

/-- The descended adjunction morphism pulls back to the specified original map. -/
lemma map_homEquiv_symm (M : S.Modules) {N : S.Modules} (hN : LocallyFreeRankOne N)
    (a : (pullback f).obj M ⟶ (pullback f).obj N) :
    (pullback f).map ((homEquiv f M hN).symm a) = a := by
  rw [← homEquiv_apply f M hN, Equiv.apply_symm_apply]

/-- The given total-space line isomorphism descends to an actual base-line isomorphism. -/
def descendIso {M N : S.Modules} (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N)
    (e : (pullback f).obj M ≅ (pullback f).obj N) : M ≅ N where
  hom := (homEquiv f M hN).symm e.hom
  inv := (homEquiv f N hM).symm e.inv
  hom_inv_id := by
    apply map_injective f M hM
    dsimp only
    rw [Functor.map_comp, map_homEquiv_symm, map_homEquiv_symm,
      CategoryTheory.Functor.map_id, e.hom_inv_id]
  inv_hom_id := by
    apply map_injective f N hN
    dsimp only
    rw [Functor.map_comp, map_homEquiv_symm, map_homEquiv_symm,
      CategoryTheory.Functor.map_id, e.inv_hom_id]

/-- Descent recovers the full specified pullback isomorphism. -/
lemma mapIso_descendIso {M N : S.Modules} (hM : LocallyFreeRankOne M)
    (hN : LocallyFreeRankOne N) (e : (pullback f).obj M ≅ (pullback f).obj N) :
    (pullback f).mapIso (descendIso f hM hN e) = e := by
  apply Iso.ext
  exact map_homEquiv_symm f M hN e.hom

/-- Descending an original base-line isomorphism returns that same isomorphism. -/
lemma descendIso_mapIso {M N : S.Modules} (hM : LocallyFreeRankOne M)
    (hN : LocallyFreeRankOne N) (e : M ≅ N) :
    descendIso f hM hN ((pullback f).mapIso e) = e := by
  apply Iso.ext
  apply map_injective f M hN
  exact congrArg Iso.hom (mapIso_descendIso f hM hN ((pullback f).mapIso e))

/-- Base-line isomorphisms correspond exactly to their actual total-space pullbacks. -/
def isoEquiv {M N : S.Modules} (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N) :
    (M ≅ N) ≃ ((pullback f).obj M ≅ (pullback f).obj N) where
  toFun := (pullback f).mapIso
  invFun := descendIso f hM hN
  left_inv := descendIso_mapIso f hM hN
  right_inv := mapIso_descendIso f hM hN

end FLT.Mazur.FCurve.LinePullbackAdjunction
