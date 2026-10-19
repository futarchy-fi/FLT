/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicIntegerSourceLocallyRinged
public import FLT.Mazur.PresheafedOpenFactorSections

/-!
# Original section coordinates of the characteristic source projection

The locally ringed source pullback is the original invariant inclusion,
transported to top sections of the source open. This identifies the geometric
section comparison with the concrete equalizer section ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] integerSourceToInvariantOpen invariantLocallyRingedProjection
variable (n : ℕ) [NeZero n] (b : Bool)

/-- The full source section comparison is the original invariant inclusion with top transport. -/
theorem integerSourceInvariantSectionMap_inclusion :
    integerSourceInvariantSectionMap n b =
      (invariantInclusion n).hom.app (op (integerOpen n (chartInteger (!b)))) ≫
        (integerSourceOpen n b).topIso.inv := by
  let W := integerOpen n (chartInteger (!b))
  let f := (integerSourceToInvariantOpen n b).toHom
  have hf := congrArg (fun k => k.toHom) (integerSourceToInvariantOpen_comp n b)
  change f ≫ (invariantLocallyRingedSpace n).toPresheafedSpace.ofRestrict
    W.isOpenEmbedding =
      (integerSourceOpen n b).ι.toLRSHom.toHom ≫
        (invariantLocallyRingedProjection n).toHom at hf
  have hp := congrArg (fun k => k.hom) (invariantLocallyRingedProjection_toShHom n)
  change (invariantLocallyRingedProjection n).toHom = (toRingedSpace n).hom at hp
  erw [hp] at hf
  have he := PresheafedOpenFactorSections.factor_top_of_comp
    (X := (integerSourceOpen n b).toScheme.toPresheafedSpace)
    (Y := (invariantLocallyRingedSpace n).toPresheafedSpace) W f
    ((integerSourceOpen n b).ι.toLRSHom.toHom ≫ (toRingedSpace n).hom) hf
    (by intro x _; exact x.property)
  rw [PresheafedSpace.comp_c_app] at he
  change integerSourceInvariantSectionMap n b =
    ((invariantInclusion n).hom.app (op W) ≫
      (integerSourceOpen n b).ι.app (integerSourceOpen n b)) ≫
        (integerSourceOpen n b).toScheme.presheaf.map (homOfLE _).op at he
  rw [Category.assoc, Scheme.Opens.ι_app,
    Scheme.Opens.toScheme_presheaf_map, ← Functor.map_comp] at he
  exact he

/-- Actual sections are determined by their full original source pullback. -/
theorem integerSourceInvariantSectionMap_injective :
    Function.Injective (integerSourceInvariantSectionMap n b) := by
  intro s t h
  apply invariantSection_ext n (integerOpen n (chartInteger (!b)))
  rw [integerSourceInvariantSectionMap_inclusion] at h
  exact (integerSourceOpen n b).topIso.symm.commRingCatIsoToRingEquiv.injective h

end FLT.Mazur.CyclicCharacteristicOrbit
