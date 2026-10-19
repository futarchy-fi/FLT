/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSourceLocallyRinged
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
attribute [local irreducible] affineSourceToInvariantOpen invariantLocallyRingedProjection
variable (n : ℕ) [NeZero n] (b : Bool)
  (j : (invariantAffineCover n (!b)).I₀)

/-- The full source section comparison is the original invariant inclusion with top transport. -/
theorem affineSourceInvariantSectionMap_inclusion :
    affineSourceInvariantSectionMap n b j =
      (invariantInclusion n).hom.app (op (affineOrbitOpen n ⟨!b, j⟩)) ≫
        (affineSourceOpen n b j).topIso.inv := by
  let W := affineOrbitOpen n ⟨!b, j⟩
  let f := (affineSourceToInvariantOpen n b j).toHom
  have hf := congrArg (fun k => k.toHom) (affineSourceToInvariantOpen_comp n b j)
  change f ≫ (invariantLocallyRingedSpace n).toPresheafedSpace.ofRestrict
    W.isOpenEmbedding =
      (affineSourceOpen n b j).ι.toLRSHom.toHom ≫
        (invariantLocallyRingedProjection n).toHom at hf
  have hp := congrArg (fun k => k.hom) (invariantLocallyRingedProjection_toShHom n)
  change (invariantLocallyRingedProjection n).toHom = (toRingedSpace n).hom at hp
  erw [hp] at hf
  have he := PresheafedOpenFactorSections.factor_top_of_comp
    (X := (affineSourceOpen n b j).toScheme.toPresheafedSpace)
    (Y := (invariantLocallyRingedSpace n).toPresheafedSpace) W f
    ((affineSourceOpen n b j).ι.toLRSHom.toHom ≫ (toRingedSpace n).hom) hf
    (by intro x _; exact x.property)
  rw [PresheafedSpace.comp_c_app] at he
  change affineSourceInvariantSectionMap n b j =
    ((invariantInclusion n).hom.app (op W) ≫
      (affineSourceOpen n b j).ι.app (affineSourceOpen n b j)) ≫
        (affineSourceOpen n b j).toScheme.presheaf.map (homOfLE _).op at he
  rw [Category.assoc, Scheme.Opens.ι_app,
    Scheme.Opens.toScheme_presheaf_map, ← Functor.map_comp] at he
  exact he

/-- Actual sections are determined by their full original source pullback. -/
theorem affineSourceInvariantSectionMap_injective :
    Function.Injective (affineSourceInvariantSectionMap n b j) := by
  intro s t h
  apply invariantSection_ext n (affineOrbitOpen n ⟨!b, j⟩)
  rw [affineSourceInvariantSectionMap_inclusion] at h
  exact (affineSourceOpen n b j).topIso.symm.commRingCatIsoToRingEquiv.injective h

end FLT.Mazur.CyclicCharacteristicOrbit
