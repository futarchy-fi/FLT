/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionSpectrumCover
public import FLT.Mazur.SchemeFlatFamilyReflection
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Flatness from the actual completion and parameter localization

A Noetherian target algebra is flat over the original source if its completion
and its parameter localization are flat over that source. The two flat maps
jointly cover the target spectrum, so no open-flat-locus theorem is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AdicCompletionFlatDescent
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing B]
  (f : A →+* B) (t : B)

/-- Completion and parameter inversion detect flatness of the unchanged ring map. -/
theorem flat_of_completion_and_away
    (hc : ((algebraMap B (AdicCompletion (Ideal.span {t}) B)).comp f).Flat)
    (hg : ((algebraMap B (Localization.Away t)).comp f).Flat) : f.Flat := by
  let c := Spec.map (CommRingCat.ofHom
    (algebraMap B (AdicCompletion (Ideal.span {t}) B)))
  let g := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t)))
  let a := Spec.map (CommRingCat.ofHom f)
  let _ : Flat c := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : Flat (c ≫ a) := by
    change Flat (Spec.map _ ≫ Spec.map _)
    rw [← Spec.map_comp]
    exact Flat.SpecMap_iff.mpr hc
  let _ : Flat (g ≫ a) := by
    change Flat (Spec.map _ ≫ Spec.map _)
    rw [← Spec.map_comp]
    exact Flat.SpecMap_iff.mpr hg
  apply (Flat.SpecMap_iff (f := CommRingCat.ofHom f)).mp
  apply Flat.of_stalkMap
  intro x
  obtain hc | hg := AdicCompletionSpectrumCover.principal_cover t x
  · obtain ⟨y, hy⟩ := hc
    change c y = x at hy
    subst x
    exact SchemeFlatFamilyReflection.stalkMap_flat_of_comp a c y
  · obtain ⟨y, hy⟩ := hg
    change g y = x at hy
    subst x
    exact SchemeFlatFamilyReflection.stalkMap_flat_of_comp a g y

/-- The original affine projection is flat under the same two concrete ring checks. -/
theorem spec_flat_of_completion_and_away
    (hc : ((algebraMap B (AdicCompletion (Ideal.span {t}) B)).comp f).Flat)
    (hg : ((algebraMap B (Localization.Away t)).comp f).Flat) :
    Flat (Spec.map (CommRingCat.ofHom f)) :=
  Flat.SpecMap_iff.mpr (flat_of_completion_and_away f t hc hg)

end FLT.Mazur.AdicCompletionFlatDescent
