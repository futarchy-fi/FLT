/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionSpectrumCover
public import FLT.Mazur.SchemeFlatTargetFamilyReflection
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Descent from completion for an arbitrary scheme over the original affine input

The source of the morphism need not be affine. Its actual base changes to the
parameter completion and complementary localization jointly detect flatness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeAdicCompletionFlatDescent
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (t : R)

/-- The unchanged scheme projection is flat if both of its concrete base changes are flat. -/
theorem flat_of_completion_and_away
    [Flat (pullback.snd f (Spec.map (CommRingCat.ofHom
      (algebraMap R (AdicCompletion (Ideal.span {t}) R)))))]
    [Flat (pullback.snd f (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away t)))))] : Flat f := by
  let c := Spec.map (CommRingCat.ofHom
    (algebraMap R (AdicCompletion (Ideal.span {t}) R)))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))
  let _ : Flat c := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  exact SchemeFlatTargetFamilyReflection.flat_of_pair f c g
    (AdicCompletionSpectrumCover.principal_cover t)

end FLT.Mazur.SchemeAdicCompletionFlatDescent
