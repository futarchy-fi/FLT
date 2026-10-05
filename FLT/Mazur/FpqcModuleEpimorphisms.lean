/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackEpiReflection
public import FLT.Mazur.AffineFpqcRefinement

/-!
# Fpqc reflection of module epimorphisms

Affine refinement on each target chart removes the affineness assumption on
the faithfully flat morphism. The result concerns the actual sheaf pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
namespace FLT.Mazur.FpqcModuleEpimorphisms
open FCurve AffinePullbackEpiReflection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme.{u}}

/-- An epimorphic pullback stays epimorphic after composing with any morphism. -/
lemma epi_pullback_comp (f : X ⟶ Y) (g : Z ⟶ X) {M N : Y.Modules} (a : M ⟶ N)
    [Epi ((pullback f).map a)] : Epi ((pullback (g ≫ f)).map a) := by
  have : Epi (((pullbackComp g f).app M).hom ≫ (pullback (g ≫ f)).map a) := by
    change Epi ((pullbackComp g f).hom.app M ≫ (pullback (g ≫ f)).map a)
    rw [← (pullbackComp g f).hom.naturality a]
    change Epi ((pullback g).map ((pullback f).map a) ≫ (pullbackComp g f).hom.app N)
    infer_instance
  exact epi_of_epi ((pullbackComp g f).app M).hom _

/-- Fpqc pullback reflects epimorphisms of quasi-coherent module sheaves. -/
theorem epi_of_pullback (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f]
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    [Epi ((pullback f).map a)] : Epi a := by
  apply AffineModuleEpimorphisms.epi_of_affineOpen_surjective a
  intro U hU
  let : IsAffine U.toScheme := hU
  have : Surjective (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
      (inferInstance : Surjective f)
  obtain ⟨Z, hZ, k, hkf, hks⟩ := exists_affine_fpqc_refinement (f ∣_ U)
  let := hZ
  let := hkf
  let := hks
  have := epi_pullback_restrict f U a
  have := epi_pullback_comp (f ∣_ U) k ((restrictFunctor U.ι).map a)
  have := AffineFaithfullyFlatEpimorphisms.epi_of_pullback (k ≫ f ∣_ U)
    ((restrictFunctor U.ι).map a)
  have hs := AffineModuleEpimorphisms.surjective_of_epi ((restrictFunctor U.ι).map a)
  change Function.Surjective (a.app (U.ι ''ᵁ ⊤)) at hs
  rwa [U.ι_image_top] at hs

/-- Fpqc base change preserves and reflects quasi-coherent epimorphisms. -/
theorem epi_pullback_iff (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f]
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N) :
    Epi ((pullback f).map a) ↔ Epi a :=
  ⟨fun _ ↦ epi_of_pullback f a, fun _ ↦ inferInstance⟩

end FLT.Mazur.FpqcModuleEpimorphisms
