/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFaithfullyFlatEpimorphisms
public import FLT.Mazur.ModulePullbackRestrictionPasting
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Reflection of epimorphisms under affine faithfully flat pullback

Reflection on affine schemes glues over the target's affine open cover. The
ambient target need not be affine, quasi-compact, separated or reduced.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u v
namespace FLT.Mazur.AffinePullbackEpiReflection
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}}

/-- Epimorphicity of sheaf morphisms is local on any open cover. -/
lemma epi_of_restrict_cover {M N : Y.Modules} (a : M ⟶ N)
    {ι : Type v} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (ha : ∀ i, Epi ((restrictFunctor (U i).ι).map a)) : Epi a where
  left_cancellation b c h := by
    apply ModuleSheafMorphismGluing.hom_ext_restrict U hU
    intro i
    have := ha i
    apply (cancel_epi ((restrictFunctor (U i).ι).map a)).mp
    simpa only [Functor.map_comp] using congrArg (restrictFunctor (U i).ι).map h

/-- The actual restriction comparison intertwines pullback morphisms. -/
@[reassoc]
lemma openIso_naturality (f : X ⟶ Y) (U : Y.Opens) {M N : Y.Modules} (a : M ⟶ N) :
    (restrictFunctor (f ⁻¹ᵁ U).ι).map ((pullback f).map a) ≫
      (modulePullbackOpenIso f U N).hom =
    (modulePullbackOpenIso f U M).hom ≫ (pullback (f ∣_ U)).map
      ((restrictFunctor U.ι).map a) :=
  (modulePullbackRestrictNatIso f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι
    (morphismRestrict_ι f U).symm).hom.naturality a

/-- An epimorphic pullback remains epimorphic after restricting its base. -/
lemma epi_pullback_restrict (f : X ⟶ Y) (U : Y.Opens) {M N : Y.Modules} (a : M ⟶ N)
    [Epi ((pullback f).map a)] :
    Epi ((pullback (f ∣_ U)).map ((restrictFunctor U.ι).map a)) := by
  have : Epi ((modulePullbackOpenIso f U M).hom ≫
      (pullback (f ∣_ U)).map ((restrictFunctor U.ι).map a)) := by
    rw [← openIso_naturality]
    infer_instance
  exact epi_of_epi (modulePullbackOpenIso f U M).hom _

/-- Affine faithfully flat pullback reflects epimorphisms of quasi-coherent sheaves. -/
theorem epi_of_pullback (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    [Epi ((pullback f).map a)] : Epi a := by
  apply AffineModuleEpimorphisms.epi_of_affineOpen_surjective a
  intro U hU
  let : IsAffine U.toScheme := hU
  let : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  have : Surjective (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
      (inferInstance : Surjective f)
  have := epi_pullback_restrict f U a
  have := AffineFaithfullyFlatEpimorphisms.epi_of_pullback (f ∣_ U)
    ((restrictFunctor U.ι).map a)
  have hs := AffineModuleEpimorphisms.surjective_of_epi ((restrictFunctor U.ι).map a)
  change Function.Surjective (a.app (U.ι ''ᵁ ⊤)) at hs
  rwa [U.ι_image_top] at hs

/-- Epimorphicity is unchanged by affine faithfully flat pullback. -/
theorem epi_pullback_iff (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N) :
    Epi ((pullback f).map a) ↔ Epi a :=
  ⟨fun _ ↦ epi_of_pullback f a, fun _ ↦ inferInstance⟩

end FLT.Mazur.AffinePullbackEpiReflection
