/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleGlobalSections
public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Epimorphisms and affine module sections

For quasi-coherent sheaves on an affine scheme, epimorphisms are exactly
surjections on global sections. Affine-open surjectivity detects epimorphisms
on any scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineModuleEpimorphisms
open AffineModuleGlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}}

/-- Maps from an affine quasi-coherent sheaf are detected on global sections. -/
lemma hom_ext_sections [IsAffine X] {M N : X.Modules} [M.IsQuasicoherent]
    (a b : M ⟶ N) (h : (sections X).map a = (sections X).map b) : a = b := by
  apply (cancel_epi ((affineAdjunction X).counit.app M)).mp
  exact ((affineAdjunction X).counit.naturality a).symm.trans
    ((congrArg (fun k ↦ (affineTilde X).map k ≫ (affineAdjunction X).counit.app N) h).trans
      ((affineAdjunction X).counit.naturality b))

/-- Surjective global sections imply an epimorphism when the target is quasi-coherent. -/
lemma epi_of_surjective [IsAffine X] {M N : X.Modules} [N.IsQuasicoherent]
    (a : M ⟶ N) (ha : Function.Surjective (a.app ⊤)) : Epi a where
  left_cancellation {Q} b c h := by
    apply hom_ext_sections
    ext n
    obtain ⟨m, rfl⟩ := ha n
    exact congrArg (fun k ↦ k.app ⊤ m) h

/-- An epimorphism of affine quasi-coherent sheaves is surjective on global sections. -/
lemma surjective_of_epi [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N) [Epi a] :
    Function.Surjective (a.app ⊤) := by
  have he : (affineTilde X).map ((sections X).map a) =
      (affineAdjunction X).counit.app M ≫ a ≫ inv ((affineAdjunction X).counit.app N) := by
    have hn := (affineAdjunction X).counit.naturality a
    change (affineTilde X).map ((sections X).map a) ≫ _ = _ ≫ a at hn
    rw [← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have : Epi ((affineTilde X).map ((sections X).map a)) := by
    rw [he]
    infer_instance
  have : Epi ((sections X).map a) := (affineTilde X).epi_of_epi_map inferInstance
  exact (ModuleCat.epi_iff_surjective _).mp this

/-- The affine section criterion for quasi-coherent sheaves. -/
theorem epi_iff_surjective [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N) :
    Epi a ↔ Function.Surjective (a.app ⊤) :=
  ⟨fun _ ↦ surjective_of_epi a, epi_of_surjective a⟩

/-- Epimorphisms between quasi-coherent sheaves are surjective on every affine open. -/
lemma affineOpen_surjective {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) [Epi a] (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (a.app U) := by
  let : IsAffine U.toScheme := hU
  have h := surjective_of_epi ((restrictFunctor U.ι).map a)
  change Function.Surjective (a.app (U.ι ''ᵁ ⊤)) at h
  rwa [U.ι_image_top] at h

/-- Surjectivity on every affine open detects epimorphisms of arbitrary module sheaves. -/
theorem epi_of_affineOpen_surjective {M N : X.Modules} (a : M ⟶ N)
    (ha : ∀ (U : X.Opens), IsAffineOpen U → Function.Surjective (a.app U)) : Epi a where
  left_cancellation {Q} b c h := by
    apply Scheme.Modules.hom_ext
    intro V
    ext s
    apply TopCat.Presheaf.IsSheaf.section_ext
      Q.isSheaf
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    refine ⟨U, hUV, hxU, ?_⟩
    change Q.val.map (homOfLE (show U ≤ V from hUV)).op (b.val.app (op V) s) =
      Q.val.map (homOfLE (show U ≤ V from hUV)).op (c.val.app (op V) s)
    rw [← PresheafOfModules.naturality_apply b.val,
      ← PresheafOfModules.naturality_apply c.val]
    obtain ⟨m, hm⟩ := ha U hU (N.presheaf.map (homOfLE hUV).op s)
    change b.app U (N.presheaf.map (homOfLE (show U ≤ V from hUV)).op s) =
      c.app U (N.presheaf.map (homOfLE (show U ≤ V from hUV)).op s)
    exact (congrArg (b.app U) hm.symm).trans
      ((congrArg (fun k ↦ k.app U m) h).trans (congrArg (c.app U) hm))

end FLT.Mazur.AffineModuleEpimorphisms
