/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleEpimorphisms
public import FLT.Mazur.AffineQuasiCoherentBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Faithfully flat reflection on affine module sheaves

The canonical affine section comparison is natural in the module. Faithfully
flat scalar extension therefore reflects epimorphisms of quasi-coherent sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.AffineFaithfullyFlatEpimorphisms
open AffineModuleGlobalSections AffineQuasiCoherentBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Faithfully flat extension of scalars reflects surjectivity of module maps. -/
lemma surjective_of_extendScalars {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : φ.hom.FaithfullyFlat) {M N : ModuleCat R} (a : M ⟶ N)
    (ha : Function.Surjective ((ModuleCat.extendScalars φ.hom).map a)) :
    Function.Surjective a := by
  let : Algebra R S := φ.hom.toAlgebra
  let : Module.FaithfullyFlat R S := hφ
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S a.hom).mp ha

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)

/-- Naturality of the actual affine pullback section comparison. -/
@[reassoc]
lemma sectionsIso_naturality {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) :
    (ModuleCat.extendScalars f.appTop.hom).map ((sections Y).map a) ≫
      (sectionsIso f N).hom =
    (sectionsIso f M).hom ≫ (sections X).map ((pullback f).map a) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (sectionsIso f N).hom
    ((ModuleCat.extendScalars f.appTop.hom).map ((sections Y).map a)
      ((1 : Γ(X, ⊤)) ⊗ₜ[Γ(Y, ⊤),f.appTop.hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul, sectionsIso_tmul, one_smul]
  change _ = ((pullback f).map a).app ⊤
    ((sectionsIso f M).hom ((1 : Γ(X, ⊤)) ⊗ₜ[Γ(Y, ⊤),f.appTop.hom] m))
  rw [sectionsIso_tmul, one_smul]
  exact congrArg (fun k ↦ k.app ⊤ m) ((pullbackPushforwardAdjunction f).unit.naturality a)

/-- Faithfully flat affine pullback reflects epimorphisms of quasi-coherent sheaves. -/
theorem epi_of_pullback [Flat f] [Surjective f] {M N : Y.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    [Epi ((pullback f).map a)] : Epi a := by
  have := isQuasicoherent_pullback f M
  have := isQuasicoherent_pullback f N
  have hs := AffineModuleEpimorphisms.surjective_of_epi ((pullback f).map a)
  have he : Function.Surjective
      ((ModuleCat.extendScalars f.appTop.hom).map ((sections Y).map a)) := by
    intro n
    obtain ⟨m, hm⟩ := hs ((sectionsIso f N).hom n)
    obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso (sectionsIso f M).hom).surjective m
    refine ⟨t, (ConcreteCategory.bijective_of_isIso (sectionsIso f N).hom).injective ?_⟩
    exact (congrArg (fun k ↦ k t) (sectionsIso_naturality f a)).trans hm
  apply AffineModuleEpimorphisms.epi_of_surjective a
  exact surjective_of_extendScalars f.appTop
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩)
    ((sections Y).map a) he

/-- Epimorphicity is equivalent before and after faithfully flat affine pullback. -/
theorem epi_pullback_iff [Flat f] [Surjective f] {M N : Y.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N) :
    Epi ((pullback f).map a) ↔ Epi a :=
  ⟨fun _ ↦ epi_of_pullback f a, fun _ ↦ inferInstance⟩

end FLT.Mazur.AffineFaithfullyFlatEpimorphisms
