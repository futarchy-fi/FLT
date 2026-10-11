/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFaithfullyFlatEpimorphisms
public import FLT.Mazur.CoherentSubquotient

/-!
# Faithfully flat reflection of affine module monomorphisms

Injectivity descends by faithful flatness on global sections. The tilde counit
then transfers it to the actual quasi-coherent module sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineFaithfullyFlatMonomorphisms
open AffineModuleGlobalSections AffineQuasiCoherentBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Faithful flatness reflects injectivity of the actual scalar-extension map. -/
lemma injective_of_extendScalars {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : φ.hom.FaithfullyFlat) {M N : ModuleCat R} (a : M ⟶ N)
    (ha : Function.Injective ((ModuleCat.extendScalars φ.hom).map a)) :
    Function.Injective a := by
  let : Algebra R S := φ.hom.toAlgebra
  let : Module.FaithfullyFlat R S := hφ
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective R S a.hom).mp ha

/-- Injectivity of spectrum sections gives a monomorphism of the reconstructed sheaves. -/
lemma mono_of_injective {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    (ha : Function.Injective (a.app ⊤)) : Mono a := by
  let _ : Mono (moduleSpecΓFunctor.map a) := (ModuleCat.mono_iff_injective _).mpr ha
  have he : a = inv M.fromTildeΓ ≫
      (tilde.functor R).map (moduleSpecΓFunctor.map a) ≫ N.fromTildeΓ := by
    apply (cancel_epi M.fromTildeΓ).mp
    rw [IsIso.hom_inv_id_assoc]
    exact (fromTildeΓNatTrans.naturality a).symm
  rw [he]
  infer_instance

/-- Affine faithfully flat pullback detects monicity of quasi-coherent module maps. -/
theorem mono_of_pullback {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : φ.hom.FaithfullyFlat) {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    [Mono ((pullback (Spec.map φ)).map a)] : Mono a := by
  let f := Spec.map φ
  let _ : Mono ((pullback f).map a).val :=
    inferInstanceAs (Mono ((SheafOfModules.forget _).map ((pullback f).map a)))
  have hi := PresheafOfModules.injective_of_mono
    ((pullback f).map a).val (op ⊤)
  have he : Function.Injective
      ((ModuleCat.extendScalars f.appTop.hom).map ((sections (Spec R)).map a)) := by
    intro s t hst
    apply (ConcreteCategory.bijective_of_isIso (sectionsIso f M).hom).injective
    apply hi
    exact (congrArg (fun k ↦ k s)
      (AffineFaithfullyFlatEpimorphisms.sectionsIso_naturality f a)).symm.trans
      ((congrArg (sectionsIso f N).hom hst).trans
        (congrArg (fun k ↦ k t)
          (AffineFaithfullyFlatEpimorphisms.sectionsIso_naturality f a)))
  apply mono_of_injective a
  let _ : Flat f := (flat_and_surjective_SpecMap_iff φ).mpr hφ |>.1
  let _ : Surjective f := (flat_and_surjective_SpecMap_iff φ).mpr hφ |>.2
  exact injective_of_extendScalars f.appTop
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp
      ⟨inferInstance, inferInstance⟩) ((sections (Spec R)).map a) he

end FLT.Mazur.AffineFaithfullyFlatMonomorphisms
