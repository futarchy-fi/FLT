/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.TensorProduct.Finite
public import FLT.Mazur.CoherentIdealIntersection
public import FLT.Mazur.ModuleSheafTensorAffineOpen
public import FLT.Mazur.AffineIdealPowerExtension

/-!
# The actual ideal-action image

The ideal multiple is the image of scalar multiplication from the sheaf tensor.
Its affine coordinates are obtained from the canonical tensor comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CoherentIdealIntersection

universe u

namespace FLT.Mazur.GlobalIdealPower

variable {X : Scheme.{u}}

/-- Scalar multiplication by sections of the actual ideal module. -/
def scalarPairing (I : X.IdealSheafData) (F : X.Modules) :
    ModuleSheafTensor.Bilinear (idealModule I) F F where
  app U := (LinearMap.lsmul Γ(X, U) Γ(F, U)).comp
    (show Γ(idealModule I, U) →ₗ[Γ(X, U)] Γ(X, U) from
      ((idealModuleι I).val.app (op U)).hom)
  naturality {U V} i s t := by
    change (show Γ(X, U) from (idealModuleι I).app U
      ((idealModule I).presheaf.map i.op s)) •
      F.presheaf.map i.op t = F.presheaf.map i.op ((show Γ(X, V) from (idealModuleι I).app V s) • t)
    rw [F.map_smul]
    congr 1
    exact congr($((idealModuleι I).val.naturality i.op) s)

/-- The canonical scalar-action morphism out of the sheaf tensor. -/
def scalarAction (I : X.IdealSheafData) (F : X.Modules) :
    ModuleSheafTensor.tensor (idealModule I) F ⟶ F :=
  ModuleSheafTensor.lift (scalarPairing I F)

@[simp]
lemma scalarAction_pure (I : X.IdealSheafData) (F : X.Modules) (U : X.Opens)
    (s : Γ(idealModule I, U)) (t : Γ(F, U)) :
    (scalarAction I F).app U (ModuleSheafTensor.pure (idealModule I) F U s t) =
      (show Γ(X, U) from (idealModuleι I).app U s) • t := ModuleSheafTensor.lift_pure _ _ _ _

/-- The ideal multiple, defined as the image of the actual scalar-action map. -/
def multiple (I : X.IdealSheafData) (F : X.Modules) : X.Modules :=
  Abelian.image (scalarAction I F)

/-- Its inclusion in the original module sheaf. -/
def inclusion (I : X.IdealSheafData) (F : X.Modules) : multiple I F ⟶ F :=
  Abelian.image.ι (scalarAction I F)

instance inclusion_mono (I : X.IdealSheafData) (F : X.Modules) :
    Mono (inclusion I F) := inferInstanceAs (Mono (Abelian.image.ι _))

/-- The scalar-action map with codomain its image. -/
def onto (I : X.IdealSheafData) (F : X.Modules) :
    ModuleSheafTensor.tensor (idealModule I) F ⟶ multiple I F :=
  Abelian.factorThruImage (scalarAction I F)

instance onto_epi (I : X.IdealSheafData) (F : X.Modules) : Epi (onto I F) :=
  inferInstanceAs (Epi (Abelian.factorThruImage _))

@[reassoc (attr := simp)]
lemma onto_inclusion (I : X.IdealSheafData) (F : X.Modules) :
    onto I F ≫ inclusion I F = scalarAction I F := Abelian.image.fac _

/-- The image of the action of the actual power of the ideal sheaf. -/
abbrev power (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) : X.Modules :=
  multiple (I ^ n) F

/-- Tensor products of coherent sheaves are coherent on a locally Noetherian scheme. -/
theorem tensor_coherent [IsLocallyNoetherian X] (M N : X.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation] :
    (ModuleSheafTensor.tensor M N).IsFinitePresentation := by
  apply coherentPresentation_of_affine_restrict
  intro U
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have := coherentPresentation_restrict U.2.fromSpec M
  have := coherentPresentation_restrict U.2.fromSpec N
  have : Module.Finite Γ(X, U.1) Γ(M.restrict U.2.fromSpec, ⊤) :=
    affineCoherent_finite_sections _
  have : Module.Finite Γ(X, U.1) Γ(N.restrict U.2.fromSpec, ⊤) :=
    affineCoherent_finite_sections _
  have : Module.Finite Γ(X, U.1) (ModuleSheafTensor.affineTensorModule
      (M.restrict U.2.fromSpec) (N.restrict U.2.fromSpec)) :=
    inferInstanceAs (Module.Finite Γ(X, U.1)
      (Γ(M.restrict U.2.fromSpec, ⊤) ⊗[Γ(X, U.1)] Γ(N.restrict U.2.fromSpec, ⊤)))
  let e := ModuleSheafTensor.affineTildeIso (M.restrict U.2.fromSpec)
    (N.restrict U.2.fromSpec) ≪≫ (ModuleSheafTensor.restrictIso M N U.2.fromSpec).symm
  exact (SheafOfModules.isFinitePresentation (Spec Γ(X, U.1)).ringCatSheaf).prop_of_iso e
    (affineTilde_isFinitePresentation_of_finite _)

instance multiple_coherent [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] : (multiple I F).IsFinitePresentation := by
  have := idealModule_coherent I
  have := tensor_coherent (idealModule I) F
  exact coherent_image (scalarAction I F)

/-- The range of the scalar-action map on any affine open is the ideal product. -/
theorem scalarAction_range [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] (V : X.affineOpens) :
    LinearMap.range ((scalarAction I F).val.app (op V.1)).hom =
      I.ideal V • (⊤ : Submodule Γ(X, V.1) Γ(F, V.1)) := by
  have := idealModule_coherent I
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    obtain ⟨t, rfl⟩ := (ModuleSheafTensor.affineSectionsEquiv
      (idealModule I) F V.1 V.2).surjective t
    induction t using TensorProduct.inductionOn with
    | tmul s t =>
      change (scalarAction I F).app V.1
        (ModuleSheafTensor.affineSectionsEquiv (idealModule I) F V.1 V.2 (s ⊗ₜ t)) ∈ _
      rw [ModuleSheafTensor.affineSectionsEquiv_tmul, scalarAction_pure]
      exact Submodule.smul_mem_smul
        (by rw [← idealModuleAffineEquiv_val]; exact (idealModuleAffineEquiv I V s).property)
        (Submodule.mem_top)
    | add s t hs ht => simpa only [map_add] using Submodule.add_mem _ hs ht
  · apply Submodule.smul_le.mpr
    intro r hr t _
    let s := (idealModuleAffineEquiv I V).symm ⟨r, hr⟩
    refine ⟨ModuleSheafTensor.pure (idealModule I) F V.1 s t, ?_⟩
    change (scalarAction I F).app V.1 _ = _
    rw [scalarAction_pure, ← idealModuleAffineEquiv_val]
    simp [s]

/-- An epimorphism between quasi-coherent affine sheaves is surjective on sections. -/
lemma spec_epi_surjective {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) [Epi f] :
    Function.Surjective (f.app ⊤) := by
  have hn : (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f := fromTildeΓNatTrans.naturality f
  have he : (tilde.functor R).map (moduleSpecΓFunctor.map f) =
      M.fromTildeΓ ≫ f ≫ inv N.fromTildeΓ := by
    rw [← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have : Epi ((tilde.functor R).map (moduleSpecΓFunctor.map f)) := by
    rw [he]
    infer_instance
  have : Epi (moduleSpecΓFunctor.map f) :=
    (tilde.functor R).epi_of_epi_map inferInstance
  exact (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map f)).mp this

/-- Coherent epimorphisms are surjective on every affine open. -/
lemma affine_epi_surjective {M N : X.Modules}
    [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) [Epi f]
    (V : X.affineOpens) : Function.Surjective (f.app V.1) := by
  have := coherentPresentation_restrict V.2.fromSpec M
  have := coherentPresentation_restrict V.2.fromSpec N
  have h := spec_epi_surjective ((restrictFunctor V.2.fromSpec).map f)
  change Function.Surjective (f.app (V.2.fromSpec ''ᵁ ⊤)) at h
  have he : V.2.fromSpec ''ᵁ ⊤ = V.1 := by simp
  rw [he] at h
  exact h

/-- Affine sections of the image inclusion are exactly the ideal multiple. -/
theorem inclusion_range [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] (V : X.affineOpens) :
    LinearMap.range ((inclusion I F).val.app (op V.1)).hom =
      I.ideal V • (⊤ : Submodule Γ(X, V.1) Γ(F, V.1)) := by
  have := idealModule_coherent I
  have := tensor_coherent (idealModule I) F
  rw [← scalarAction_range I F V]
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := affine_epi_surjective (onto I F) V s
    exact ⟨t, congr($(onto_inclusion I F).app V.1 t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨(onto I F).app V.1 t, congr($(onto_inclusion I F).app V.1 t)⟩

/-- The affine identification, with the image inclusion as its underlying map. -/
def affineEquiv [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] (V : X.affineOpens) :
    Γ(multiple I F, V.1) ≃ₗ[Γ(X, V.1)]
      ↥(I.ideal V • (⊤ : Submodule Γ(X, V.1) Γ(F, V.1))) :=
  (LinearEquiv.ofInjective (σ₁₂ := RingHom.id Γ(X, V.1)) ((inclusion I F).val.app (op V.1)).hom
    (ModuleSubobjectCoverEquality.app_injective (inclusion I F) V.1)).trans
      (LinearEquiv.ofEq _ _ (inclusion_range I F V))

@[simp]
lemma affineEquiv_val [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] (V : X.affineOpens) (s : Γ(multiple I F, V.1)) :
    (affineEquiv I F V s).val = (inclusion I F).app V.1 s := rfl

/-- The power-source affine coordinates use the ordinary power of the affine ideal. -/
def powerAffineEquiv [IsLocallyNoetherian X] (I : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) [F.IsFinitePresentation] (V : X.affineOpens) :
    Γ(power I n F, V.1) ≃ₗ[Γ(X, V.1)]
      ↥((I.ideal V) ^ n • (⊤ : Submodule Γ(X, V.1) Γ(F, V.1))) :=
  affineEquiv (I ^ n) F V

section Spec

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

/-- The ideal in the original coordinate ring of a spectrum. -/
def specIdeal (I : (Spec R).IdealSheafData) : Ideal R :=
  (I.ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso R).hom.hom

omit [IsNoetherianRing R] in
lemma specIdeal_map (I : (Spec R).IdealSheafData) (n : ℕ) :
    ((specIdeal I) ^ n).map (algebraMap R Γ(Spec R, ⊤)) =
      (I.ideal ⟨⊤, isAffineOpen_top _⟩) ^ n := by
  rw [Ideal.map_pow, specIdeal, Ideal.map_map]
  change (Ideal.map ((Scheme.ΓSpecIso R).hom ≫ (Scheme.ΓSpecIso R).inv).hom _) ^ n = _
  simp

/-- The range calculation transported to the original spectrum's coefficient ring. -/
lemma spec_power_range (I : (Spec R).IdealSheafData) (n : ℕ) (F : (Spec R).Modules)
    [F.IsFinitePresentation] :
    LinearMap.range (moduleSpecΓFunctor.map (inclusion (I ^ n) F)).hom =
      (specIdeal I) ^ n • (⊤ : Submodule R (moduleSpecΓFunctor.obj F)) := by
  have h := congrArg (fun P : Submodule Γ(Spec R, ⊤) Γ(F, ⊤) ↦
    P.restrictScalars R) (inclusion_range (I ^ n) F
    ⟨⊤, isAffineOpen_top _⟩)
  change LinearMap.range (moduleSpecΓFunctor.map (inclusion (I ^ n) F)).hom =
    (((I.ideal ⟨⊤, isAffineOpen_top _⟩) ^ n •
      (⊤ : Submodule Γ(Spec R, ⊤) Γ(F, ⊤))).restrictScalars R) at h
  rw [← specIdeal_map I n, Ideal.smul_restrictScalars] at h
  exact h

/-- Actual image sections in the coefficient module used by the affine extension theorem. -/
def specPowerEquiv (I : (Spec R).IdealSheafData) (n : ℕ) (F : (Spec R).Modules)
    [F.IsFinitePresentation] :
    moduleSpecΓFunctor.obj (power I n F) ≃ₗ[R]
      ↥((specIdeal I) ^ n • (⊤ : Submodule R (moduleSpecΓFunctor.obj F))) :=
  (LinearEquiv.ofInjective (σ₁₂ := RingHom.id R)
    (moduleSpecΓFunctor.map (inclusion (I ^ n) F)).hom
    (ModuleSubobjectCoverEquality.app_injective (inclusion (I ^ n) F) ⊤)).trans
      (LinearEquiv.ofEq _ _ (spec_power_range I n F))

/-- The global power image is B2's constructed affine power source. -/
def specPowerIso (I : (Spec R).IdealSheafData) (n : ℕ) (F : (Spec R).Modules)
    [F.IsFinitePresentation] :
    power I n F ≅ AffineIdealPowerExtension.powerMultiple F (specIdeal I) n :=
  (asIso (power I n F).fromTildeΓ).symm ≪≫
    (tilde.functor R).mapIso (specPowerEquiv I n F).toModuleIso

/-- The affine comparison commutes with the original sheaf inclusion. -/
@[reassoc]
lemma specPowerIso_inclusion (I : (Spec R).IdealSheafData) (n : ℕ) (F : (Spec R).Modules)
    [F.IsFinitePresentation] :
    (specPowerIso I n F).hom ≫
      AffineIdealPowerExtension.powerMultipleι F (specIdeal I) n = inclusion (I ^ n) F := by
  dsimp only [specPowerIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    AffineIdealPowerExtension.powerMultipleι,
    AffineCoherentSubmoduleRestriction.coefficientInclusion]
  rw [Category.assoc, ← Functor.map_comp_assoc]
  have he : (specPowerEquiv I n F).toModuleIso.hom ≫
      ModuleCat.ofHom ((specIdeal I) ^ n •
        (⊤ : Submodule R (moduleSpecΓFunctor.obj F))).subtype =
      moduleSpecΓFunctor.map (inclusion (I ^ n) F) := by
    ext s
    rfl
  rw [he]
  have hn : (tilde.functor R).map (moduleSpecΓFunctor.map (inclusion (I ^ n) F)) ≫
      F.fromTildeΓ = (power I n F).fromTildeΓ ≫ inclusion (I ^ n) F :=
    fromTildeΓNatTrans.naturality _
  rw [hn]
  exact IsIso.inv_hom_id_assoc _ _

end Spec

end FLT.Mazur.GlobalIdealPower
