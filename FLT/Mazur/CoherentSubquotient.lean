/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleStalkExact
public import FLT.Mazur.TildePrincipalOpen

/-!
# Coherent subquotients

Exactness of tilde follows from injectivity on principal opens and preservation
of cokernels. Affine finite-module presentations then give coherent kernels,
images, and cokernels on every locally Noetherian scheme. The canonical kernel,
image, and cokernel sequences are exported as coherent short exact sequences.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

section LocalPresentation

open SheafOfModules

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [HasPullbacks C] [HasPullbacks D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The continuous pushforward associated to a restriction preserves finite presentations. -/
lemma coherentPresentation_pushforward (G : D ⥤ C)
    [G.IsContinuous K J] [G.IsCocontinuous K J] [G.IsLeftAdjoint]
    (φ : B ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj A) [IsIso φ]
    [∀ X, Functor.IsContinuous (Over.post (X := X) G) (K.over _) (J.over _)]
    (η : (pushforward φ).obj (unit A) ≅ unit B)
    (M : SheafOfModules.{u} A) [M.IsFinitePresentation] :
    ((pushforward φ).obj M).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := IsFinitePresentation.exists_quasicoherentData M
  have := hq
  have h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u}
        (pushforward.{u} (R := A.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ)) := by
    intro X Y f
    let G' := Over.post (X := X) G ⋙ Over.map f
    have : G'.IsContinuous (K.over X) (J.over Y) :=
      Functor.isContinuous_comp _ _ _ (J.over _) _
    have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
    let a : B.over X ⟶
        (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (A.over Y) :=
      ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
    have : (pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
    infer_instance
  refine ⟨q.pushforward G φ η h, ⟨fun i ↦ ?_⟩⟩
  dsimp [QuasicoherentData.pushforward]
  exact affinePresentation_map_isFinite (q.presentation i.2.1) _ _

end LocalPresentation

open Scheme.Modules

/-- Restricting a coherent sheaf along an open immersion preserves finite presentation. -/
lemma coherentPresentation_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsFinitePresentation] :
    (M.restrict f).IsFinitePresentation := by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  have : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : X.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  exact coherentPresentation_pushforward f.opensFunctor φ (restrictUnitIso f) M

/-- A coherent sheaf on a Noetherian affine spectrum has a finite global presentation. -/
lemma affineCoherent_exists_presentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsFinitePresentation] :
    ∃ P : M.Presentation, P.IsFinite := by
  let N := moduleSpecΓFunctor.obj M
  have : Module.Finite R N := affineCoherent_finite_sections M
  have := Module.finitePresentation_of_finite R N
  obtain ⟨s, hs, ht⟩ := Module.FinitePresentation.out (R := R) (M := N)
  obtain ⟨t, ht⟩ := ht
  let P := presentationTilde N (s : Set N) hs (t : Set (s →₀ R)) ht
  have : P.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set N))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set (s →₀ R)))⟩ }
  exact ⟨P.ofIsIso (affineCoherentIso M).inv, inferInstance⟩

section Affine

variable {R : CommRingCat.{u}}

/-- Tilde preserves injections, as can be checked on a basis of principal opens. -/
instance coherentTilde_preservesMonomorphisms :
    (tilde.functor R).PreservesMonomorphisms where
  preserves {M N} f hf := by
    constructor
    intro P a b hab
    apply modulesSpecToSheaf.map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ _ PrimeSpectrum.isBasis_basic_opens
    intro r
    have hm : Mono ((TildePrincipalOpen.sectionsFunctor r).map f) :=
      (ModuleCat.mono_iff_injective _).mpr
        (TildePrincipalOpen.sections_injective r f ((ModuleCat.mono_iff_injective f).mp hf))
    apply (cancel_mono ((TildePrincipalOpen.sectionsFunctor r).map f)).mp
    exact congrArg (fun g ↦ (modulesSpecToSheaf.map g).hom.app (.op
      (PrimeSpectrum.basicOpen r))) hab

instance coherentTilde_preservesHomology : (tilde.functor R).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance coherentTilde_preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) :=
  (tilde.functor R).preservesFiniteLimits_of_preservesHomology

/-- A coefficient short exact sequence gives a short exact sequence of tilde sheaves. -/
theorem coherentTilde_shortExact {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    (S.map (tilde.functor R)).ShortExact := hS.map_of_exact _

variable [IsNoetherianRing R]

/-- Kernels of maps of finite modules over a Noetherian ring are finite. -/
lemma coherentModule_kernel_finite {M N : ModuleCat.{u} R} (f : M ⟶ N)
    [Module.Finite R M] : Module.Finite R (kernel f : ModuleCat R) :=
  Module.Finite.of_injective (kernel.ι f).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

omit [IsNoetherianRing R] in
/-- Cokernels of maps into finite modules are finite. -/
lemma coherentModule_cokernel_finite {M N : ModuleCat.{u} R} (f : M ⟶ N)
    [Module.Finite R N] : Module.Finite R (cokernel f : ModuleCat R) :=
  Module.Finite.of_surjective (cokernel.π f).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- The kernel of a map between coherent sheaves on an affine spectrum is coherent. -/
theorem affineCoherent_kernel {M N : (Spec R).Modules}
    [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) :
    (kernel f).IsFinitePresentation := by
  let eM := affineCoherentIso M
  let eN := affineCoherentIso N
  let g := (tilde.functor R).preimage (eM.inv ≫ f ≫ eN.hom)
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := affineCoherent_finite_sections M
  have : Module.Finite R (kernel g : ModuleCat R) := coherentModule_kernel_finite g
  let e : tilde (kernel g) ≅ kernel f :=
    PreservesKernel.iso (tilde.functor R) g ≪≫
      kernel.mapIso _ f eM.symm eN.symm (by
        change (tilde.functor R).map g ≫ eN.inv = eM.inv ≫ f
        simp only [g, Functor.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso e
    (affineTilde_isFinitePresentation_of_finite (kernel g))

/-- The cokernel of a map between coherent sheaves on an affine spectrum is coherent. -/
theorem affineCoherent_cokernel {M N : (Spec R).Modules}
    [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) :
    (cokernel f).IsFinitePresentation := by
  let eM := affineCoherentIso M
  let eN := affineCoherentIso N
  let g := (tilde.functor R).preimage (eM.inv ≫ f ≫ eN.hom)
  have : Module.Finite R (moduleSpecΓFunctor.obj N) := affineCoherent_finite_sections N
  have : Module.Finite R (cokernel g : ModuleCat R) := coherentModule_cokernel_finite g
  let e : tilde (cokernel g) ≅ cokernel f :=
    PreservesCokernel.iso (tilde.functor R) g ≪≫
      cokernel.mapIso _ f eM.symm eN.symm (by
        change (tilde.functor R).map g ≫ eN.inv = eM.inv ≫ f
        simp only [g, Functor.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso e
    (affineTilde_isFinitePresentation_of_finite (cokernel g))

/-- The image of a map between coherent sheaves on an affine spectrum is coherent. -/
theorem affineCoherent_image {M N : (Spec R).Modules}
    [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) :
    (Abelian.image f).IsFinitePresentation := by
  have := affineCoherent_cokernel f
  exact affineCoherent_kernel (cokernel.π f)

end Affine

/-- Finite presentations on every affine chart descend to a finite presentation locally. -/
lemma coherentPresentation_of_affine_restrict {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules)
    (h : ∀ U : X.affineOpens, (M.restrict U.2.fromSpec).IsFinitePresentation) :
    M.IsFinitePresentation := by
  have presentations (U : X.affineOpens) :
      ∃ P : (M.over U.1).Presentation, P.IsFinite := by
    have := h U
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨P, hP⟩ := affineCoherent_exists_presentation (M.restrict U.2.fromSpec)
    have := hP
    let E := overEquiv U.1
    let F := restrictFunctor U.2.isoSpec.hom ⋙ E.inverse
    have : PreservesColimitsOfSize.{u, u} (restrictFunctor U.2.isoSpec.hom) := inferInstance
    have : PreservesColimitsOfSize.{u, u} F := comp_preservesColimits _ _
    let unitIso : SheafOfModules.unit (X.ringCatSheaf.over U.1) ≅
        F.obj (SheafOfModules.unit _) :=
      E.unitIso.app _ ≪≫ E.inverse.mapIso (restrictUnitIso U.2.isoSpec.hom).symm
    let e : F.obj (M.restrict U.2.fromSpec) ≅ M.over U.1 :=
      E.inverse.mapIso
        ((restrictFunctorComp U.2.isoSpec.hom U.2.fromSpec).symm.app M ≪≫
          (restrictFunctorCongr U.2.isoSpec_hom_fromSpec).app M ≪≫
          (overFunctorEquiv U.1).symm.app M) ≪≫ E.unitIso.symm.app _
    have := affinePresentation_map_isFinite P F unitIso
    exact ⟨(P.map F unitIso).ofIsIso e.hom, inferInstance⟩
  choose P hP using presentations
  let q : M.QuasicoherentData :=
    { I := X.affineOpens
      X := fun U ↦ U.1
      coversTop := by
        rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
        exact iSup_affineOpens_eq_top X
      presentation := P }
  refine { exists_quasicoherentData := ?_ }
  exact ⟨q, { isFinite_presentation := hP }⟩

/-- Restriction along an open immersion preserves finite limits of module sheaves. -/
instance coherentRestrict_finiteLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteLimits (restrictFunctor f) := by
  have : PreservesFiniteLimits (Scheme.Modules.toPresheaf Y) := inferInstance
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj f.opensFunctor.op) := inferInstance
  have : PreservesFiniteLimits (restrictFunctor f ⋙ Scheme.Modules.toPresheaf X) :=
    inferInstanceAs (PreservesFiniteLimits
      (Scheme.Modules.toPresheaf Y ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj f.opensFunctor.op))
  exact preservesFiniteLimits_of_reflects_of_preserves
    (restrictFunctor f) (Scheme.Modules.toPresheaf X)

/-- Kernels of morphisms of coherent sheaves on a locally Noetherian scheme are coherent. -/
theorem coherent_kernel {X : Scheme.{u}} [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) :
    (kernel f).IsFinitePresentation := by
  apply coherentPresentation_of_affine_restrict
  intro U
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have := coherentPresentation_restrict U.2.fromSpec M
  have := coherentPresentation_restrict U.2.fromSpec N
  let F := restrictFunctor U.2.fromSpec
  exact (SheafOfModules.isFinitePresentation (Spec Γ(X, U.1)).ringCatSheaf).prop_of_iso
    (PreservesKernel.iso F f).symm
    (affineCoherent_kernel (F.map f))

/-- Cokernels of morphisms of coherent sheaves on a locally Noetherian scheme are coherent. -/
theorem coherent_cokernel {X : Scheme.{u}} [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) :
    (cokernel f).IsFinitePresentation := by
  apply coherentPresentation_of_affine_restrict
  intro U
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have := coherentPresentation_restrict U.2.fromSpec M
  have := coherentPresentation_restrict U.2.fromSpec N
  let F := restrictFunctor U.2.fromSpec
  exact (SheafOfModules.isFinitePresentation (Spec Γ(X, U.1)).ringCatSheaf).prop_of_iso
    (PreservesCokernel.iso F f).symm
    (affineCoherent_cokernel (F.map f))

/-- Images of morphisms of coherent sheaves on a locally Noetherian scheme are coherent. -/
theorem coherent_image {X : Scheme.{u}} [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) :
    (Abelian.image f).IsFinitePresentation := by
  have := coherent_cokernel f
  exact coherent_kernel (cokernel.π f)

section Sequences

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {M N : X.Modules}
  [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N)

/-- A coherent epimorphism gives the coherent kernel short exact sequence. -/
theorem coherent_kernelSequence [Epi f] : CoherentSequence (ShortComplex.kernelSequence f) where
  shortExact :=
    { exact := ShortComplex.kernelSequence_exact f
      epi_g := inferInstanceAs (Epi f) }
  finite₁ := coherent_kernel f
  finite₂ := inferInstanceAs M.IsFinitePresentation
  finite₃ := inferInstanceAs N.IsFinitePresentation

/-- A coherent monomorphism gives the coherent cokernel short exact sequence. -/
theorem coherent_cokernelSequence [Mono f] :
    CoherentSequence (ShortComplex.cokernelSequence f) where
  shortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      mono_f := inferInstanceAs (Mono f) }
  finite₁ := inferInstanceAs M.IsFinitePresentation
  finite₂ := inferInstanceAs N.IsFinitePresentation
  finite₃ := coherent_cokernel f

/-- The canonical sequence from the kernel to the source and then its image. -/
def coherentKernelImageComplex : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι f) (Abelian.factorThruImage f) (by
    apply (cancel_mono (Abelian.image.ι f)).mp
    simp only [Category.assoc, Abelian.image.fac, kernel.condition, zero_comp])

/-- Kernel, source, and image form a coherent short exact sequence. -/
theorem coherent_kernelImageSequence : CoherentSequence (coherentKernelImageComplex f) where
  shortExact := by
    let φ : coherentKernelImageComplex f ⟶ ShortComplex.kernelSequence f :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := Abelian.image.ι f
        comm₁₂ := by simp [coherentKernelImageComplex]
        comm₂₃ := by simp [coherentKernelImageComplex] }
    exact
      { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
          (ShortComplex.kernelSequence_exact f)
        mono_f := inferInstanceAs (Mono (kernel.ι f))
        epi_g := inferInstanceAs (Epi (Abelian.factorThruImage f)) }
  finite₁ := coherent_kernel f
  finite₂ := inferInstanceAs M.IsFinitePresentation
  finite₃ := coherent_image f

/-- Image, target, and cokernel form a coherent short exact sequence. -/
theorem coherent_imageCokernelSequence :
    CoherentSequence (ShortComplex.kernelSequence (cokernel.π f)) := by
  have := coherent_cokernel f
  exact coherent_kernelSequence (cokernel.π f)

end Sequences

end FLT.Mazur.FCurve.CoherentDevissage
