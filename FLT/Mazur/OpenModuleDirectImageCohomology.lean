/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleOpenCohomologyRestriction
public import FLT.Mazur.AcyclicPushforwardCohomology
public import FLT.Mazur.ClosedPushforwardRestriction

/-!
# Open restriction of acyclic module direct-image cohomology

Local acyclicity follows from the original higher-image vanishing. The local
linear comparison is the existing absolute comparison for the restricted
morphism, composed with the actual module pushforward-restriction isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace FLT.Mazur.FCurve

open CoherentDevissage OpenSheafCohomologyRestriction

local instance moduleOpenDirectImageHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :=
  HasExt.standard _

local instance moduleOpenDirectImageRestrictedHasExt {T : TopCat.{u}} (W : Opens T) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u}) :=
  HasExt.standard _

private lemma restriction_forget_map {S : Scheme.{u}} (U : S.Opens)
    {M N : S.Modules} (a : M ⟶ N) :
    (OpenSheafRestriction.restriction U).map ((SheafOfModules.toSheaf S.ringCatSheaf).map a) =
      (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map ((restrictFunctor U.ι).map a) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext O
  rfl

private lemma moduleOpenRestriction_openHEquiv {S : Scheme.{u}} (M : S.Modules)
    {U V : S.Opens} (i : V ⟶ U) (n : ℕ)
    (x : Sheaf.H'.{u + 1} (moduleAbelianSheaf M) n U) :
    moduleOpenRestriction M i n (moduleOpenHEquiv U M n x) =
      moduleOpenHEquiv V M n (((moduleAbelianSheaf M).cohomologyPresheaf n).map i.op x) := by
  change moduleOpenHEquiv V M n
    (((moduleAbelianSheaf M).cohomologyPresheaf n).map i.op
      ((moduleOpenHEquiv U M n).symm (moduleOpenHEquiv U M n x))) = _
  rw [AddEquiv.symm_apply_apply]

private lemma restriction_forget_H_map {S : Scheme.{u}} (U : S.Opens)
    {M N : S.Modules} (a : M ⟶ N) (n : ℕ) (x : ModuleH (M.restrict U.ι) n) :
    Sheaf.H.map ((OpenSheafRestriction.restriction U).map
      ((SheafOfModules.toSheaf S.ringCatSheaf).map a)) n x =
      moduleHMap ((restrictFunctor U.ι).map a) n x :=
  congrArg (fun b ↦ Sheaf.H.map b n x) (restriction_forget_map U a)

private lemma restricted_absolute_eq {S T : Scheme.{u}} (W : S.Opens) (M : S.Modules)
    (g : W.toScheme ⟶ T)
    (h : AbsoluteDirectImageCohomology.Acyclic g.base (moduleAbelianSheaf (M.restrict W.ι)))
    (n : ℕ) (x : Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base).obj
      (moduleAbelianSheaf (M.restrict W.ι))) n) :
    AbsoluteDirectImageCohomology.cohomologyEquiv g.base
      (moduleAbelianSheaf (M.restrict W.ι)) h n x =
      AbsoluteDirectImageCohomology.cohomologyEquiv g.base
        ((OpenSheafRestriction.restriction W).obj (moduleAbelianSheaf M)) h n x := rfl

/-- The actual module open comparison is natural in coefficients. -/
lemma moduleOpenHEquiv_naturality {S : Scheme.{u}} (U : S.Opens)
    {M N : S.Modules} (a : M ⟶ N) (n : ℕ)
    (x : Sheaf.H'.{u + 1} (moduleAbelianSheaf M) n U) :
    moduleOpenHEquiv U N n
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology S) n).map
        ((SheafOfModules.toSheaf S.ringCatSheaf).map a)).app (op U) x) =
      moduleHMap ((Scheme.Modules.restrictFunctor U.ι).map a) n (moduleOpenHEquiv U M n x) := by
  refine (OpenSheafCohomology.openHEquiv_naturality U
    ((SheafOfModules.toSheaf S.ringCatSheaf).map a) n x).trans ?_
  exact restriction_forget_H_map U a n (moduleOpenHEquiv U M n x)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  (M : X.Modules) (hM : ModulePushforwardAcyclic f M)

include hM

/-- Local module acyclicity is derived from the original module vanishing. -/
lemma modulePushforwardAcyclic_restrict :
    ModulePushforwardAcyclic (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) := by
  intro q
  exact ModuleDerivedAbelianComparison.isZero_module_of_abelian (f ∣_ U) _ q
    (OpenDirectImageRestriction.restricted_acyclic f U (moduleAbelianSheaf M)
      (modulePushforwardAcyclic_abelian f M hM) q)

omit hM in
/-- Forgetting the underived module comparison gives the abelian restriction comparison. -/
lemma closedPushforwardRestriction_abelian :
    (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map
      ((closedPushforwardRestriction f U).hom.app M) =
        (OpenDirectImageRestriction.pushforwardRestriction f U).hom.app
          (moduleAbelianSheaf M) := by
  apply Sheaf.hom_ext
  ext V x
  rfl

/-- The local comparison is linear over every section on the target open. -/
def openAcyclicPushforwardModuleHEquiv (n : ℕ) :
    letI := Module.compHom (ModuleH (M.restrict (f ⁻¹ᵁ U).ι) n) (f ∣_ U).appTop.hom
    ModuleH (((pushforward f).obj M).restrict U.ι) n ≃ₗ[Γ(U.toScheme, ⊤)]
      ModuleH (M.restrict (f ⁻¹ᵁ U).ι) n := by
  letI := Module.compHom (ModuleH (M.restrict (f ⁻¹ᵁ U).ι) n) (f ∣_ U).appTop.hom
  exact (moduleHIsoOfIso ((closedPushforwardRestriction f U).app M) n).trans
      (acyclicPushforwardModuleHEquiv (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι)
        (modulePushforwardAcyclic_restrict f U M hM) n)

private lemma openAcyclicPushforwardModuleHEquiv_apply (n : ℕ)
    (x : ModuleH (((pushforward f).obj M).restrict U.ι) n) :
    openAcyclicPushforwardModuleHEquiv f U M hM n x =
      AbsoluteDirectImageCohomology.cohomologyEquiv (f ∣_ U).base
        (moduleAbelianSheaf (M.restrict (f ⁻¹ᵁ U).ι))
        (modulePushforwardAcyclic_abelian (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι)
          (modulePushforwardAcyclic_restrict f U M hM)) n
        (Sheaf.H.map ((SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map
          ((closedPushforwardRestriction f U).hom.app M)) n x) := rfl

private lemma openAcyclicPushforwardModuleHEquiv_local (n : ℕ)
    (x : Sheaf.H'.{u + 1} (moduleAbelianSheaf ((pushforward f).obj M)) n U) :
    openAcyclicPushforwardModuleHEquiv f U M hM n
      (moduleOpenHEquiv U ((pushforward f).obj M) n x) =
      OpenDirectImageRestriction.localComparison f U (moduleAbelianSheaf M)
        (modulePushforwardAcyclic_abelian f M hM) n x := by
  rw [openAcyclicPushforwardModuleHEquiv_apply, closedPushforwardRestriction_abelian,
    restricted_absolute_eq]
  rfl

/-- The local linear comparison is the original open Ext comparison under `moduleOpenHEquiv`. -/
lemma openAcyclicPushforwardModuleHEquiv_eq (n : ℕ)
    (x : Sheaf.H'.{u + 1} (moduleAbelianSheaf ((pushforward f).obj M)) n U) :
    openAcyclicPushforwardModuleHEquiv f U M hM n
      (moduleOpenHEquiv U ((pushforward f).obj M) n x) =
        moduleOpenHEquiv (f ⁻¹ᵁ U) M n
          (OpenDirectImageCohomology.cohomologyEquiv f.base (moduleAbelianSheaf M)
            (modulePushforwardAcyclic_abelian f M hM) U n x) :=
  (openAcyclicPushforwardModuleHEquiv_local f U M hM n x).trans
    (OpenDirectImageRestriction.localComparison_eq f U (moduleAbelianSheaf M)
      (modulePushforwardAcyclic_abelian f M hM) n x)

/-- The local comparisons commute with ambient open restriction. -/
lemma openAcyclicPushforwardModuleHEquiv_restrict {V : Y.Opens} (i : V ⟶ U) (n : ℕ)
    (x : ModuleH (((pushforward f).obj M).restrict U.ι) n) :
    openAcyclicPushforwardModuleHEquiv f V M hM n
      (moduleOpenRestriction ((pushforward f).obj M) i n x) =
        moduleOpenRestriction M ((Opens.map f.base).map i) n
          (openAcyclicPushforwardModuleHEquiv f U M hM n x) := by
  obtain ⟨x, rfl⟩ := (moduleOpenHEquiv U ((pushforward f).obj M) n).surjective x
  rw [moduleOpenRestriction_openHEquiv, openAcyclicPushforwardModuleHEquiv_eq,
    openAcyclicPushforwardModuleHEquiv_eq, moduleOpenRestriction_openHEquiv]
  exact congrArg (moduleOpenHEquiv (f ⁻¹ᵁ V) M n)
    (OpenDirectImageNaturality.cohomologyEquiv_restrict f.base (moduleAbelianSheaf M)
      (modulePushforwardAcyclic_abelian f M hM) i n x)

/-- Restricting the existing absolute linear comparison gives the local comparison. -/
lemma openAcyclicPushforwardModuleHEquiv_global (n : ℕ)
    (x : ModuleH ((pushforward f).obj M) n) :
    openAcyclicPushforwardModuleHEquiv f U M hM n
      (globalOpenRestriction U (moduleAbelianSheaf ((pushforward f).obj M)) n x) =
        globalOpenRestriction (f ⁻¹ᵁ U) (moduleAbelianSheaf M) n
          (acyclicPushforwardModuleHEquiv f M hM n x) := by
  change openAcyclicPushforwardModuleHEquiv f U M hM n
    (moduleOpenHEquiv U ((pushforward f).obj M) n
      (AffineCohomologyVanishingLocal.restrictSheafH _ n U x)) = _
  rw [openAcyclicPushforwardModuleHEquiv_eq]
  exact congrArg (moduleOpenHEquiv (f ⁻¹ᵁ U) M n)
    (OpenDirectImageNaturality.cohomologyEquiv_restrictSheafH f.base (moduleAbelianSheaf M)
      (modulePushforwardAcyclic_abelian f M hM) U n x)

/-- Coefficient maps commute with the local module comparison. -/
lemma openAcyclicPushforwardModuleHEquiv_naturality {N : X.Modules}
    (hN : ModulePushforwardAcyclic f N) (a : M ⟶ N) (n : ℕ)
    (x : ModuleH (((pushforward f).obj M).restrict U.ι) n) :
    openAcyclicPushforwardModuleHEquiv f U N hN n
      (moduleHMap ((restrictFunctor U.ι).map ((pushforward f).map a)) n x) =
        moduleHMap ((restrictFunctor (f ⁻¹ᵁ U).ι).map a) n
          (openAcyclicPushforwardModuleHEquiv f U M hM n x) := by
  obtain ⟨x, rfl⟩ := (moduleOpenHEquiv U ((pushforward f).obj M) n).surjective x
  rw [← moduleOpenHEquiv_naturality, openAcyclicPushforwardModuleHEquiv_eq]
  refine (congrArg (moduleOpenHEquiv (f ⁻¹ᵁ U) N n)
    (OpenDirectImageCohomology.cohomologyEquiv_naturality f.base
      ((SheafOfModules.toSheaf X.ringCatSheaf).map a)
      (modulePushforwardAcyclic_abelian f M hM)
      (modulePushforwardAcyclic_abelian f N hN) U n x)).trans ?_
  refine (moduleOpenHEquiv_naturality (f ⁻¹ᵁ U) a n _).trans ?_
  exact congrArg (moduleHMap ((restrictFunctor (f ⁻¹ᵁ U).ι).map a) n)
    (openAcyclicPushforwardModuleHEquiv_eq f U M hM n x).symm

/-- The local comparison after restriction to an arbitrary base-ring action. -/
def openAcyclicPushforwardRingHEquiv {R : Type v} [Ring R]
    (ρ : R →+* Γ(U.toScheme, ⊤)) (n : ℕ) :
    letI := Module.compHom (ModuleH (((pushforward f).obj M).restrict U.ι) n) ρ
    letI := Module.compHom (ModuleH (M.restrict (f ⁻¹ᵁ U).ι) n)
      ((f ∣_ U).appTop.hom.comp ρ)
    ModuleH (((pushforward f).obj M).restrict U.ι) n ≃ₗ[R]
      ModuleH (M.restrict (f ⁻¹ᵁ U).ι) n := by
  letI := Module.compHom (ModuleH (M.restrict (f ⁻¹ᵁ U).ι) n) (f ∣_ U).appTop.hom
  letI := Module.compHom (ModuleH (((pushforward f).obj M).restrict U.ι) n) ρ
  letI := Module.compHom (ModuleH (M.restrict (f ⁻¹ᵁ U).ι) n)
    ((f ∣_ U).appTop.hom.comp ρ)
  exact { toAddEquiv := (openAcyclicPushforwardModuleHEquiv f U M hM n).toAddEquiv
          map_smul' := fun r x ↦ (openAcyclicPushforwardModuleHEquiv f U M hM n).map_smul
            (ρ r) x }

/-- The comparison in the existing ring-cohomology functor's codomain. -/
def openAcyclicPushforwardRingHIso {R : Type u} [CommRing R]
    (ρ : R →+* Γ(U.toScheme, ⊤)) (n : ℕ) :
    (moduleRingHFunctor ρ n).obj (((pushforward f).obj M).restrict U.ι) ≅
      (moduleRingHFunctor ((f ∣_ U).appTop.hom.comp ρ) n).obj (M.restrict (f ⁻¹ᵁ U).ι) :=
  (openAcyclicPushforwardRingHEquiv f U M hM ρ n).toModuleIso

/-- The same local comparison retaining a specified structure morphism to a field. -/
def openAcyclicPushforwardScalarHEquiv {k : Type u} [Field k]
    (g : U.toScheme ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    ModuleScalarH g (((pushforward f).obj M).restrict U.ι) n ≃ₗ[k]
      ModuleScalarH ((f ∣_ U) ≫ g) (M.restrict (f ⁻¹ᵁ U).ι) n := by
  letI := Module.compHom (ModuleH (M.restrict (f ⁻¹ᵁ U).ι) n) (f ∣_ U).appTop.hom
  refine { toAddEquiv := (openAcyclicPushforwardModuleHEquiv f U M hM n).toAddEquiv
           map_smul' := ?_ }
  intro r x
  change ModuleH (((pushforward f).obj M).restrict U.ι) n at x
  have h : structureScalarMap ((f ∣_ U) ≫ g) r =
      (f ∣_ U).appTop (structureScalarMap g r) := by
    simp [structureScalarMap]
  change openAcyclicPushforwardModuleHEquiv f U M hM n (structureScalarMap g r • x) =
    structureScalarMap ((f ∣_ U) ≫ g) r • openAcyclicPushforwardModuleHEquiv f U M hM n x
  rw [h]
  exact (openAcyclicPushforwardModuleHEquiv f U M hM n).map_smul (structureScalarMap g r) x

omit M hM in
/-- The scalar maps in the open-restriction square commute. -/
lemma openDirectImage_restriction_scalars {V : Y.Opens} (i : V ⟶ U) :
    (f ∣_ U).appTop ≫ (X.homOfLE (f.preimage_mono (leOfHom i))).appTop =
      (Y.homOfLE (leOfHom i)).appTop ≫ (f ∣_ V).appTop := by
  have h := congrArg Scheme.Hom.appTop (morphismRestrict_homOfLE f V U (leOfHom i))
  simpa only [Scheme.Hom.comp_appTop] using h.symm

/-- The restriction square after restriction of scalars to any base ring. -/
lemma openAcyclicPushforwardRingHEquiv_restrict {R : Type v} [Ring R]
    (ρ : R →+* Γ(U.toScheme, ⊤)) {V : Y.Opens} (i : V ⟶ U) (n : ℕ)
    (x : ModuleH (((pushforward f).obj M).restrict U.ι) n) :
    openAcyclicPushforwardRingHEquiv f V M hM
      ((Y.homOfLE (leOfHom i)).appTop.hom.comp ρ) n
      (moduleOpenRestrictionRing ((pushforward f).obj M) i ρ n x) =
        moduleOpenRestrictionRing M ((Opens.map f.base).map i)
          ((f ∣_ U).appTop.hom.comp ρ) n
          (openAcyclicPushforwardRingHEquiv f U M hM ρ n x) :=
  openAcyclicPushforwardModuleHEquiv_restrict f U M hM i n x

/-- The restriction square for the existing cohomology with field scalars. -/
lemma openAcyclicPushforwardScalarHEquiv_restrict {k : Type u} [Field k]
    (g : U.toScheme ⟶ Spec (CommRingCat.of k)) {V : Y.Opens} (i : V ⟶ U) (n : ℕ)
    (x : ModuleScalarH g (((pushforward f).obj M).restrict U.ι) n) :
    openAcyclicPushforwardScalarHEquiv f V M hM (Y.homOfLE (leOfHom i) ≫ g) n
      (moduleOpenRestrictionScalar ((pushforward f).obj M) i g n x) =
        moduleOpenRestrictionScalar M ((Opens.map f.base).map i) ((f ∣_ U) ≫ g) n
          (openAcyclicPushforwardScalarHEquiv f U M hM g n x) :=
  openAcyclicPushforwardModuleHEquiv_restrict f U M hM i n x

/-- The base-ring comparison is natural in coefficient modules. -/
lemma openAcyclicPushforwardRingHIso_naturality {R : Type u} [CommRing R]
    (ρ : R →+* Γ(U.toScheme, ⊤)) {N : X.Modules} (hN : ModulePushforwardAcyclic f N)
    (a : M ⟶ N) (n : ℕ) :
    (moduleRingHFunctor ρ n).map ((restrictFunctor U.ι).map ((pushforward f).map a)) ≫
      (openAcyclicPushforwardRingHIso f U N hN ρ n).hom =
        (openAcyclicPushforwardRingHIso f U M hM ρ n).hom ≫
          (moduleRingHFunctor ((f ∣_ U).appTop.hom.comp ρ) n).map
            ((restrictFunctor (f ⁻¹ᵁ U).ι).map a) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact openAcyclicPushforwardModuleHEquiv_naturality f U M hM hN a n x

/-- Coefficient naturality for the field-valued local comparison. -/
lemma openAcyclicPushforwardScalarHEquiv_naturality {k : Type u} [Field k]
    (g : U.toScheme ⟶ Spec (CommRingCat.of k)) {N : X.Modules}
    (hN : ModulePushforwardAcyclic f N) (a : M ⟶ N) (n : ℕ)
    (x : ModuleScalarH g (((pushforward f).obj M).restrict U.ι) n) :
    openAcyclicPushforwardScalarHEquiv f U N hN g n
      (moduleScalarHMap g ((restrictFunctor U.ι).map ((pushforward f).map a)) n x) =
        moduleScalarHMap ((f ∣_ U) ≫ g) ((restrictFunctor (f ⁻¹ᵁ U).ι).map a) n
          (openAcyclicPushforwardScalarHEquiv f U M hM g n x) :=
  openAcyclicPushforwardModuleHEquiv_naturality f U M hM hN a n x

/-- The global square retains the existing absolute base-ring comparison. -/
lemma openAcyclicPushforwardRingHEquiv_global {R : Type v} [Ring R]
    (ρ : R →+* Γ(Y, ⊤)) (n : ℕ) (x : ModuleH ((pushforward f).obj M) n) :
    openAcyclicPushforwardRingHEquiv f U M hM (U.ι.appTop.hom.comp ρ) n
      (globalOpenRestriction U (moduleAbelianSheaf ((pushforward f).obj M)) n x) =
        globalOpenRestriction (f ⁻¹ᵁ U) (moduleAbelianSheaf M) n
          (acyclicPushforwardRingHEquiv f M hM ρ n x) :=
  openAcyclicPushforwardModuleHEquiv_global f U M hM n x

/-- The global square retains the existing absolute comparison with field scalars. -/
lemma openAcyclicPushforwardScalarHEquiv_global {k : Type u} [Field k]
    (g : Y ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    (x : ModuleScalarH g ((pushforward f).obj M) n) :
    openAcyclicPushforwardScalarHEquiv f U M hM (U.ι ≫ g) n
      (globalOpenRestriction U (moduleAbelianSheaf ((pushforward f).obj M)) n x) =
        globalOpenRestriction (f ⁻¹ᵁ U) (moduleAbelianSheaf M) n
          (acyclicPushforwardScalarHEquiv f M hM g n x) :=
  openAcyclicPushforwardModuleHEquiv_global f U M hM n x

end FLT.Mazur.FCurve
