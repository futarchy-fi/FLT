/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAnnihilator
public import FLT.Mazur.ClosedModuleDescent
public import FLT.Mazur.CoherentAffineCoverSections
public import FLT.Mazur.IdealModuleSheaf
public import FLT.Mazur.ModuleSheafInternalHom

/-!
# The canonical annihilator subsheaf

The scalar action gives a morphism from the given sheaf to the internal Hom
from the actual ideal module. Its kernel is a subsheaf of the original sheaf,
and the ideal kills it. This file constructs the global subobject; coherence
and the equality with the stalk annihilator require further localization results.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.AnnihilatorSubsheaf

variable {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules)

/-- An ideal section viewed as a scalar in the actual structure ring. -/
abbrev scalar (V : X.Opens) (a : Γ(idealModule I, V)) : Γ(X, V) :=
  (idealModuleι I).app V a

/-- A section acts on the actual ideal module on every subopen. -/
def localAction (U : X.Opens) (m : Γ(F, U)) :
    ModuleSheafInternalHom.Sections (idealModule I) F U :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun := fun a ↦ scalar I V.unop.left a •
            F.presheaf.map V.unop.hom.op m
          map_zero' := by simp
          map_add' := by intro a b; simp [add_smul] }
      naturality := fun V W f ↦ by
        ext a
        change Γ(idealModule I, V.unop.left) at a
        change scalar I W.unop.left
          ((idealModule I).presheaf.map f.unop.left.op a) •
            F.presheaf.map W.unop.hom.op m =
          F.presheaf.map f.unop.left.op
            (scalar I V.unop.left a • F.presheaf.map V.unop.hom.op m)
        rw [Scheme.Modules.map_smul]
        have hn := congr($((idealModuleι I).mapPresheaf.naturality f.unop.left.op) a)
        change scalar I W.unop.left
          ((idealModule I).presheaf.map f.unop.left.op a) =
            X.presheaf.map f.unop.left.op (scalar I V.unop.left a) at hn
        rw [hn]
        congr 1
        exact congr($(F.presheaf.map_comp V.unop.hom.op f.unop.left.op) m) }
    (fun V r a ↦ by
      change Γ(X, V.unop.left) at r
      change Γ(idealModule I, V.unop.left) at a
      change scalar I V.unop.left (r • a) • F.presheaf.map V.unop.hom.op m =
        r • (scalar I V.unop.left a • F.presheaf.map V.unop.hom.op m)
      have h := Hom.app_smul (idealModuleι I) r a
      change scalar I V.unop.left (r • a) = r * scalar I V.unop.left a at h
      rw [h, mul_smul])⟩

/-- Evaluation of the local scalar action uses the canonical inclusion of the ideal. -/
@[simp]
lemma localAction_app (U : X.Opens) (m : Γ(F, U)) (V : Over U)
    (a : Γ(idealModule I, V.left)) :
    ModuleSheafInternalHom.app (idealModule I) F (localAction I F U m) V a =
      scalar I V.left a • F.presheaf.map V.hom.op m := rfl

/-- Currying scalar multiplication gives a morphism of the actual module sheaves. -/
def action : F ⟶ ModuleSheafInternalHom.sheaf (idealModule I) F :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := localAction I F U.unop
          map_zero' := by
            apply ModuleSheafInternalHom.sections_ext
            intro V a
            simp
          map_add' := by
            intro m n
            apply ModuleSheafInternalHom.sections_ext
            intro V a
            change scalar I V.left a • F.presheaf.map V.hom.op (m + n) =
              scalar I V.left a • F.presheaf.map V.hom.op m +
                scalar I V.left a • F.presheaf.map V.hom.op n
            rw [map_add, smul_add] }
      naturality := fun U V f ↦ by
        ext m : 2
        change Γ(F, U.unop) at m
        apply ModuleSheafInternalHom.sections_ext
        intro W a
        change scalar I W.left a •
            F.presheaf.map W.hom.op (F.presheaf.map f m) =
          scalar I W.left a • F.presheaf.map (W.hom ≫ f.unop).op m
        exact congrArg (scalar I W.left a • ·)
          (congr($(F.presheaf.map_comp f W.hom.op) m)).symm }
    (fun U r m ↦ by
      change Γ(X, U.unop) at r
      change Γ(F, U.unop) at m
      apply ModuleSheafInternalHom.sections_ext
      intro V a
      change scalar I V.left a • F.presheaf.map V.hom.op (r • m) =
        X.presheaf.map V.hom.op r •
          (scalar I V.left a • F.presheaf.map V.hom.op m)
      rw [Scheme.Modules.map_smul, smul_comm])⟩

/-- The annihilator subsheaf is the kernel of scalar action, with no killing hypothesis on F. -/
def sheaf : X.Modules := kernel (action I F)

/-- The canonical inclusion into the original sheaf. -/
def inclusion : sheaf I F ⟶ F := kernel.ι (action I F)

instance inclusion_mono : Mono (inclusion I F) :=
  inferInstanceAs (Mono (kernel.ι (action I F)))

/-- The resulting subobject of the original sheaf. -/
def subobject : Subobject F := Subobject.mk (inclusion I F)

/-- Its actual sections are the kernel of the action on sections. -/
def sectionsKernelIso (U : X.Opens) :
    (sheaf I F).val.obj (op U) ≅
      ModuleCat.of Γ(X, U) ((action I F).val.app (op U)).hom.ker :=
  letI : (SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)).PreservesZeroMorphisms :=
    ⟨by intros; rfl⟩
  PreservesKernel.iso (SheafOfModules.evaluation.{u} X.ringCatSheaf (op U))
    (action I F) ≪≫ ModuleCat.kernelIsoKer _

/-- The section comparison commutes with the original inclusion. -/
@[simp]
lemma sectionsKernelIso_val (U : X.Opens) (m : Γ(sheaf I F, U)) :
    ((sectionsKernelIso I F U).hom m).val = (inclusion I F).app U m := by
  have h : (sectionsKernelIso I F U).hom ≫
      ModuleCat.ofHom ((action I F).val.app (op U)).hom.ker.subtype =
        (inclusion I F).val.app (op U) := by
    dsimp only [sectionsKernelIso, Iso.trans_hom]
    erw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
    rfl
  exact congr($(h) m)

/-- A section belongs to the image precisely when its local action vanishes. -/
theorem mem_range_inclusion (U : X.Opens) (m : Γ(F, U)) :
    m ∈ Set.range ((inclusion I F).app U) ↔ localAction I F U m = 0 := by
  constructor
  · rintro ⟨n, rfl⟩
    have h := ((sectionsKernelIso I F U).hom n).property
    rwa [sectionsKernelIso_val] at h
  · intro hm
    let n : ((action I F).val.app (op U)).hom.ker := ⟨m, hm⟩
    refine ⟨(sectionsKernelIso I F U).inv n, ?_⟩
    rw [← sectionsKernelIso_val]
    exact congrArg Subtype.val (Iso.inv_hom_id_apply (sectionsKernelIso I F U) n)

/-- Image sections are killed by all ideal sections on every subopen. -/
theorem inclusion_smul (U : X.Opens) (m : Γ(sheaf I F, U)) (V : Over U)
    (a : Γ(idealModule I, V.left)) :
    scalar I V.left a •
      F.presheaf.map V.hom.op ((inclusion I F).app U m) = 0 := by
  have h := (mem_range_inclusion I F U _).mp ⟨m, rfl⟩
  exact congrArg (fun φ ↦ ModuleSheafInternalHom.app (idealModule I) F φ V a) h

/-- The given ideal kills the constructed subsheaf on every affine open. -/
theorem idealKilled : CoherentDevissage.IdealKilled I (sheaf I F) := by
  intro U r hr m
  obtain ⟨a, ha⟩ := (Set.ext_iff.mp (idealModuleι_range I U) r).mpr hr
  apply ModuleSubobjectCoverEquality.app_injective (inclusion I F) U.1
  rw [Hom.app_smul, map_zero, ← ha]
  simpa using inclusion_smul I F U.1 m (Over.mk (𝟙 U.1)) a

/-- Annihilation on an affine open persists on smaller affine opens. -/
lemma affine_restrict_annihilated {U V : X.affineOpens} (h : V ≤ U)
    (m : Γ(F, U.1))
    (hm : m ∈ AffineAnnihilator.annihilated (I.ideal U) Γ(F, U.1)) :
    F.presheaf.map (homOfLE h).op m ∈
      AffineAnnihilator.annihilated (I.ideal V) Γ(F, V.1) := by
  rw [← I.map_ideal h]
  apply (AffineAnnihilator.mem_annihilated_span _ _).mpr
  rintro _ ⟨r, hr, rfl⟩
  exact (F.map_smul (homOfLE (show V.1 ≤ U.1 from h)) r m).symm.trans
    (by rw [hm r hr, map_zero])

/-- Vanishing against affine ideal sections gives vanishing on every subopen. -/
lemma localAction_eq_zero_of_affine (U : X.affineOpens) (m : Γ(F, U.1))
    (hm : m ∈ AffineAnnihilator.annihilated (I.ideal U) Γ(F, U.1)) :
    localAction I F U.1 m = 0 := by
  apply ModuleSheafInternalHom.sections_ext
  intro V a
  change scalar I V.left a • F.presheaf.map V.hom.op m = 0
  apply F.isSheaf.section_ext
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.left.isOpen
  change W ≤ V.left at hWV
  let hWU : (⟨W, hW⟩ : X.affineOpens) ≤ U := hWV.trans (leOfHom V.hom)
  have hk := affine_restrict_annihilated I F hWU m hm
  let b := (idealModule I).presheaf.map (homOfLE hWV).op a
  have hb : scalar I W b ∈ I.ideal ⟨W, hW⟩ := by
    exact (Set.ext_iff.mp (idealModuleι_range I ⟨W, hW⟩) _).mp ⟨b, rfl⟩
  have hn : scalar I W b = X.presheaf.map (homOfLE hWV).op (scalar I V.left a) :=
    congr($((idealModuleι I).mapPresheaf.naturality (homOfLE hWV).op) a)
  refine ⟨W, hWV, hxW, ?_⟩
  rw [map_zero, Scheme.Modules.map_smul, ← hn]
  have he : F.presheaf.map (homOfLE hWV).op (F.presheaf.map V.hom.op m) =
      F.presheaf.map (homOfLE hWU).op m :=
    (congr($(F.presheaf.map_comp V.hom.op (homOfLE hWV).op) m)).symm
  rw [he]
  exact hk _ hb

/-- On every affine open the inclusion has exactly the annihilator as its image. -/
theorem affine_range (U : X.affineOpens) (m : Γ(F, U.1)) :
    m ∈ Set.range ((inclusion I F).app U.1) ↔
      m ∈ AffineAnnihilator.annihilated (I.ideal U) Γ(F, U.1) := by
  rw [mem_range_inclusion]
  constructor
  · intro h r hr
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp (idealModuleι_range I U) r).mpr hr
    have he := congrArg (fun φ ↦ ModuleSheafInternalHom.app (idealModule I) F
      φ (Over.mk (𝟙 U.1)) a) h
    change scalar I U.1 a • F.presheaf.map (𝟙 U.1).op m = 0 at he
    have hi : F.presheaf.map (𝟙 U.1).op m = m :=
      congr($(F.presheaf.map_id (op U.1)) m)
    rw [hi] at he
    simpa only [scalar, ha] using he
  · exact localAction_eq_zero_of_affine I F U m

/-- The affine section comparison is linear and uses the canonical section inclusion. -/
def affineSectionsEquiv (U : X.affineOpens) :
    Γ(sheaf I F, U.1) ≃ₗ[Γ(X, U.1)]
      AffineAnnihilator.annihilated (I.ideal U) Γ(F, U.1) :=
  LinearEquiv.trans (R₁ := Γ(X, U.1)) (R₂ := Γ(X, U.1)) (R₃ := Γ(X, U.1))
    (sectionsKernelIso I F U.1).toLinearEquiv (LinearEquiv.ofEq _ _ (by
    ext m
    exact (mem_range_inclusion I F U.1 m).symm.trans (affine_range I F U m)))

/-- The affine comparison preserves the original ambient section. -/
@[simp]
lemma affineSectionsEquiv_val (U : X.affineOpens) (m : Γ(sheaf I F, U.1)) :
    (affineSectionsEquiv I F U m).val = (inclusion I F).app U.1 m :=
  sectionsKernelIso_val I F U.1 m

/-- Canonical affine section inclusions determine the overlap coherence. -/
theorem affineSectionsEquiv_restrict {U V : X.affineOpens} (h : V ≤ U)
    (m : Γ(sheaf I F, U.1)) :
    (affineSectionsEquiv I F V ((sheaf I F).presheaf.map (homOfLE h).op m)).val =
      F.presheaf.map (homOfLE h).op (affineSectionsEquiv I F U m).val := by
  simp only [affineSectionsEquiv_val]
  exact congr($((inclusion I F).mapPresheaf.naturality
    (homOfLE (show V.1 ≤ U.1 from h)).op) m)

/-- The actual affine sections of the annihilator are finitely presented. -/
theorem affineSections_finitePresentation [IsLocallyNoetherian X] [F.IsFinitePresentation]
    (U : X.affineOpens) : Module.FinitePresentation Γ(X, U.1) Γ(sheaf I F, U.1) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite Γ(X, U.1) Γ(F, U.1) := coherentAffineOpen_sections_finite F U.2
  have := AffineAnnihilator.annihilated_finitePresentation (M := Γ(F, U.1)) (I.ideal U)
  exact Module.FinitePresentation.of_equiv (affineSectionsEquiv I F U).symm

end FLT.Mazur.AnnihilatorSubsheaf
