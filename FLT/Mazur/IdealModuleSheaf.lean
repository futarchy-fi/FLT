/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The module sheaf of an ideal

The ideal module is the kernel of the map from the structure sheaf to the
pushforward of the structure sheaf of its closed subscheme. Evaluation preserves
kernels, and the affine kernel calculation identifies its sections with the given ideals.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}}

/-- The structure sheaf, regarded as a sheaf of modules over itself. -/
def structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The canonical map to the structure module of a closed subscheme. -/
def idealQuotientMap (I : X.IdealSheafData) :
    structureModule X ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
      (structureModule I.subscheme) :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (I.subschemeι.app U.unop).hom.toAddMonoidHom
      naturality := fun _ _ f ↦ by
        ext x
        exact congr($(I.subschemeι.naturality f) x) }
    (fun U r m ↦ (I.subschemeι.app U.unop).hom.map_mul r m)⟩

/-- The module sheaf constructed from the actual ideal data. -/
def idealModule (I : X.IdealSheafData) : X.Modules :=
  kernel (idealQuotientMap I)

/-- The canonical inclusion into the structure module. -/
def idealModuleι (I : X.IdealSheafData) : idealModule I ⟶ structureModule X :=
  kernel.ι (idealQuotientMap I)

instance idealModuleSheafInst1 (I : X.IdealSheafData) : Mono (idealModuleι I) :=
  inferInstanceAs (Mono (kernel.ι (idealQuotientMap I)))

/-- Evaluation of the ideal module is the kernel of the map on sections. -/
def idealModuleKernelIso (I : X.IdealSheafData) (U : X.Opens) :
    (idealModule I).val.obj (op U) ≅
      ModuleCat.of Γ(X, U) ((idealQuotientMap I).val.app (op U)).hom.ker :=
  PreservesKernel.iso (SheafOfModules.evaluation.{u} X.ringCatSheaf (op U))
    (idealQuotientMap I) ≪≫ ModuleCat.kernelIsoKer _

/-- On an affine open, the kernel on sections is the specified ideal. -/
lemma idealQuotientMap_ker (I : X.IdealSheafData) (U : X.affineOpens) :
    ((idealQuotientMap I).val.app (op U.1)).hom.ker = I.ideal U := by
  ext r
  change (I.subschemeι.app U.1) r = 0 ↔ r ∈ I.ideal U
  rw [← I.ker_subschemeι_app U]
  rfl

/-- The canonical linear identification of affine sections with the given ideal. -/
def idealModuleAffineEquiv (I : X.IdealSheafData) (U : X.affineOpens) :
    Γ(idealModule I, U.1) ≃ₗ[Γ(X, U.1)] I.ideal U :=
  LinearEquiv.trans (R₁ := Γ(X, U.1)) (R₂ := Γ(X, U.1)) (R₃ := Γ(X, U.1))
    (idealModuleKernelIso I U.1).toLinearEquiv
    (LinearEquiv.ofEq _ _ (idealQuotientMap_ker I U))

/-- The affine identification commutes with inclusion into the structure sheaf. -/
@[simp]
lemma idealModuleAffineEquiv_val (I : X.IdealSheafData) (U : X.affineOpens)
    (s : Γ(idealModule I, U.1)) :
    (idealModuleAffineEquiv I U s).val = (idealModuleι I).app U.1 s := by
  change ((idealModuleKernelIso I U.1).hom s).val = _
  have h : (idealModuleKernelIso I U.1).hom ≫
      ModuleCat.ofHom ((idealQuotientMap I).val.app (op U.1)).hom.ker.subtype =
        (idealModuleι I).val.app (op U.1) := by
    dsimp only [idealModuleKernelIso, Iso.trans_hom]
    erw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
    rfl
  exact congr($(h) s)

/-- Restriction of an affine ideal section, with its natural semilinear structure. -/
def idealRestrict (I : X.IdealSheafData) {U V : X.affineOpens} (h : U ≤ V) :
    I.ideal V →ₛₗ[(X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom] I.ideal U :=
  ((X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom.toSemilinearMap).restrict
    (fun _ hs ↦ I.ideal_le_comap_ideal h hs)

@[simp]
lemma idealRestrict_val (I : X.IdealSheafData) {U V : X.affineOpens} (h : U ≤ V)
    (s : I.ideal V) :
    (idealRestrict I h s).val = X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op s.val := rfl

/-- The affine section identifications intertwine the actual sheaf restrictions. -/
lemma idealModuleAffineEquiv_restrict (I : X.IdealSheafData)
    {U V : X.affineOpens} (h : U ≤ V) (s : Γ(idealModule I, V.1)) :
    idealModuleAffineEquiv I U
        ((idealModule I).presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op s) =
      idealRestrict I h (idealModuleAffineEquiv I V s) := by
  apply Subtype.ext
  simp only [idealModuleAffineEquiv_val, idealRestrict_val]
  exact congr($((idealModuleι I).val.naturality (homOfLE (show U.1 ≤ V.1 from h)).op) s)

/-- The inclusion on affine sections has image precisely the specified ideal. -/
lemma idealModuleι_range (I : X.IdealSheafData) (U : X.affineOpens) :
    Set.range ((idealModuleι I).app U.1) = (I.ideal U : Set Γ(X, U.1)) := by
  ext r
  constructor
  · rintro ⟨s, rfl⟩
    rw [← idealModuleAffineEquiv_val]
    exact (idealModuleAffineEquiv I U s).property
  · intro hr
    refine ⟨(idealModuleAffineEquiv I U).symm ⟨r, hr⟩, ?_⟩
    rw [← idealModuleAffineEquiv_val, LinearEquiv.apply_symm_apply]

/-- The restricted sheaf sections generate the target ideal, realizing `map_ideal`. -/
lemma idealModule_restrict_span (I : X.IdealSheafData) {U V : X.affineOpens}
    (h : U ≤ V) :
    Ideal.span (α := Γ(X, U.1)) (Set.range fun s : Γ(idealModule I, V.1) ↦
      (idealModuleι I).app U.1
        ((idealModule I).presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op s)) =
      I.ideal U := by
  have hres (s : Γ(idealModule I, V.1)) :
      (idealModuleι I).app U.1
          ((idealModule I).presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op s) =
        X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op
          ((idealModuleι I).app V.1 s) :=
    congr($((idealModuleι I).val.naturality (homOfLE (show U.1 ≤ V.1 from h)).op) s)
  simp only [hres, Set.range_comp', idealModuleι_range]
  exact I.map_ideal h

/-- The quotient map for the unit ideal vanishes. -/
@[simp]
lemma idealQuotientMap_top : idealQuotientMap (⊤ : X.IdealSheafData) = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change (⊤ : X.IdealSheafData).subschemeι.app U s = 0
  exact Subsingleton.elim _ _

instance idealModuleSheafInst2 : IsIso (idealModuleι (⊤ : X.IdealSheafData)) :=
  kernel.ι_of_zero idealQuotientMap_top

/-- The unit ideal gives the structure module, via its canonical inclusion. -/
def idealModuleTopIso : idealModule (⊤ : X.IdealSheafData) ≅ structureModule X :=
  asIso (idealModuleι ⊤)

@[simp]
lemma idealModuleTopIso_hom :
    (idealModuleTopIso (X := X)).hom = idealModuleι ⊤ := rfl

end FLT.Mazur.FCurve
