/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorInvertibleSheaf
public import FLT.Mazur.ModuleSheafDualSheaf

/-!
# The line bundle of an effective Cartier divisor

The positive divisor sheaf is the intrinsic dual of the actual ideal module.
Evaluation identifies its Cartier-chart sections with the dual ideal modules.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}}

/-- Evaluate a local sheaf morphism on an actual section of its domain. -/
def moduleDualEval (M : X.Modules) (U : X.Opens) (φ : ModuleDualSections M U) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun s := moduleDualHomApp M ((moduleDualSectionsEquiv M U).symm φ).1 (Over.mk (𝟙 U)) s
  map_add' := map_add _
  map_smul' r s := ((moduleDualSectionsEquiv M U).symm φ).2 (Over.mk (𝟙 U)) r s

lemma moduleDualEval_add (M : X.Modules) (U : X.Opens)
    (φ ψ : ModuleDualSections M U) :
    moduleDualEval M U (φ + ψ) = moduleDualEval M U φ + moduleDualEval M U ψ := by
  obtain ⟨φ, rfl⟩ := (moduleDualSectionsEquiv M U).surjective φ
  obtain ⟨ψ, rfl⟩ := (moduleDualSectionsEquiv M U).surjective ψ
  rw [← moduleDualSectionsEquiv_add]
  ext s
  simp only [moduleDualEval, Equiv.symm_apply_apply]
  rfl

lemma moduleDualEval_smul (M : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (φ : ModuleDualSections M U) :
    moduleDualEval M U (r • φ) = r • moduleDualEval M U φ := by
  obtain ⟨φ, rfl⟩ := (moduleDualSectionsEquiv M U).surjective φ
  rw [← moduleDualSectionsEquiv_smul]
  ext s
  simp only [moduleDualEval, Equiv.symm_apply_apply]
  change X.presheaf.map (𝟙 U).op r * _ = r * _
  simp

/-- Evaluation commutes with restriction of both arguments. -/
lemma moduleDualEval_restrict (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (φ : ModuleDualSections M U) (s : Γ(M, U)) :
    moduleDualEval M V (moduleDualRestrict M h φ)
        (M.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (moduleDualEval M U φ s) := by
  obtain ⟨φ, rfl⟩ := (moduleDualSectionsEquiv M U).surjective φ
  rw [← moduleDualSectionsEquiv_restrict]
  let g : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U) := Over.homMk (homOfLE h)
  have hn := congr($(φ.1.naturality g.op) s)
  change φ.1.app (op (Over.mk (homOfLE h))) (M.presheaf.map (homOfLE h).op s) =
    X.presheaf.map (homOfLE h).op (φ.1.app (op (Over.mk (𝟙 U))) s) at hn
  simp only [moduleDualEval, Equiv.symm_apply_apply, moduleDualHomApp]
  exact hn

/-- The identity map on every subopen, in the linear local Hom model. -/
def moduleDualUnitLinear (U : X.Opens) :
    (moduleDualLinearHom (structureModule X)).obj (op U) :=
  ⟨𝟙 _, fun _ _ _ ↦ rfl⟩

/-- Local multiplication by a function as a dual section of the unit module. -/
def moduleDualUnitSection (U : X.Opens) (r : Γ(X, U)) :
    ModuleDualSections (structureModule X) U :=
  moduleDualSectionsEquiv (structureModule X) U
    (moduleDualLinearSMul (structureModule X) r (moduleDualUnitLinear U))

lemma moduleDualEval_unitSection (U : X.Opens) (r s : Γ(X, U)) :
    moduleDualEval (structureModule X) U (moduleDualUnitSection U r) s = r * s := by
  simp only [moduleDualUnitSection, moduleDualEval, Equiv.symm_apply_apply]
  change X.presheaf.map (𝟙 U).op r * s = r * s
  simp

/-- A local endomorphism of the structure module is multiplication by its value at one. -/
lemma moduleDualUnitSection_eval (U : X.Opens)
    (φ : ModuleDualSections (structureModule X) U) :
    moduleDualUnitSection U (moduleDualEval (structureModule X) U φ (1 : Γ(X, U))) = φ := by
  obtain ⟨φ, rfl⟩ := (moduleDualSectionsEquiv (structureModule X) U).surjective φ
  apply (moduleDualSectionsEquiv (structureModule X) U).symm.injective
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  ext s
  let g : V.unop ⟶ Over.mk (𝟙 U) := Over.homMk V.unop.hom
  have hn := congr($(φ.1.naturality g.op) (1 : Γ(X, U)))
  change Γ(X, V.unop.left) at s
  have hl := φ.2 V.unop s (1 : Γ(X, V.unop.left))
  let F : Γ(X, V.unop.left) →+ Γ(X, V.unop.left) := (φ.1.app V).hom
  simp only [moduleDualUnitSection, Equiv.symm_apply_apply]
  change F (s * 1) = s * F 1 at hl
  simp only [mul_one] at hl
  change X.presheaf.map V.unop.hom.op _ * s = F s
  rw [hl, mul_comm]
  congr 1
  change φ.1.app V (X.presheaf.map V.unop.hom.op (1 : Γ(X, U))) =
    X.presheaf.map V.unop.hom.op (φ.1.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) at hn
  simp only [map_one] at hn
  simp only [moduleDualEval, Equiv.symm_apply_apply, moduleDualHomApp]
  exact hn.symm

/-- Evaluation at one identifies dual sections of the unit with functions. -/
def moduleDualUnitEquiv (U : X.Opens) :
    ModuleDualSections (structureModule X) U ≃ₗ[Γ(X, U)] Γ(X, U) where
  toFun φ := moduleDualEval (structureModule X) U φ (1 : Γ(X, U))
  invFun := moduleDualUnitSection U
  left_inv := moduleDualUnitSection_eval U
  right_inv r := (moduleDualEval_unitSection U r 1).trans (mul_one r)
  map_add' φ ψ := by erw [moduleDualEval_add]; rfl
  map_smul' r φ := by erw [moduleDualEval_smul]; rfl

/-- The dual of the structure module is canonically the structure module. -/
def moduleSheafDualUnitIso : moduleSheafDual (structureModule X) ≅ structureModule X := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ (moduleDualUnitEquiv U.unop).toModuleIso) ?_)
  intro U V f
  ext φ
  have h := moduleDualEval_restrict (structureModule X) (leOfHom f.unop) φ
    (1 : Γ(X, U.unop))
  change moduleDualEval (structureModule X) V.unop _
    (X.presheaf.map f (1 : Γ(X, U.unop))) = _ at h
  simp only [map_one] at h
  exact h

/-- Evaluation on restrictions of a section computes every component of its pairing. -/
lemma moduleDualEval_app (M : X.Modules) (U : X.Opens)
    (φ : ModuleDualSections M U) (s : Γ(M, U)) (W : U.toScheme.Opens) :
    φ.app W (M.presheaf.map (homOfLE (U.ι_image_le W)).op s) =
      X.presheaf.map (homOfLE (U.ι_image_le W)).op (moduleDualEval M U φ s) := by
  obtain ⟨φ, rfl⟩ := (moduleDualSectionsEquiv M U).surjective φ
  let V := U.overEquivalence.inverse.obj W
  let g : V ⟶ Over.mk (𝟙 U) := Over.homMk V.hom
  have hn := congr($(φ.1.naturality g.op) s)
  simp only [moduleDualEval, Equiv.symm_apply_apply, moduleDualHomApp]
  exact hn

/-- Composition with a section morphism is multiplication by its evaluation. -/
lemma moduleDualEval_sectionHom (M : X.Modules) (U : X.Opens)
    (φ : ModuleDualSections M U) (s : Γ(M, U)) :
    sectionHom M U s ≫ φ =
      sectionHom (structureModule X) U (moduleDualEval M U φ s) ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom := by
  apply Scheme.Modules.hom_ext
  intro W
  ext r
  simp only [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply, sectionHom_app]
  erw [Scheme.Modules.smul_apply, Scheme.Modules.Hom.app_smul]
  change Γ(U.toScheme, W) at r
  let a : Γ(U.toScheme, W) := φ.app W
    (M.presheaf.map (homOfLE (U.ι_image_le W)).op s)
  change r * a = (U.ι.appIso W).hom ((U.ι.appIso W).inv r *
      X.presheaf.map (homOfLE (U.ι_image_le W)).op (moduleDualEval M U φ s))
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom, Iso.refl_inv]
  exact congrArg (fun t : Γ(U.toScheme, W) ↦ r * t) (moduleDualEval_app M U φ s W)

/-- An actual section is determined by its associated morphism on the open subscheme. -/
lemma sectionHom_injective (M : X.Modules) (U : X.Opens) :
    Function.Injective (sectionHom M U) := by
  intro s t h
  have he := congr($(h).app (⊤ : U.toScheme.Opens) (1 : Γ(U.toScheme, ⊤)))
  simp only [sectionHom_app, Scheme.Modules.smul_apply, one_smul] at he
  let g : U.ι ''ᵁ ⊤ ⟶ U := eqToHom U.ι_image_top
  have : IsIso g := by dsimp [g]; infer_instance
  exact (ConcreteCategory.bijective_of_isIso (M.presheaf.map g.op)).injective he

/-- Evaluation at a trivializing section is bijective. -/
lemma moduleDualEval_bijective (M : X.Modules) (U : X.Opens) (s : Γ(M, U))
    [IsIso (sectionHom M U s)] : Function.Bijective (fun φ ↦ moduleDualEval M U φ s) := by
  constructor
  · intro φ ψ h
    apply (cancel_epi (sectionHom M U s)).mp
    rw [moduleDualEval_sectionHom M U φ s, moduleDualEval_sectionHom M U ψ s]
    exact congrArg (fun r ↦ sectionHom (structureModule X) U r ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) h
  · intro r
    let φ : ModuleDualSections M U := inv (sectionHom M U s) ≫
      sectionHom (structureModule X) U r ≫ (Scheme.Modules.restrictUnitIso U.ι).hom
    refine ⟨φ, sectionHom_injective (structureModule X) U ?_⟩
    apply (cancel_mono (Scheme.Modules.restrictUnitIso U.ι).hom).mp
    rw [← moduleDualEval_sectionHom]
    simp [φ]

/-- The intrinsic positive divisor sheaf. -/
def divisorLineBundle (I : X.IdealSheafData) (_hI : EffectiveCartier I) : X.Modules :=
  moduleSheafDual (idealModule I)

/-- The canonical pairing on actual affine ideal sections. -/
def divisorChartEval (I : X.IdealSheafData) (U : X.affineOpens) :
    ModuleDualSections (idealModule I) U.1 →ₗ[Γ(X, U)] divisorChartModule I U where
  toFun φ := (moduleDualEval (idealModule I) U.1 φ).comp
    (idealModuleAffineEquiv I U).symm.toLinearMap
  map_add' φ ψ := by rw [moduleDualEval_add]; rfl
  map_smul' r φ := by rw [moduleDualEval_smul]; rfl

/-- The Cartier trivialization makes the canonical pairing bijective. -/
lemma CartierChart.divisorChartEval_bijective {I : X.IdealSheafData}
    {U : X.affineOpens} (hU : CartierChart I U) :
    Function.Bijective (divisorChartEval I U) := by
  apply (Function.Bijective.of_comp_iff' hU.dualEquiv.bijective _).mp
  change Function.Bijective (fun φ ↦
    moduleDualEval (idealModule I) U.1 φ hU.idealSection)
  have : IsIso (sectionHom (idealModule I) U.1 hU.idealSection) :=
    inferInstanceAs (IsIso hU.idealTrivializationHom)
  exact moduleDualEval_bijective (idealModule I) U.1 hU.idealSection

/-- Sections of the divisor sheaf on a Cartier chart are the dual ideal module. -/
def CartierChart.divisorSectionsEquiv {I : X.IdealSheafData} {U : X.affineOpens}
    (hU : CartierChart I U) (hI : EffectiveCartier I) :
    Γ(divisorLineBundle I hI, U.1) ≃ₗ[Γ(X, U)] divisorChartModule I U :=
  LinearEquiv.ofBijective (divisorChartEval I U) hU.divisorChartEval_bijective

/-- The section comparison evaluates on the actual ideal section corresponding to its input. -/
lemma CartierChart.divisorSectionsEquiv_apply {I : X.IdealSheafData}
    {U : X.affineOpens} (hU : CartierChart I U) (hI : EffectiveCartier I)
    (φ : Γ(divisorLineBundle I hI, U.1)) (s : I.ideal U) :
    hU.divisorSectionsEquiv hI φ s =
      moduleDualEval (idealModule I) U.1 φ ((idealModuleAffineEquiv I U).symm s) := rfl

/-- The affine evaluation pairing commutes with both sheaf restrictions. -/
lemma divisorChartEval_restrict (I : X.IdealSheafData) {U V : X.affineOpens}
    (h : U ≤ V) (φ : ModuleDualSections (idealModule I) V.1) (s : I.ideal V) :
    divisorChartEval I U (moduleDualRestrict (idealModule I) h φ)
        (CartierModule.idealRestrict _ _ _ (I.map_ideal h).le s) =
      X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op (divisorChartEval I V φ s) := by
  have he : (idealModuleAffineEquiv I U).symm
      (CartierModule.idealRestrict _ _ _ (I.map_ideal h).le s) =
        (idealModule I).presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op
          ((idealModuleAffineEquiv I V).symm s) := by
    apply (idealModuleAffineEquiv I U).injective
    rw [LinearEquiv.apply_symm_apply, idealModuleAffineEquiv_restrict I h,
      LinearEquiv.apply_symm_apply]
    rfl
  exact (congrArg (moduleDualEval (idealModule I) U.1
    (moduleDualRestrict (idealModule I) h φ)) he).trans
      (moduleDualEval_restrict (idealModule I) h φ ((idealModuleAffineEquiv I V).symm s))

/-- Under the chart comparisons, sheaf restriction is the canonical dual ideal restriction. -/
lemma CartierChart.divisorSectionsEquiv_restrict {I : X.IdealSheafData}
    {U V : X.affineOpens} (hV : CartierChart I V) (hU : CartierChart I U)
    (hI : EffectiveCartier I) (h : U ≤ V) (φ : Γ(divisorLineBundle I hI, V.1)) :
    hU.divisorSectionsEquiv hI
        ((divisorLineBundle I hI).presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op φ) =
      hV.dualRestrict h (hV.divisorSectionsEquiv hI φ) := by
  let F : divisorChartModule I V →ₛₗ[(X.presheaf.map
      (homOfLE (show U.1 ≤ V.1 from h)).op).hom] divisorChartModule I U :=
    { toFun := fun f ↦ divisorChartEval I U
        (moduleDualRestrict (idealModule I) h ((hV.divisorSectionsEquiv hI).symm f))
      map_add' := fun f g ↦ by
        simp only [map_add]
        erw [moduleDualRestrict_add, map_add]
      map_smul' := fun r f ↦ by
        simp only [map_smul]
        erw [moduleDualRestrict_smul, map_smul] }
  have hF : F = hV.dualRestrict h := by
    apply CartierModule.dualRestrict_unique _ _ _ _ _ _ _ _ (I.map_ideal h).le
    intro f s
    change divisorChartEval I U _ _ = _
    rw [divisorChartEval_restrict]
    change X.presheaf.map _ ((hV.divisorSectionsEquiv hI)
      ((hV.divisorSectionsEquiv hI).symm f) s) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have he := congr($(hF) (hV.divisorSectionsEquiv hI φ))
  simp only [F, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply] at he
  exact he

/-- Dualizing a Cartier ideal trivialization trivializes the positive divisor sheaf. -/
def CartierChart.divisorTrivialization {I : X.IdealSheafData} {U : X.affineOpens}
    (hU : CartierChart I U) (hI : EffectiveCartier I) :
    (divisorLineBundle I hI).restrict U.1.ι ≅ structureModule U.1.toScheme :=
  moduleSheafDualRestrictIso (idealModule I) U.1 ≪≫
    (moduleSheafDualIso _ hU.idealTrivialization).symm ≪≫ moduleSheafDualUnitIso

/-- An effective Cartier divisor defines a locally free sheaf of rank one. -/
theorem EffectiveCartier.divisorLineBundle_locallyFreeRankOne {I : X.IdealSheafData}
    (hI : EffectiveCartier I) : LocallyFreeRankOne (divisorLineBundle I hI) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hI x
  exact ⟨U.1, hxU, ⟨CartierChart.divisorTrivialization hU hI⟩⟩

/-- The unit ideal defines the trivial line bundle. -/
def divisorLineBundleTopIso (hI : EffectiveCartier (⊤ : X.IdealSheafData)) :
    divisorLineBundle ⊤ hI ≅ structureModule X :=
  (moduleSheafDualIso _ idealModuleTopIso).symm ≪≫ moduleSheafDualUnitIso

end FLT.Mazur.FCurve
