/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleSheaf
public import FLT.Mazur.DivisorRestrictCoherence

/-!
# Restriction of divisor line bundles

The comparison of ideal modules is characterized by their inclusions in the
structure module. Duality then compares the actual positive divisor sheaves.
Affine evaluation agrees with dual-ideal transport. The comparisons on nested
opens satisfy the identity and composition constraints for module restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X Y : Scheme.{u}}

/-- Morphisms of module sheaves agree if they agree on all affine opens. -/
lemma moduleHom_ext_affine {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ U : X.affineOpens, f.app U.1 = g.app U.1) : f = g := by
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply CategoryTheory.Sheaf.hom_ext
  apply (TopCat.Sheaf.restrictHomEquivHom _ _
    (B := fun U : X.affineOpens ↦ U.1) (by simpa using X.isBasis_affineOpens)).symm.injective
  ext U : 2
  exact h U.unop

/-- The restricted ideal inclusion, with values in the structure module of the source. -/
def idealModuleRestrictι (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (idealModule I).restrict f ⟶ structureModule X :=
  (Scheme.Modules.restrictFunctor f).map (idealModuleι I) ≫
    (Scheme.Modules.restrictUnitIso f).hom

lemma idealModuleRestrictι_app (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) (s : Γ((idealModule I).restrict f, U)) :
    (idealModuleRestrictι I f).app U s =
      (f.appIso U).hom ((idealModuleι I).app (f ''ᵁ U) s) := rfl

/-- The restricted ideal inclusion vanishes in the quotient by the pulled-back ideal. -/
lemma idealModuleRestrictι_quotient (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] :
    idealModuleRestrictι I f ≫ idealQuotientMap (I.comap f) = 0 := by
  apply moduleHom_ext_affine
  intro U
  ext s
  change (idealModuleRestrictι I f).app U.1 s ∈
    ((idealQuotientMap (I.comap f)).val.app (op U.1)).hom.ker
  rw [idealQuotientMap_ker, I.ideal_comap_of_isOpenImmersion]
  change (f.appIso U.1).inv ((f.appIso U.1).hom
    ((idealModuleι I).app (f ''ᵁ U.1) s)) ∈
      I.ideal ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  rw [Iso.hom_inv_id_apply]
  rw [← idealModuleAffineEquiv_val I ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩]
  exact (idealModuleAffineEquiv I
    ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩ s).property

/-- Restriction maps the actual ideal module to the module of the restricted ideal. -/
def idealModuleRestrictHom (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (idealModule I).restrict f ⟶ idealModule (I.comap f) :=
  kernel.lift _ (idealModuleRestrictι I f) (idealModuleRestrictι_quotient I f)

@[reassoc (attr := simp)]
lemma idealModuleRestrictHom_ι (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] :
    idealModuleRestrictHom I f ≫ idealModuleι (I.comap f) = idealModuleRestrictι I f :=
  kernel.lift_ι _ _ _

/-- The comparison on affine sections is the canonical map of the actual ideals. -/
lemma idealModuleRestrictHom_affine (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.affineOpens) (s : Γ((idealModule I).restrict f, U.1)) :
    (idealModuleAffineEquiv (I.comap f) U ((idealModuleRestrictHom I f).app U.1 s)).val =
      (f.appIso U.1).hom
        (idealModuleAffineEquiv I ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩ s).val := by
  erw [idealModuleAffineEquiv_val, idealModuleAffineEquiv_val]
  exact congr($(idealModuleRestrictHom_ι I f).app U.1 s)

/-- On every affine open the ideal comparison is bijective. -/
lemma idealModuleRestrictHom_bijective (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.affineOpens) :
    Function.Bijective ((idealModuleRestrictHom I f).app U.1) := by
  let V : Y.affineOpens := ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  constructor
  · intro s t h
    apply (idealModuleAffineEquiv I V).injective
    apply Subtype.ext
    apply (ConcreteCategory.bijective_of_isIso (f.appIso U.1).hom).injective
    have he := congrArg (fun z ↦ (idealModuleAffineEquiv (I.comap f) U z).val) h
    rw [idealModuleRestrictHom_affine, idealModuleRestrictHom_affine] at he
    exact he
  · intro t
    let r := idealModuleAffineEquiv (I.comap f) U t
    have hr : (f.appIso U.1).inv r.val ∈ I.ideal V := by
      have := r.property
      simpa only [I.ideal_comap_of_isOpenImmersion, Ideal.mem_comap] using this
    refine ⟨(idealModuleAffineEquiv I V).symm ⟨(f.appIso U.1).inv r.val, hr⟩, ?_⟩
    apply (idealModuleAffineEquiv (I.comap f) U).injective
    apply Subtype.ext
    rw [idealModuleRestrictHom_affine, LinearEquiv.apply_symm_apply]
    exact Iso.inv_hom_id_apply (f.appIso U.1) r.val

instance idealModuleRestrictHom_isIso (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] : IsIso (idealModuleRestrictHom I f) := by
  let φ := (SheafOfModules.toSheaf X.ringCatSheaf).map (idealModuleRestrictHom I f)
  have hφ : IsIso φ := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun U : X.affineOpens ↦ U.1) (by simpa using X.isBasis_affineOpens)
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    exact idealModuleRestrictHom_bijective I f U
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  exact inferInstanceAs (IsIso (φ.hom.app (op U)))

/-- Restriction of the actual ideal module is the module of the restricted divisor. -/
def idealModuleRestrictIso (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (idealModule I).restrict f ≅ idealModule (I.comap f) :=
  asIso (idealModuleRestrictHom I f)

/-- The positive divisor sheaf commutes with restriction to any open subscheme. -/
def divisorLineBundleRestrictIso (I : X.IdealSheafData) (hI : EffectiveCartier I)
    (U : X.Opens) : (divisorLineBundle I hI).restrict U.ι ≅
      divisorLineBundle (I.comap U.ι) (hI.comap_of_isOpenImmersion U.ι) :=
  moduleSheafDualRestrictIso (idealModule I) U ≪≫
    (moduleSheafDualIso _ (idealModuleRestrictIso I U.ι)).symm

/-- Section morphisms are natural in the module sheaf. -/
lemma sectionHom_comp {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) (s : Γ(M, U)) :
    sectionHom M U s ≫ (Scheme.Modules.restrictFunctor U.ι).map f =
      sectionHom N U (f.app U s) := by
  apply Scheme.Modules.hom_ext
  intro W
  ext r
  simp only [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply, sectionHom_app]
  erw [Scheme.Modules.smul_apply, Scheme.Modules.Hom.app_smul]
  congr 1
  exact congr($(f.val.naturality (homOfLE (U.ι_image_le W)).op) s)

/-- Evaluation of a dual map is precomposition on the section being paired. -/
lemma moduleDualEval_precomp {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (φ : ModuleDualSections N U) (s : Γ(M, U)) :
    moduleDualEval M U ((Scheme.Modules.restrictFunctor U.ι).map f ≫ φ) s =
      moduleDualEval N U φ (f.app U s) := by
  apply sectionHom_injective (structureModule X) U
  apply (cancel_mono (Scheme.Modules.restrictUnitIso U.ι).hom).mp
  rw [← moduleDualEval_sectionHom, ← moduleDualEval_sectionHom,
    ← Category.assoc, sectionHom_comp]

/-- Open restriction preserves the evaluation pairing. -/
lemma moduleDualOpenSectionsEquiv_eval (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) (φ : ModuleDualSections M (U.ι ''ᵁ W))
    (s : Γ(M, U.ι ''ᵁ W)) :
    moduleDualEval (M.restrict U.ι) W (moduleDualOpenSectionsEquiv M U W φ) s =
      moduleDualEval M (U.ι ''ᵁ W) φ s := by
  obtain ⟨φ, rfl⟩ := (moduleDualSectionsEquiv M (U.ι ''ᵁ W)).surjective φ
  simp only [moduleDualOpenSectionsEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    moduleDualEval]
  rfl

/-- The canonical comparison preserves evaluation against the actual ideal sections. -/
lemma divisorLineBundleRestrictIso_eval (I : X.IdealSheafData) (hI : EffectiveCartier I)
    (U : X.Opens) (W : U.toScheme.Opens)
    (φ : Γ((divisorLineBundle I hI).restrict U.ι, W))
    (s : Γ((idealModule I).restrict U.ι, W)) :
    moduleDualEval (idealModule (I.comap U.ι)) W
        ((divisorLineBundleRestrictIso I hI U).hom.app W φ)
        ((idealModuleRestrictIso I U.ι).hom.app W s) =
      moduleDualEval (idealModule I) (U.ι ''ᵁ W) φ s := by
  change moduleDualEval (idealModule (I.comap U.ι)) W
    ((Scheme.Modules.restrictFunctor W.ι).map (idealModuleRestrictIso I U.ι).inv ≫
      moduleDualOpenSectionsEquiv (idealModule I) U W φ) _ = _
  rw [moduleDualEval_precomp]
  have he := congr($((idealModuleRestrictIso I U.ι).hom_inv_id).app W s)
  change (idealModuleRestrictIso I U.ι).inv.app W
    ((idealModuleRestrictIso I U.ι).hom.app W s) = s at he
  rw [he]
  exact moduleDualOpenSectionsEquiv_eval (idealModule I) U W φ s

/-- On affine charts the line-bundle comparison is the canonical dual-ideal comparison. -/
lemma divisorLineBundleRestrictIso_chartEval (I : X.IdealSheafData)
    (hI : EffectiveCartier I) (U : X.Opens) (W : U.toScheme.affineOpens)
    (φ : Γ((divisorLineBundle I hI).restrict U.ι, W.1))
    (s : Γ((idealModule I).restrict U.ι, W.1)) :
    divisorChartEval (I.comap U.ι) W ((divisorLineBundleRestrictIso I hI U).hom.app W.1 φ)
        (idealModuleAffineEquiv (I.comap U.ι) W
          ((idealModuleRestrictIso I U.ι).hom.app W.1 s)) =
      divisorChartEval I ⟨U.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion U.ι⟩ φ
        (idealModuleAffineEquiv I ⟨U.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion U.ι⟩ s) := by
  simp only [divisorChartEval, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact divisorLineBundleRestrictIso_eval I hI U W.1 φ s

/-- The sheaf comparison induces the established affine dual-ideal transport. -/
lemma divisorLineBundleRestrictIso_chartTransport (I : X.IdealSheafData)
    (hI : EffectiveCartier I) (U : X.Opens) (W : U.toScheme.affineOpens)
    (φ : Γ((divisorLineBundle I hI).restrict U.ι, W.1)) :
    divisorChartEval (I.comap U.ι) W ((divisorLineBundleRestrictIso I hI U).hom.app W.1 φ) =
      divisorChartTransport I U.ι W
        (divisorChartEval I ⟨U.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion U.ι⟩ φ) := by
  ext t
  obtain ⟨s, rfl⟩ := (idealModuleAffineEquiv (I.comap U.ι) W).surjective t
  obtain ⟨s, rfl⟩ :=
    (ConcreteCategory.bijective_of_isIso ((idealModuleRestrictIso I U.ι).hom.app W.1)).surjective s
  rw [divisorLineBundleRestrictIso_chartEval]
  have he := idealModuleRestrictHom_affine I U.ι W s
  have ht : idealModuleAffineEquiv (I.comap U.ι) W
      ((idealModuleRestrictIso I U.ι).hom.app W.1 s) =
        CartierModule.idealRestrict _ _ _ (ideal_map_appIso I U.ι W).le
          (idealModuleAffineEquiv I ⟨U.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion U.ι⟩ s) :=
    Subtype.ext he
  rw [ht, divisorChartTransport_apply]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
  rfl

lemma moduleRestrict_map_app {M N : Y.Modules} (f : X ⟶ Y) [IsOpenImmersion f]
    (a : M ⟶ N) (U : X.Opens) :
    ((Scheme.Modules.restrictFunctor f).map a).app U = a.app (f ''ᵁ U) := rfl

/-- Compare successive restrictions to nested open subschemes. -/
def moduleRestrictLEIso (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    (M.restrict U.ι).restrict (X.homOfLE h) ≅ M.restrict V.ι :=
  ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M

lemma moduleRestrictLEIso_hom_app (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (W : V.toScheme.Opens) :
    (moduleRestrictLEIso M h).hom.app W =
      M.presheaf.map (eqToHom (show V.ι ''ᵁ W = U.ι ''ᵁ X.homOfLE h ''ᵁ W by
        simp [← Scheme.Hom.comp_image])).op := by
  simp only [moduleRestrictLEIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, ← Functor.map_comp]
  rfl

/-- Successive restriction to the same open is the identity constraint. -/
lemma moduleRestrictLEIso_id (M : X.Modules) (U : X.Opens) :
    (moduleRestrictLEIso M (le_refl U)).hom =
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_rfl U)).hom.app (M.restrict U.ι) ≫
        Scheme.Modules.restrictFunctorId.hom.app (M.restrict U.ι) := by
  apply Scheme.Modules.hom_ext
  intro W
  rw [moduleRestrictLEIso_hom_app]
  simp only [Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorId_hom_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, ← Functor.map_comp]
  rfl

/-- The restriction comparisons respect composition of open inclusions. -/
lemma moduleRestrictLEIso_comp (M : X.Modules) {U V W : X.Opens}
    (h : V ≤ U) (k : W ≤ V) :
    (Scheme.Modules.restrictFunctorComp (X.homOfLE k) (X.homOfLE h)).hom.app
        (M.restrict U.ι) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE k)).map (moduleRestrictLEIso M h).hom ≫
        (moduleRestrictLEIso M k).hom =
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_homOfLE k h)).hom.app
        (M.restrict U.ι) ≫ (moduleRestrictLEIso M (k.trans h)).hom := by
  apply Scheme.Modules.hom_ext
  intro Z
  simp only [Scheme.Modules.Hom.comp_app, moduleRestrict_map_app,
    moduleRestrictLEIso_hom_app, Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, Scheme.Modules.restrict_map,
    ← Functor.map_comp]
  rfl

/-- The actual divisor line bundle on an open subscheme. -/
abbrev divisorLineBundleOn (I : X.IdealSheafData) (hI : EffectiveCartier I) (U : X.Opens) :=
  divisorLineBundle (I.comap U.ι) (hI.comap_of_isOpenImmersion U.ι)

/-- Canonical comparison between the divisor line bundles on nested opens. -/
def divisorLineBundleRestrictLEIso (I : X.IdealSheafData) (hI : EffectiveCartier I)
    {U V : X.Opens} (h : V ≤ U) :
    (divisorLineBundleOn I hI U).restrict (X.homOfLE h) ≅ divisorLineBundleOn I hI V :=
  (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso
      (divisorLineBundleRestrictIso I hI U).symm ≪≫
    moduleRestrictLEIso (divisorLineBundle I hI) h ≪≫ divisorLineBundleRestrictIso I hI V

/-- The open comparison intertwines restriction with the nested-open comparison. -/
@[reassoc]
lemma divisorLineBundleRestrictLEIso_naturality (I : X.IdealSheafData)
    (hI : EffectiveCartier I) {U V : X.Opens} (h : V ≤ U) :
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        (divisorLineBundleRestrictIso I hI U).hom ≫
      (divisorLineBundleRestrictLEIso I hI h).hom =
        (moduleRestrictLEIso (divisorLineBundle I hI) h).hom ≫
          (divisorLineBundleRestrictIso I hI V).hom := by
  simp [divisorLineBundleRestrictLEIso, ← Functor.map_comp_assoc]

/-- Identity compatibility for the actual divisor line bundles on opens. -/
lemma divisorLineBundleRestrictLEIso_id (I : X.IdealSheafData)
    (hI : EffectiveCartier I) (U : X.Opens) :
    (divisorLineBundleRestrictLEIso I hI (le_refl U)).hom =
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_rfl U)).hom.app
          (divisorLineBundleOn I hI U) ≫
        Scheme.Modules.restrictFunctorId.hom.app (divisorLineBundleOn I hI U) := by
  apply (cancel_epi ((Scheme.Modules.restrictFunctor (X.homOfLE (le_refl U))).map
    (divisorLineBundleRestrictIso I hI U).hom)).mp
  rw [divisorLineBundleRestrictLEIso_naturality]
  rw [(Scheme.Modules.restrictFunctorCongr (X.homOfLE_rfl U)).hom.naturality_assoc,
    Scheme.Modules.restrictFunctorId.hom.naturality]
  rw [moduleRestrictLEIso_id, Category.assoc]
  rfl

/-- Composition compatibility for the actual divisor line bundles on opens. -/
lemma divisorLineBundleRestrictLEIso_comp (I : X.IdealSheafData)
    (hI : EffectiveCartier I) {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) :
    (Scheme.Modules.restrictFunctorComp (X.homOfLE k) (X.homOfLE h)).hom.app
        (divisorLineBundleOn I hI U) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE k)).map
          (divisorLineBundleRestrictLEIso I hI h).hom ≫
        (divisorLineBundleRestrictLEIso I hI k).hom =
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_homOfLE k h)).hom.app
          (divisorLineBundleOn I hI U) ≫
        (divisorLineBundleRestrictLEIso I hI (k.trans h)).hom := by
  apply (cancel_epi ((Scheme.Modules.restrictFunctor
    (X.homOfLE k ≫ X.homOfLE h)).map (divisorLineBundleRestrictIso I hI U).hom)).mp
  rw [(Scheme.Modules.restrictFunctorComp (X.homOfLE k)
    (X.homOfLE h)).hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, divisorLineBundleRestrictLEIso_naturality]
  rw [Functor.map_comp, Category.assoc, divisorLineBundleRestrictLEIso_naturality]
  rw [(Scheme.Modules.restrictFunctorCongr
    (X.homOfLE_homOfLE k h)).hom.naturality_assoc]
  rw [divisorLineBundleRestrictLEIso_naturality]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ t ≫ (divisorLineBundleRestrictIso I hI W).hom)
    (moduleRestrictLEIso_comp (divisorLineBundle I hI) h k)

end FLT.Mazur.FCurve
