/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoherentSubmoduleExtension
public import FLT.Mazur.CoherentSubquotient

/-!
# Coordinates for sections of a subsheaf on a principal open

The coordinates use the canonical affine counit and actual restriction maps.
The submodule is the range of the given inclusion on sections of its affine chart.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open CategoryTheory AlgebraicGeometry Opposite PrimeSpectrum
open Scheme.Modules

universe u

namespace FLT.Mazur.PrincipalSubmoduleCoordinates

variable {R : CommRingCat.{u}}

/-- Actual principal-open sections with scalars in the original ring. -/
abbrev sections (M : (Spec R).Modules) (f : R) : Type u := Γ(M, basicOpen f)

/-- Restriction of global sections to a principal open. -/
abbrev toSections (M : (Spec R).Modules) (f : R) :
    Γ(M, ⊤) →ₗ[R] sections M f :=
  ((modulesSpecToSheaf.obj M).presheaf.map
    (homOfLE (show basicOpen f ≤ ⊤ from le_top)).op).hom

instance toSections_isLocalized (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    IsLocalizedModule (.powers f) (toSections M f) :=
  (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance f

/-- The localized scalar action determined by restriction of global sections. -/
instance sectionsModule (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    Module (Localization.Away f) (sections M f) :=
  IsLocalizedModule.module (.powers f) (toSections M f)

instance sectionsScalarTower (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    IsScalarTower R (Localization.Away f) (sections M f) :=
  IsLocalizedModule.isScalarTower_module (.powers f) (toSections M f)

/-- Coordinates of actual sections in the localized global-section module. -/
def coordinates (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    sections M f ≃ₗ[Localization.Away f]
      LocalizedModule (.powers f) (moduleSpecΓFunctor.obj M) :=
  { (IsLocalizedModule.iso (.powers f) (toSections M f)).symm with
    map_smul' := (IsLocalization.linearMap_compatibleSMul (.powers f)
      (Localization.Away f) _ _).map_smul _ }

@[simp]
lemma coordinates_toSections (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : R) (m : moduleSpecΓFunctor.obj M) :
    coordinates M f (toSections M f m) = LocalizedModule.mk m 1 :=
  IsLocalizedModule.iso_symm_apply _ _ _

/-- The coordinate comparison is the canonical affine counit on sections. -/
lemma coordinates_counit (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    (x : TildePrincipalOpen.sections (moduleSpecΓFunctor.obj M) f) :
    coordinates M f ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op (basicOpen f)) x) =
      TildePrincipalOpen.sectionsEquiv (moduleSpecΓFunctor.obj M) f x := by
  let a := ((coordinates M f).restrictScalars R).toLinearMap.comp
    ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op (basicOpen f))).hom
  let b := ((TildePrincipalOpen.sectionsEquiv
    (moduleSpecΓFunctor.obj M) f).restrictScalars R).toLinearMap
  suffices a = b from DFunLike.congr_fun this x
  apply IsLocalizedModule.linearMap_ext (.powers f)
    (TildePrincipalOpen.toSections (moduleSpecΓFunctor.obj M) f)
    (LocalizedModule.mkLinearMap (.powers f) (moduleSpecΓFunctor.obj M))
  ext m
  have h := congrArg (fun a ↦ a.hom m) (M.toOpen_fromTildeΓ_app (basicOpen f))
  exact (congrArg (coordinates M f) h).trans
    ((coordinates_toSections M f m).trans
      (TildePrincipalOpen.sectionsEquiv_toSections _ f m).symm)

/-- Restriction in coordinates is the canonical map between localizations. -/
lemma coordinates_restriction (M : (Spec R).Modules) [M.IsQuasicoherent] (f g : R)
    (x : sections M f) :
    coordinates M (f * g)
        ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (basicOpen_mul_le_left f g)).op x) =
      TildePrincipalOpen.localizationRestriction (moduleSpecΓFunctor.obj M) f g
        (coordinates M f x) := by
  suffices h :
      ((coordinates M (f * g)).restrictScalars R).toLinearMap.comp
          ((modulesSpecToSheaf.obj M).presheaf.map
            (homOfLE (basicOpen_mul_le_left f g)).op).hom =
        (TildePrincipalOpen.localizationRestriction (moduleSpecΓFunctor.obj M) f g).comp
          ((coordinates M f).restrictScalars R).toLinearMap from DFunLike.congr_fun h x
  apply IsLocalizedModule.ext (.powers f) (toSections M f)
    (TildePrincipalOpen.localizationUnits (moduleSpecΓFunctor.obj M) f g)
  ext m
  change coordinates M (f * g)
    (((modulesSpecToSheaf.obj M).presheaf.map
      (homOfLE (basicOpen_mul_le_left f g)).op).hom (toSections M f m)) =
    TildePrincipalOpen.localizationRestriction (moduleSpecΓFunctor.obj M) f g
      (coordinates M f (toSections M f m))
  rw [coordinates_toSections, TildePrincipalOpen.localizationRestriction_mk]
  have h := congrArg (fun a ↦ a.hom m) ((modulesSpecToSheaf.obj M).presheaf.map_comp
    (basicOpen f).leTop.op (homOfLE (basicOpen_mul_le_left f g)).op)
  change toSections M (f * g) m = _ at h
  exact (congrArg (coordinates M (f * g)) h.symm).trans
    (coordinates_toSections M (f * g) m)

/-- The standard affine parametrization of a principal open. -/
abbrev principalMap (f : R) : Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))

/-- The same principal chart, with codomain a containing open subscheme. -/
def chart (U : (Spec R).Opens) (f : R) (hf : basicOpen f ≤ U) :
    Spec (CommRingCat.of (Localization.Away f)) ⟶ U :=
  (basicOpenIsoSpecAway f).inv ≫ (Spec R).homOfLE hf

instance chart_isOpenImmersion (U : (Spec R).Opens) (f : R) (hf : basicOpen f ≤ U) :
    IsOpenImmersion (chart U f hf) := by dsimp [chart]; infer_instance

@[simp]
lemma chart_comp (U : (Spec R).Opens) (f : R) (hf : basicOpen f ≤ U) :
    chart U f hf ≫ U.ι = principalMap f := by
  simp only [chart, Category.assoc, Scheme.homOfLE_ι]
  rw [← basicOpenIsoSpecAway_hom_SpecMap f, Iso.inv_hom_id_assoc]

/-- The canonical comparison for the two ways of restricting the ambient sheaf. -/
def chartRestrictIso (M : (Spec R).Modules) (U : (Spec R).Opens)
    (f : R) (hf : basicOpen f ≤ U) :
    (M.restrict U.ι).restrict (chart U f hf) ≅ M.restrict (principalMap f) :=
  ((restrictFunctorComp (chart U f hf) U.ι).symm ≪≫
    restrictFunctorCongr (chart_comp U f hf)).app M

/-- Restriction identifies chart sections with the actual sections on `D(f)`. -/
def chartSectionsIso (M : (Spec R).Modules) (f : R) :
    Γ(M.restrict (principalMap f), ⊤) ≅ Γ(M, basicOpen f) :=
  M.restrictAppIso (principalMap f) ⊤ ≪≫
    M.presheaf.mapIso (eqToIso (by simp [principalMap])).op

/-- Chart sections carry the canonical action of the localized affine coordinate ring. -/
local instance chartLocalizedModule (f : R)
    (N : (Spec (CommRingCat.of (Localization.Away f))).Modules)
    (V : (Spec (CommRingCat.of (Localization.Away f))).Opens) :
    Module (Localization.Away f) Γ(N, V) :=
  inferInstanceAs (Module (Localization.Away f)
    (((modulesSpecToSheaf (R := CommRingCat.of (Localization.Away f))).obj N).obj.obj (op V)))

/-- Restrict the scalars of chart sections along the principal localization map. -/
local instance chartBaseModule (f : R)
    (N : (Spec (CommRingCat.of (Localization.Away f))).Modules)
    (V : (Spec (CommRingCat.of (Localization.Away f))).Opens) : Module R Γ(N, V) :=
  Module.compHom _ (algebraMap R (Localization.Away f))

local instance chartBaseScalarTower (f : R)
    (N : (Spec (CommRingCat.of (Localization.Away f))).Modules)
    (V : (Spec (CommRingCat.of (Localization.Away f))).Opens) :
    IsScalarTower R (Localization.Away f) Γ(N, V) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The affine chart comparison is linear over the original coefficient ring. -/
def chartSectionsLinear (M : (Spec R).Modules) (f : R) :
    Γ(M.restrict (principalMap f), ⊤) →ₗ[R] sections M f where
  toFun := (chartSectionsIso M f).hom
  map_add' := map_add _
  map_smul' r x := by
    change M.presheaf.map _ ((M.restrictAppIso (principalMap f) ⊤).hom
      ((algebraMap R (Localization.Away f) r) • x)) = _
    exact (congrArg (fun z ↦ M.presheaf.map _ z)
      (AlgebraicGeometry.Scheme.Modules.restrictAppIso_smul_Spec (M := M)
        (CommRingCat.ofHom (algebraMap R (Localization.Away f))) r x)).trans
      (M.map_smul_Spec _ r _)

/-- Chart coordinates are linear over the localized coefficient ring. -/
def chartCoordinates (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    Γ(M.restrict (principalMap f), ⊤) →ₗ[Localization.Away f]
      LocalizedModule (.powers f) (moduleSpecΓFunctor.obj M) :=
  { ((coordinates M f).restrictScalars R).toLinearMap.comp (chartSectionsLinear M f) with
    map_smul' := (IsLocalization.linearMap_compatibleSMul (.powers f)
      (Localization.Away f) _ _).map_smul _ }

/-- The chart coordinate map is a bijection, with no supplied comparison data. -/
lemma chartCoordinates_bijective (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    Function.Bijective (chartCoordinates M f) :=
  (coordinates M f).bijective.comp
    (ConcreteCategory.bijective_of_isIso (chartSectionsIso M f).hom)

/-- The given sheaf inclusion restricted to its actual affine chart. -/
def chartInclusion {M : (Spec R).Modules} {U : (Spec R).Opens}
    {L : U.toScheme.Modules} (i : L ⟶ M.restrict U.ι) (f : R) (hf : basicOpen f ≤ U) :
    L.restrict (chart U f hf) ⟶ M.restrict (principalMap f) :=
  (restrictFunctor (chart U f hf)).map i ≫ (chartRestrictIso M U f hf).hom

/-- The actual section map, expressed in localized global-section coordinates. -/
def inclusionCoordinates {M : (Spec R).Modules} [M.IsQuasicoherent]
    {U : (Spec R).Opens} {L : U.toScheme.Modules} (i : L ⟶ M.restrict U.ι)
    (f : R) (hf : basicOpen f ≤ U) :
    Γ(L.restrict (chart U f hf), ⊤) →ₗ[Localization.Away f]
      LocalizedModule (.powers f) (moduleSpecΓFunctor.obj M) :=
  (chartCoordinates M f).comp (moduleSpecΓFunctor.map (chartInclusion i f hf)).hom

/-- The coefficient submodule is constructed from the image of actual sections. -/
def sectionSubmodule {M : (Spec R).Modules} [M.IsQuasicoherent]
    {U : (Spec R).Opens} {L : U.toScheme.Modules} (i : L ⟶ M.restrict U.ι)
    (f : R) (hf : basicOpen f ≤ U) :
    Submodule (Localization.Away f) (LocalizedModule (.powers f) (moduleSpecΓFunctor.obj M)) :=
  LinearMap.range (inclusionCoordinates i f hf)

@[simp]
lemma mem_sectionSubmodule {M : (Spec R).Modules} [M.IsQuasicoherent]
    {U : (Spec R).Opens} {L : U.toScheme.Modules} (i : L ⟶ M.restrict U.ι)
    (f : R) (hf : basicOpen f ≤ U)
    (x : LocalizedModule (.powers f) (moduleSpecΓFunctor.obj M)) :
    x ∈ sectionSubmodule i f hf ↔ ∃ y, inclusionCoordinates i f hf y = x := Iff.rfl

/-- The chart really parametrizes the specified principal open in the ambient scheme. -/
lemma chart_image (U : (Spec R).Opens) (f : R) (hf : basicOpen f ≤ U) :
    U.ι ''ᵁ (chart U f hf ''ᵁ ⊤) = basicOpen f := by
  rw [← Scheme.Hom.comp_image]
  simp [chart_comp, principalMap]

/-- The actual inclusion on sections, before passing to affine coordinates. -/
def inclusionSection {M : (Spec R).Modules} {U : (Spec R).Opens}
    {L : U.toScheme.Modules} (i : L ⟶ M.restrict U.ι) (f : R) (hf : basicOpen f ≤ U) :
    Γ(L, chart U f hf ''ᵁ ⊤) →+ Γ(M, basicOpen f) :=
  ((M.presheaf.map (eqToHom (chart_image U f hf).symm).op).hom.comp
    ((M.restrictAppIso U.ι (chart U f hf ''ᵁ ⊤)).hom.hom)).comp
      (i.app (chart U f hf ''ᵁ ⊤)).hom

/-- All chart comparison maps commute with the original sheaf inclusion. -/
lemma inclusionCoordinates_apply {M : (Spec R).Modules} [M.IsQuasicoherent]
    {U : (Spec R).Opens} {L : U.toScheme.Modules} (i : L ⟶ M.restrict U.ι)
    (f : R) (hf : basicOpen f ≤ U) (y : Γ(L.restrict (chart U f hf), ⊤)) :
    inclusionCoordinates i f hf y = coordinates M f
      (inclusionSection i f hf ((L.restrictAppIso (chart U f hf) ⊤).hom y)) := by
  change coordinates M f
    (M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ (i.app _ y)))) =
      coordinates M f (M.presheaf.map _ (i.app _ y))
  simp only [← M.presheaf.map_comp_apply]
  rfl

/-- Membership is witnessed by an actual section of the subsheaf on the chart image. -/
lemma mem_sectionSubmodule_iff_actual {M : (Spec R).Modules} [M.IsQuasicoherent]
    {U : (Spec R).Opens} {L : U.toScheme.Modules} (i : L ⟶ M.restrict U.ι)
    (f : R) (hf : basicOpen f ≤ U)
    (x : LocalizedModule (.powers f) (moduleSpecΓFunctor.obj M)) :
    x ∈ sectionSubmodule i f hf ↔
      ∃ y : Γ(L, chart U f hf ''ᵁ ⊤), coordinates M f (inclusionSection i f hf y) = x := by
  simp only [mem_sectionSubmodule, inclusionCoordinates_apply]
  rfl

/-- Coherence of the given subsheaf makes each constructed coefficient submodule finite. -/
lemma sectionSubmodule_finite {M : (Spec R).Modules} [M.IsQuasicoherent]
    {U : (Spec R).Opens} {L : U.toScheme.Modules} [L.IsFinitePresentation]
    (i : L ⟶ M.restrict U.ι) (f : R) (hf : basicOpen f ≤ U) :
    Module.Finite (Localization.Away f) (sectionSubmodule i f hf) := by
  have : (L.restrict (chart U f hf)).IsFinitePresentation :=
    FCurve.CoherentDevissage.coherentPresentation_restrict _ L
  have := FCurve.affineCoherent_finite_sections (L.restrict (chart U f hf))
  exact Module.Finite.range (inclusionCoordinates i f hf)

/-- At its own denominator the contraction recovers this actual section-image submodule. -/
lemma sectionSubmodule_contraction_localized {M : (Spec R).Modules} [M.IsQuasicoherent]
    {U : (Spec R).Opens} {L : U.toScheme.Modules} (i : L ⟶ M.restrict U.ι)
    (f : R) (hf : basicOpen f ≤ U) :
    (AffineCoherentSubmoduleExtension.principalContraction f
      (sectionSubmodule i f hf)).localized (.powers f) = sectionSubmodule i f hf :=
  AffineCoherentSubmoduleExtension.principalContraction_localized _ _

/-- The principal product chart lies inside the first chart on the open subscheme. -/
lemma chart_product_le (U : (Spec R).Opens) (f g : R) (hf : basicOpen f ≤ U) :
    chart U (f * g) ((basicOpen_mul_le_left f g).trans hf) ''ᵁ ⊤ ≤
      chart U f hf ''ᵁ ⊤ := by
  rw [← Scheme.Hom.image_le_image_iff U.ι, chart_image, chart_image]
  exact basicOpen_mul_le_left f g

/-- Actual section inclusions commute with restriction to a product principal open. -/
lemma inclusionSection_restriction {M : (Spec R).Modules} {U : (Spec R).Opens}
    {L : U.toScheme.Modules} (i : L ⟶ M.restrict U.ι)
    (f g : R) (hf : basicOpen f ≤ U) (y : Γ(L, chart U f hf ''ᵁ ⊤)) :
    inclusionSection i (f * g) ((basicOpen_mul_le_left f g).trans hf)
        (L.presheaf.map (homOfLE (chart_product_le U f g hf)).op y) =
      M.presheaf.map (homOfLE (basicOpen_mul_le_left f g)).op
        (inclusionSection i f hf y) := by
  let V := chart U f hf ''ᵁ ⊤
  let W := chart U (f * g) ((basicOpen_mul_le_left f g).trans hf) ''ᵁ ⊤
  let k : W ⟶ V := homOfLE (chart_product_le U f g hf)
  let t : op (U.ι ''ᵁ V) ⟶ op (U.ι ''ᵁ W) :=
    (homOfLE (U.ι.image_mono (chart_product_le U f g hf))).op
  have h : i.app W (L.presheaf.map k.op y) = M.presheaf.map t (i.app V y) :=
    congrArg (fun a ↦ a.hom y) (i.mapPresheaf.naturality k.op)
  let eW := (eqToHom (chart_image U (f * g)
    ((basicOpen_mul_le_left f g).trans hf)).symm).op
  let eV := (eqToHom (chart_image U f hf).symm).op
  change M.presheaf.map eW (i.app W (L.presheaf.map k.op y)) =
    M.presheaf.map (homOfLE (basicOpen_mul_le_left f g)).op
      (M.presheaf.map eV (i.app V y))
  apply (congrArg (fun z ↦ M.presheaf.map eW z) h).trans
  simp only [← M.presheaf.map_comp_apply]
  exact (M.presheaf.map_comp_apply t eW (i.app V y)).symm

/-- Inclusions and restriction commute after taking scalar-localization coordinates. -/
lemma inclusionSection_coordinates_restriction {M : (Spec R).Modules} [M.IsQuasicoherent]
    {U : (Spec R).Opens} {L : U.toScheme.Modules} (i : L ⟶ M.restrict U.ι)
    (f g : R) (hf : basicOpen f ≤ U) (y : Γ(L, chart U f hf ''ᵁ ⊤)) :
    coordinates M (f * g)
        (inclusionSection i (f * g) ((basicOpen_mul_le_left f g).trans hf)
          (L.presheaf.map (homOfLE (chart_product_le U f g hf)).op y)) =
      TildePrincipalOpen.localizationRestriction (moduleSpecΓFunctor.obj M) f g
        (coordinates M f (inclusionSection i f hf y)) := by
  rw [inclusionSection_restriction]
  exact coordinates_restriction M f g _

end FLT.Mazur.PrincipalSubmoduleCoordinates
