/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveCoherentCharts
public import FLT.Mazur.TildePrincipalOpen

/-!
# Localization of modules on projective chart overlaps

The coordinate spectrum of an overlap maps to the chart by `Spec.map toOverlap`.
Its sections are compared with sections on the corresponding principal open,
with the scalar action given by that same ring map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.ProjectiveSpace

/-- Restriction along a map of affine spectra respects the source ring action. -/
def specRestrictionImageEquiv {A B : CommRingCat.{u}} (f : A ⟶ B)
    [IsOpenImmersion (Spec.map f)] (M : (Spec A).Modules) :
    (ModuleCat.restrictScalars f.hom).obj
        (moduleSpecΓFunctor.obj (M.restrict (Spec.map f))) ≃ₗ[A]
      (modulesSpecToSheaf.obj M).presheaf.obj (op (Spec.map f ''ᵁ ⊤)) where
  toFun := (M.restrictAppIso (Spec.map f) ⊤).hom
  invFun := (M.restrictAppIso (Spec.map f) ⊤).inv
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_add' := map_add _
  map_smul' r x := M.restrictAppIso_smul_Spec f r x

/-- Global-to-open restriction with the affine base-ring module structures. -/
abbrev specOpenRestriction {A : CommRingCat.{u}} (M : (Spec A).Modules)
    (U : (Spec A).Opens) :
    moduleSpecΓFunctor.obj M →ₗ[A] (modulesSpecToSheaf.obj M).presheaf.obj (op U) :=
  ((modulesSpecToSheaf.obj M).presheaf.map U.leTop.op).hom

private lemma specOpenRestriction_localized {A : CommRingCat.{u}}
    (M : (Spec A).Modules) (N : ModuleCat A) (e : M ≅ tilde N) (f : A) :
    IsLocalizedModule (.powers f) (specOpenRestriction M (PrimeSpectrum.basicOpen f)) :=
  isLocalizing_of_iso (modulesSpecToSheaf.mapIso e.symm) (isLocalizing_tilde N) f

attribute [local instance] MvPolynomial.gradedAlgebra

section

variable (R : Type u) [CommRing R] (ι : Type v)

/-- The overlap spectrum maps to projective space by the actual overlap chart. -/
def overlapMap (i j : ι) : Spec (.of (overlapRing R ι i j)) ⟶ space R ι :=
  (overlapIso R ι i j).inv ≫
    (Proj.basicOpen (grading R ι) (X i * X j)).ι

instance overlapMap_isOpenImmersion (i j : ι) :
    IsOpenImmersion (overlapMap R ι i j) := by
  dsimp [overlapMap]
  infer_instance

/-- The ring restriction induces precisely the inclusion of the overlap chart. -/
lemma toOverlap_chartMap (i j : ι) :
    Spec.map (CommRingCat.ofHom (toOverlap R ι i j)) ≫ chartMap R ι i =
      overlapMap R ι i j := by
  exact Proj.SpecMap_awayMap_awayι (grading R ι) (isHomogeneous_X R i)
    (by decide) (isHomogeneous_X R j) rfl

/-- Pulling back another standard chart gives the principal open of its ratio. -/
lemma chartMap_preimage_chart (i j : ι) :
    chartMap R ι i ⁻¹ᵁ chart R ι j =
      PrimeSpectrum.basicOpen (coordinate R ι i j) := by
  simpa only [chartMap, chartIso, chart, Proj.awayι,
    HomogeneousLocalization.Away.isLocalizationElem, coordinate, pow_one] using
    Proj.awayι_preimage_basicOpen (grading R ι) (isHomogeneous_X R i)
      (by decide) (isHomogeneous_X R j) (by decide)

/-- The actual intersection has the same principal-open preimage. -/
lemma chartMap_preimage_overlap (i j : ι) :
    chartMap R ι i ⁻¹ᵁ (chart R ι i ⊓ chart R ι j) =
      PrimeSpectrum.basicOpen (coordinate R ι i j) := by
  rw [Scheme.Hom.preimage_inf, chartMap_preimage_chart, chartMap_preimage_chart,
    coordinate_self, PrimeSpectrum.basicOpen_one, top_inf_eq]

/-- The coordinate algebra of the overlap uses the specified restriction map. -/
instance overlapChartAlgebra (i j : ι) :
    Algebra (chartRing R ι i) (overlapRing R ι i j) :=
  (toOverlap R ι i j).toAlgebra

instance overlapChartLocalization (i j : ι) :
    IsLocalization.Away (coordinate R ι i j) (overlapRing R ι i j) :=
  overlap_isLocalization R ι i j

instance toOverlap_isOpenImmersion (i j : ι) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (toOverlap R ι i j))) := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (chartRing R ι i) (overlapRing R ι i j))))
  exact IsOpenImmersion.of_isLocalization (coordinate R ι i j)

/-- The overlap spectrum has exactly the expected image in the coordinate chart. -/
lemma toOverlap_image_top (i j : ι) :
    Spec.map (CommRingCat.ofHom (toOverlap R ι i j)) ''ᵁ ⊤ =
      PrimeSpectrum.basicOpen (coordinate R ι i j) := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact TopologicalSpace.Opens.ext
    (PrimeSpectrum.localization_away_comap_range (overlapRing R ι i j)
      (coordinate R ι i j))

end

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original sheaf on the coordinate spectrum of the overlap. -/
abbrev overlapModule (F : (space R ι).Modules) (i j : ι) :=
  F.restrict (overlapMap R ι i j)

/-- Actual overlap sections, with the overlap coordinate-ring action. -/
abbrev overlapSections (F : (space R ι).Modules) (i j : ι) :
    ModuleCat (overlapRing R ι i j) :=
  moduleSpecΓFunctor.obj (overlapModule R ι F i j)

/-- Base scalars act on overlap sections through `toOverlap`. -/
instance overlapSectionsChartModule (F : (space R ι).Modules) (i j : ι) :
    Module (chartRing R ι i) (overlapSections R ι F i j) :=
  Module.compHom _ (toOverlap R ι i j)

instance overlapSectionsScalarTower (F : (space R ι).Modules) (i j : ι) :
    IsScalarTower (chartRing R ι i) (overlapRing R ι i j)
      (overlapSections R ι F i j) :=
  IsScalarTower.of_compHom _ _ _

/-- Composition and the geometric equality identify the two restrictions. -/
def overlapModuleIso (F : (space R ι).Modules) (i j : ι) :
    overlapModule R ι F i j ≅
      (chartModule R ι F i).restrict
        (Spec.map (CommRingCat.ofHom (toOverlap R ι i j))) :=
  (Scheme.Modules.restrictFunctorCongr (toOverlap_chartMap R ι i j).symm).app F ≪≫
    (Scheme.Modules.restrictFunctorComp _ _).app F

/-- Sections after restricting the chart along the overlap ring map, with base scalars. -/
abbrev iteratedOverlapSections (F : (space R ι).Modules) (i j : ι) :
    ModuleCat (chartRing R ι i) :=
  (ModuleCat.restrictScalars (toOverlap R ι i j)).obj
    (moduleSpecΓFunctor.obj ((chartModule R ι F i).restrict
      (Spec.map (CommRingCat.ofHom (toOverlap R ι i j)))))

/-- The section comparison for restriction is linear for the action through `toOverlap`. -/
def iteratedOverlapImageEquiv (F : (space R ι).Modules) (i j : ι) :
    iteratedOverlapSections R ι F i j ≃ₗ[chartRing R ι i]
      (modulesSpecToSheaf.obj (chartModule R ι F i)).presheaf.obj
        (op (Spec.map (CommRingCat.ofHom (toOverlap R ι i j)) ''ᵁ ⊤)) :=
  specRestrictionImageEquiv (CommRingCat.ofHom (toOverlap R ι i j))
    (chartModule R ι F i)

/-- Overlap sections identified with actual principal-open sections of the chart. -/
def overlapPrincipalEquiv (F : (space R ι).Modules) (i j : ι) :
    overlapSections R ι F i j ≃ₗ[chartRing R ι i]
      (modulesSpecToSheaf.obj (chartModule R ι F i)).presheaf.obj
        (op (PrimeSpectrum.basicOpen (coordinate R ι i j))) :=
  (((ModuleCat.restrictScalars (toOverlap R ι i j)).mapIso
    (moduleSpecΓFunctor.mapIso (overlapModuleIso R ι F i j))).toLinearEquiv.trans
      (iteratedOverlapImageEquiv R ι F i j)).trans
    (((modulesSpecToSheaf.obj (chartModule R ι F i)).presheaf.mapIso
      (eqToIso (toOverlap_image_top R ι i j).symm).op).toLinearEquiv)

/-- Restriction of actual chart sections to the overlap, in overlap coordinates. -/
def chartOverlapRestriction (F : (space R ι).Modules) (i j : ι) :
    chartSections R ι F i →ₗ[chartRing R ι i] overlapSections R ι F i j :=
  (overlapPrincipalEquiv R ι F i j).symm.toLinearMap.comp
    (specOpenRestriction (chartModule R ι F i)
      (PrimeSpectrum.basicOpen (coordinate R ι i j)))

/-- In the principal-open coordinates this is precisely the sheaf restriction map. -/
lemma overlapPrincipalEquiv_restriction (F : (space R ι).Modules) (i j : ι)
    (s : chartSections R ι F i) :
    overlapPrincipalEquiv R ι F i j (chartOverlapRestriction R ι F i j s) =
      specOpenRestriction (chartModule R ι F i)
        (PrimeSpectrum.basicOpen (coordinate R ι i j)) s :=
  (overlapPrincipalEquiv R ι F i j).apply_symm_apply _

/-- The actual overlap restriction is localization at the powers of `Xⱼ/Xᵢ`. -/
instance chartOverlapRestriction_isLocalized (F : (space R ι).Modules)
    [F.IsFinitePresentation] (i j : ι) :
    IsLocalizedModule (.powers (coordinate R ι i j)) (chartOverlapRestriction R ι F i j) := by
  have h := specOpenRestriction_localized (chartModule R ι F i)
    (chartSections R ι F i) (chartModuleIso R ι F i) (coordinate R ι i j)
  exact IsLocalizedModule.of_linearEquiv (.powers (coordinate R ι i j)) _
    (overlapPrincipalEquiv R ι F i j).symm

/-- The overlap spectrum covers exactly the intersection in projective space. -/
lemma overlapMap_image_top (i j : ι) :
    overlapMap R ι i j ''ᵁ ⊤ = chart R ι i ⊓ chart R ι j := by
  rw [Scheme.Hom.image_top_eq_opensRange, chart_inf]
  exact Proj.opensRange_awayι (grading R ι) (X i * X j)
    ((isHomogeneous_X R i).mul (isHomogeneous_X R j)) (by decide)

/-- These coordinate-spectrum sections are the original sheaf's overlap sections. -/
def overlapSectionsIso (F : (space R ι).Modules) (i j : ι) :
    Γ(overlapModule R ι F i j, ⊤) ≅ Γ(F, chart R ι i ⊓ chart R ι j) :=
  F.restrictAppIso (overlapMap R ι i j) ⊤ ≪≫
    F.presheaf.mapIso (eqToIso (overlapMap_image_top R ι i j).symm).op

/-- Explicit compatibility with the overlap coordinate-ring action. -/
lemma chartOverlapRestriction_smul (F : (space R ι).Modules) (i j : ι)
    (r : chartRing R ι i) (s : chartSections R ι F i) :
    chartOverlapRestriction R ι F i j (r • s) =
      toOverlap R ι i j r • chartOverlapRestriction R ι F i j s :=
  (chartOverlapRestriction R ι F i j).map_smul r s

/-- The powers action uses the actual coordinate ratio in the overlap ring. -/
lemma overlapSections_pow_smul (F : (space R ι).Modules) (i j : ι) (n : ℕ)
    (s : overlapSections R ι F i j) :
    coordinate R ι i j ^ n • s =
      toOverlap R ι i j (coordinate R ι i j) ^ n • s := by
  change toOverlap R ι i j (coordinate R ι i j ^ n) • s = _
  rw [map_pow]

/-- The universal algebraic localization compared with actual overlap sections. -/
def overlapLocalizationEquiv (F : (space R ι).Modules) [F.IsFinitePresentation]
    (i j : ι) :
    overlapSections R ι F i j ≃ₗ[chartRing R ι i]
      LocalizedModule (.powers (coordinate R ι i j)) (chartSections R ι F i) :=
  (IsLocalizedModule.iso (.powers (coordinate R ι i j))
    (chartOverlapRestriction R ι F i j)).symm

/-- A restricted chart section represents the fraction with denominator one. -/
lemma overlapLocalizationEquiv_restriction (F : (space R ι).Modules)
    [F.IsFinitePresentation] (i j : ι) (s : chartSections R ι F i) :
    overlapLocalizationEquiv R ι F i j (chartOverlapRestriction R ι F i j s) =
      LocalizedModule.mk s 1 :=
  IsLocalizedModule.iso_symm_apply _ _ _

end FLT.Mazur.ProjectiveSpace
