/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveCoordinateSections
public import FLT.Mazur.ProjectiveChartSectionPullback

/-!
# Nonvanishing opens of projective coordinates

The generator open of the i-th homogeneous coordinate is exactly the i-th
standard affine chart, over any commutative coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.FCurve
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The basic open of a chart ratio is the inverse image of the numerator chart. -/
lemma chartCoordinateSection_basicOpen (i j : ι) :
    (chart R ι j).toScheme.basicOpen
      ((chart R ι j).topIso.inv (chartCoordinateSection R ι j i)) =
      (chart R ι j).ι ⁻¹ᵁ chart R ι i := by
  suffices h : (chartIso R ι j).inv ⁻¹ᵁ _ = (chartIso R ι j).inv ⁻¹ᵁ _ by
    have hh := congrArg (fun U ↦ (chartIso R ι j).hom ⁻¹ᵁ U) h
    simpa only [← Scheme.Hom.comp_preimage, Iso.hom_inv_id, Scheme.Hom.id_preimage] using hh
  rw [Scheme.Hom.preimage_basicOpen_top, ← Scheme.Hom.comp_preimage]
  have h := ConcreteCategory.congr_hom (chartSection_iso_inv R ι j) (coordinate R ι j i)
  change (chartIso R ι j).inv.appTop
    ((chart R ι j).topIso.inv (chartCoordinateSection R ι j i)) = _ at h
  rw [h, basicOpen_eq_of_affine, ← chartMap, chartMap_preimage_chart]

/-- Every projective coordinate has precisely its standard chart as generator open. -/
theorem coordinateGlobalSection_generatorOpen (i : ι) :
    sectionGeneratorOpen (twistingSheaf R ι 1) (coordinateGlobalSection R ι i) =
      chart R ι i := by
  have hlocal (j : ι) : (chart R ι j).ι ⁻¹ᵁ
      sectionGeneratorOpen (twistingSheaf R ι 1) (coordinateGlobalSection R ι i) =
      (chart R ι j).ι ⁻¹ᵁ chart R ι i := by
    refine ((twistCocycle R ι 1).sectionGeneratorOpen_preimage (iSup_chart R ι) j _ le_rfl
      (coordinateGlobalSection R ι i)).trans ?_
    rw [coordinateGlobalSection_evaluate, FLT.Mazur.FCurve.ModuleSheafUnitCocycle.res_self,
      chartCoordinateSection_basicOpen]
  ext x
  obtain ⟨j, hx⟩ := exists_mem_chart R ι x
  exact congrArg (fun U : (chart R ι j).toScheme.Opens ↦ (⟨x, hx⟩ : (chart R ι j).toScheme) ∈ U)
    (hlocal j) |>.to_iff

end FLT.Mazur.ProjectiveSpace
