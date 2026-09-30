/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveAffineChartEmbedding
public import FLT.Mazur.SegreChartQuotient
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine charts of the product of projective spaces

The fiber product over the coefficient spectrum is covered by the spectra of
pairs of standard chart rings tensored over the coefficient ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι κ : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every standard chart respects the coefficient projection. -/
@[reassoc]
lemma chartMap_baseProjection (i : ι) :
    chartMap R ι i ≫ baseProjection R ι =
      Spec.map (CommRingCat.ofHom (algebraMap R (chartRing R ι i))) := by
  change Proj.awayι _ _ _ _ ≫ (Proj.toSpecZero _ ≫ _) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The standard affine spectra cover projective space. -/
def standardChartCover : (space R ι).OpenCover where
  I₀ := ι
  X i := Spec (.of (chartRing R ι i))
  f i := chartMap R ι i
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun _ ↦ inferInstance⟩
    intro x
    obtain ⟨i, hi⟩ := exists_mem_chart R ι x
    refine ⟨i, (chartIso R ι i).hom ⟨x, hi⟩, ?_⟩
    change ((chartIso R ι i).hom ≫ (chartIso R ι i).inv ≫ (chart R ι i).ι) _ = _
    simp

/-- The actual product over `Spec R`. -/
abbrev productSpace := pullback (baseProjection R ι) (baseProjection R κ)

/-- The standard cover before identifying its members with tensor spectra. -/
def productPullbackCover : (productSpace R ι κ).OpenCover :=
  AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight
    (standardChartCover R ι) (standardChartCover R κ)
    (baseProjection R ι) (baseProjection R κ)

/-- Each member is the spectrum of the tensor product of the two chart rings. -/
def productChartIso (i : ι) (j : κ) :
    (productPullbackCover R ι κ).X (i, j) ≅ Spec (.of (segreSourceRing R ι κ i j)) :=
  pullback.congrHom (chartMap_baseProjection R ι i) (chartMap_baseProjection R κ j) ≪≫
    pullbackSpecIso R (chartRing R ι i) (chartRing R κ j)

/-- The tensor chart maps into the actual projective product. -/
def productChartMap (i : ι) (j : κ) :
    Spec (.of (segreSourceRing R ι κ i j)) ⟶ productSpace R ι κ :=
  (productChartIso R ι κ i j).inv ≫ (productPullbackCover R ι κ).f (i, j)

instance productChartMap_isOpenImmersion (i : ι) (j : κ) :
    IsOpenImmersion (productChartMap R ι κ i j) := by
  dsimp only [productChartMap]
  infer_instance

/-- First projection of a tensor chart. -/
@[reassoc (attr := simp)]
lemma productChartMap_fst (i : ι) (j : κ) :
    productChartMap R ι κ i j ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        chartMap R ι i := by
  simp [productChartMap, productChartIso, productPullbackCover,
    AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight_f, standardChartCover]

/-- Second projection of a tensor chart. -/
@[reassoc (attr := simp)]
lemma productChartMap_snd (i : ι) (j : κ) :
    productChartMap R ι κ i j ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
        chartMap R κ j := by
  simp [productChartMap, productChartIso, productPullbackCover,
    AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight_f, standardChartCover]

/-- An open cover whose members are precisely the tensor chart spectra. -/
def productChartCover : (productSpace R ι κ).OpenCover :=
  (productPullbackCover R ι κ).copy (ι × κ)
    (fun p ↦ Spec (.of (segreSourceRing R ι κ p.1 p.2)))
    (fun p ↦ productChartMap R ι κ p.1 p.2) (Equiv.refl _)
    (fun p ↦ (productChartIso R ι κ p.1 p.2).symm) (fun _ ↦ rfl)

/-- The tensor charts cover the entire fiber product. -/
lemma iSup_productChartMap_opensRange :
    ⨆ p : ι × κ, (productChartMap R ι κ p.1 p.2).opensRange = ⊤ :=
  (productChartCover R ι κ).iSup_opensRange

end FLT.Mazur.ProjectiveSpace
