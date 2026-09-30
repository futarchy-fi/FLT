/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SegreSchemeMorphism
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The Segre closed immersion

Every target standard chart has exactly the matching product chart as its
inverse image. The global morphism is therefore closed by locality on the
covered target, using the determinantal quotient on each affine chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι κ : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma segre_chartMap_opensRange (i : ι) :
    (chartMap R ι i).opensRange = chart R ι i :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (chart R ι i).opensRange_ι

/-- The product chart is exactly the intersection of the two projection preimages. -/
lemma productChartMap_opensRange (i : ι) (j : κ) :
    (productChartMap R ι κ i j).opensRange =
      pullback.fst (baseProjection R ι) (baseProjection R κ) ⁻¹ᵁ chart R ι i ⊓
        pullback.snd (baseProjection R ι) (baseProjection R κ) ⁻¹ᵁ chart R κ j := by
  change ((productChartIso R ι κ i j).inv ≫
    (productPullbackCover R ι κ).f (i, j)).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  change Set.range (pullback.map _ _ _ _ (chartMap R ι i) (chartMap R κ j) (𝟙 _)
    (Category.comp_id _) (Category.comp_id _)) = _
  rw [Scheme.Pullback.range_map]
  change _ ⁻¹' ((chartMap R ι i).opensRange : Set (space R ι)) ∩
    _ ⁻¹' ((chartMap R κ j).opensRange : Set (space R κ)) = _
  rw [segre_chartMap_opensRange, segre_chartMap_opensRange]
  rfl

/-- On every source chart, a product chart is cut out by the two coordinate conditions. -/
lemma productChartMap_preimage_productChart (i k : ι) (j l : κ) :
    productChartMap R ι κ i j ⁻¹ᵁ (productChartMap R ι κ k l).opensRange =
      PrimeSpectrum.basicOpen (coordinate R ι i k ⊗ₜ[R] (1 : chartRing R κ j)) ⊓
        PrimeSpectrum.basicOpen ((1 : chartRing R ι i) ⊗ₜ[R] coordinate R κ j l) := by
  rw [productChartMap_opensRange, Scheme.Hom.preimage_inf,
    ← Scheme.Hom.comp_preimage, productChartMap_fst,
    Scheme.Hom.comp_preimage, chartMap_preimage_chart, SpecMap_preimage_basicOpen,
    ← Scheme.Hom.comp_preimage, productChartMap_snd,
    Scheme.Hom.comp_preimage, chartMap_preimage_chart, SpecMap_preimage_basicOpen]
  rfl

/-- Each target standard chart has precisely its matching source product chart as preimage. -/
lemma segreMorphism_preimage_chart (i : ι) (j : κ) :
    segreMorphism R ι κ ⁻¹ᵁ chart R (ι × κ) (i, j) =
      (productChartMap R ι κ i j).opensRange := by
  have h (p : ι × κ) :
      productChartMap R ι κ p.1 p.2 ⁻¹ᵁ
          (segreMorphism R ι κ ⁻¹ᵁ chart R (ι × κ) (i, j)) =
        productChartMap R ι κ p.1 p.2 ⁻¹ᵁ (productChartMap R ι κ i j).opensRange := by
    rw [← Scheme.Hom.comp_preimage, productChartMap_segreMorphism,
      segreChartToProjective_preimage_factors, productChartMap_preimage_productChart]
  ext x
  obtain ⟨p, y, rfl⟩ := (productChartCover R ι κ).exists_eq x
  exact iff_of_eq (congrArg (fun U ↦ y ∈ U) (h p))

/-- The local affine Segre square is a pullback of the global map along a target chart. -/
lemma segreChartIsPullback (i : ι) (j : κ) :
    IsPullback (segreChartMorphism R ι κ i j) (productChartMap R ι κ i j)
      (chart R (ι × κ) (i, j)).ι (segreMorphism R ι κ) := by
  apply IsOpenImmersion.isPullback
  · exact productChartMap_segreMorphism R ι κ i j
  · rw [Scheme.Opens.opensRange_ι, segreMorphism_preimage_chart]

/-- The inverse image of a target chart is canonically the tensor spectrum of its source charts. -/
def segreRestrictIso (i : ι) (j : κ) :
    Spec (.of (segreSourceRing R ι κ i j)) ≅
      (segreMorphism R ι κ ⁻¹ᵁ chart R (ι × κ) (i, j)).toScheme :=
  (segreChartIsPullback R ι κ i j).isoIsPullback _ _
    (isPullback_morphismRestrict (segreMorphism R ι κ) (chart R (ι × κ) (i, j)))

/-- Under this comparison, the target restriction is the determinantal affine Segre map. -/
@[reassoc (attr := simp)]
lemma segreRestrictIso_hom_restrict (i : ι) (j : κ) :
    (segreRestrictIso R ι κ i j).hom ≫
        (segreMorphism R ι κ ∣_ chart R (ι × κ) (i, j)) =
      segreChartMorphism R ι κ i j :=
  (segreChartIsPullback R ι κ i j).isoIsPullback_hom_fst _ _ _

/-- The comparison also identifies the source inclusion with the actual product chart map. -/
@[reassoc (attr := simp)]
lemma segreRestrictIso_hom_ι (i : ι) (j : κ) :
    (segreRestrictIso R ι κ i j).hom ≫
        (segreMorphism R ι κ ⁻¹ᵁ chart R (ι × κ) (i, j)).ι =
      productChartMap R ι κ i j :=
  (segreChartIsPullback R ι κ i j).isoIsPullback_hom_snd _ _ _

/-- Every target restriction is closed, by the affine determinantal quotient. -/
instance segreMorphism_restrict_isClosedImmersion (i : ι) (j : κ) :
    IsClosedImmersion (segreMorphism R ι κ ∣_ chart R (ι × κ) (i, j)) := by
  have h : segreMorphism R ι κ ∣_ chart R (ι × κ) (i, j) =
      (segreRestrictIso R ι κ i j).inv ≫ segreChartMorphism R ι κ i j := by
    rw [← segreRestrictIso_hom_restrict, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- The Segre morphism is a closed immersion, checked on a cover of its entire target. -/
instance segreMorphism_isClosedImmersion : IsClosedImmersion (segreMorphism R ι κ) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (chart R (ι × κ)) (iSup_chart R (ι × κ))
  intro p
  exact segreMorphism_restrict_isClosedImmersion R ι κ p.1 p.2

end FLT.Mazur.ProjectiveSpace
