/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialAmbientNaturality

/-!
# Recovering polynomial families on principal basis neighborhoods

The global parameter restricts to the actual ideal-classifying map on every
principal basis neighborhood. Its ambient map recovers the entire localized
quotient ideal from the global universal ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
  (MvPolynomial I p.asIdeal.ResidueField ⧸
    J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)
variable (w : Fin d → MvPolynomial I R)

/-- Restriction to a principal basis neighborhood is its actual ideal-classifying parameter. -/
theorem polynomialFamilyMorphism_principal (r : PolynomialBasisNeighborhoods R I d w S J) :
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r.val))) ≫
        polynomialFamilyMorphism R I d S J hd =
      Spec.map (CommRingCat.ofHom (neighborhoodClassifyingMap R I d w S J r).toRingHom) ≫
        polynomialHilbertChartι R I d w := by
  have h := polynomialFamilyMorphism_schemeTest R I d S J hd w
    ((basicOpenIsoSpecAway (R := .of S) r.val).inv ≫
      (polynomialBasisSchemeCover R I d w S J).f r)
  simp only [Category.assoc] at h
  rw [← Category.assoc _ (intrinsicChartMorphism R I d w S J),
    intrinsicChartMorphism_restrict,
    ← Category.assoc _ (neighborhoodChartMorphism R I d w S J r),
    neighborhoodChartMorphism_affine] at h
  change (basicOpenIsoSpecAway (R := .of S) r.val).inv ≫
    (Spec (.of S)).homOfLE (neighborhood_basicOpen_le R I d w S J r) ≫ _ ≫ _ = _ at h
  rw [Scheme.homOfLE_ι_assoc,
    ← basicOpenIsoSpecAway_hom_SpecMap (R := .of S) r.val,
    Category.assoc, Iso.inv_hom_id_assoc] at h
  exact h

/-- The ambient restriction is exactly the explicit ambient parameter map. -/
theorem polynomialFamilyAmbientMap_principal (r : PolynomialBasisNeighborhoods R I d w S J) :
    Spec.map (CommRingCat.ofHom
        (MvPolynomial.map (algebraMap S (Localization.Away r.val)))) ≫
        polynomialFamilyAmbientMap R I d S J hd =
      polynomialParameterAmbientMap R I d w (neighborhoodClassifyingMap R I d w S J r) := by
  let a := neighborhoodClassifyingMap R I d w S J r
  let g := Spec.map (CommRingCat.ofHom a.toRingHom) ≫ polynomialHilbertChartι R I d w
  have hg : g ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r.val))) := by
    dsimp only [g, a]
    rw [← polynomialFamilyMorphism_principal R I d S J hd w r, Category.assoc,
      polynomialFamilyMorphism_over, ← Spec.map_comp]
    congr 1
  exact (polynomialAmbientMap_baseChange R I d S _
    (polynomialFamilyMorphism_over R I d S J hd) _ (IsScalarTower.toAlgHom R S _)
    g hg (polynomialFamilyMorphism_principal R I d S J hd w r)).trans
      (polynomialAmbientMap_parameter R I d _ w a hg)

/-- Pullback of the global universal ideal recovers the actual ideal on each basis neighborhood. -/
theorem polynomialUniversalIdeal_principalPullback
    (r : PolynomialBasisNeighborhoods R I d w S J) :
    ((polynomialUniversalIdeal R I d).comap (polynomialFamilyAmbientMap R I d S J hd)).comap
        (Spec.map (CommRingCat.ofHom
          (MvPolynomial.map (algebraMap S (Localization.Away r.val))))) =
      baseIdeal (.of (MvPolynomial I (Localization.Away r.val)))
        (J.map (MvPolynomial.map (algebraMap S (Localization.Away r.val)))) := by
  rw [← Scheme.IdealSheafData.comap_comp,
    polynomialFamilyAmbientMap_principal R I d S J hd w r]
  exact polynomialUniversalIdeal_prescribedPullback R I d w (neighborhoodIdeal R I d w S J r)

end FLT.Mazur.HilbertChart
