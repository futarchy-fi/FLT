/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisPrincipalCompatibility

/-!
# Gluing the classifying morphism on the intrinsic basis locus

Compatibility on actual principal intersections gives a scheme morphism to the
Hilbert chart. Its restriction to every constructed neighborhood is the
ideal-classifying map, and these restrictions characterize it uniquely.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]

/-- The actual local morphisms agree on the scheme intersection of their domains. -/
theorem neighborhoodChartMorphism_inf_agree
    (r s : PolynomialBasisNeighborhoods R I d w S J) :
    (Spec (.of S)).homOfLE (U := PrimeSpectrum.basicOpen r.val ⊓ PrimeSpectrum.basicOpen s.val)
        inf_le_left ≫ neighborhoodChartMorphism R I d w S J r =
    (Spec (.of S)).homOfLE (U := PrimeSpectrum.basicOpen r.val ⊓ PrimeSpectrum.basicOpen s.val)
        inf_le_right ≫ neighborhoodChartMorphism R I d w S J s := by
  let e := (Spec (.of S)).isoOfEq (PrimeSpectrum.basicOpen_mul r.val s.val)
  have hr : PrimeSpectrum.basicOpen (r.val * s.val) ≤ PrimeSpectrum.basicOpen r.val := by
    rw [PrimeSpectrum.basicOpen_mul]
    exact inf_le_left
  have hs : PrimeSpectrum.basicOpen (r.val * s.val) ≤ PrimeSpectrum.basicOpen s.val := by
    rw [PrimeSpectrum.basicOpen_mul]
    exact inf_le_right
  have her : e.hom ≫ (Spec (.of S)).homOfLE inf_le_left = (Spec (.of S)).homOfLE hr := by
    rw [← cancel_mono (Scheme.Opens.ι (X := Spec (.of S)) (PrimeSpectrum.basicOpen r.val))]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.isoOfEq_hom_ι, e]
  have hes : e.hom ≫ (Spec (.of S)).homOfLE inf_le_right = (Spec (.of S)).homOfLE hs := by
    rw [← cancel_mono (Scheme.Opens.ι (X := Spec (.of S)) (PrimeSpectrum.basicOpen s.val))]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.isoOfEq_hom_ι, e]
  apply (cancel_epi e.hom).mp
  simpa only [← Category.assoc, her, hes] using
    neighborhoodChartMorphism_product_agree R I d w S J r s hr hs

/-- The principal chart morphisms satisfy the categorical pullback compatibility for gluing. -/
theorem neighborhoodChartMorphism_pullback_agree
    (r s : PolynomialBasisNeighborhoods R I d w S J) :
    pullback.fst ((polynomialBasisSchemeCover R I d w S J).f r)
        ((polynomialBasisSchemeCover R I d w S J).f s) ≫
      neighborhoodChartMorphism R I d w S J r =
    pullback.snd ((polynomialBasisSchemeCover R I d w S J).f r)
        ((polynomialBasisSchemeCover R I d w S J).f s) ≫
      neighborhoodChartMorphism R I d w S J s := by
  dsimp only [polynomialBasisSchemeCover]
  let h := isPullback_opens_inf_le (X := Spec (.of S))
    (neighborhood_basicOpen_le R I d w S J r)
    (neighborhood_basicOpen_le R I d w S J s)
  apply (cancel_epi h.isoPullback.hom).mp
  simpa only [← Category.assoc, h.isoPullback_hom_fst, h.isoPullback_hom_snd] using
    neighborhoodChartMorphism_inf_agree R I d w S J r s

/-- The actual scheme morphism classifying the family on its intrinsic basis locus. -/
def intrinsicChartMorphism :
    polynomialBasisScheme R I d w S J ⟶ Spec (.of (ChartRing R I d w)) :=
  (polynomialBasisSchemeCover R I d w S J).glueMorphisms
    (neighborhoodChartMorphism R I d w S J)
    (neighborhoodChartMorphism_pullback_agree R I d w S J)

/-- The glued morphism recovers each constructed ideal-classifying chart. -/
theorem intrinsicChartMorphism_restrict (r : PolynomialBasisNeighborhoods R I d w S J) :
    (polynomialBasisSchemeCover R I d w S J).f r ≫ intrinsicChartMorphism R I d w S J =
      neighborhoodChartMorphism R I d w S J r :=
  (polynomialBasisSchemeCover R I d w S J).ι_glueMorphisms _ _ r

/-- Local ideal-classifying restrictions uniquely determine the global scheme morphism. -/
theorem intrinsicChartMorphism_unique
    (f : polynomialBasisScheme R I d w S J ⟶ Spec (.of (ChartRing R I d w)))
    (hf : ∀ r, (polynomialBasisSchemeCover R I d w S J).f r ≫ f =
      neighborhoodChartMorphism R I d w S J r) : f = intrinsicChartMorphism R I d w S J := by
  apply (polynomialBasisSchemeCover R I d w S J).hom_ext
  intro r
  rw [hf, intrinsicChartMorphism_restrict]

end FLT.Mazur.HilbertChart
