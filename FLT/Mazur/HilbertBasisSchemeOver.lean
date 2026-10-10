/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisSchemeGluing

/-!
# The intrinsic chart morphism respects the base scheme

The algebra-classifying maps commute with the original base ring. This
identity descends through the constructed cover to the glued scheme morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]

/-- Every local classifying morphism commutes with the original base scheme map. -/
theorem neighborhoodChartMorphism_over (r : PolynomialBasisNeighborhoods R I d w S J) :
    neighborhoodChartMorphism R I d w S J r ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w))) =
    Scheme.Opens.ι (X := Spec (.of S)) (PrimeSpectrum.basicOpen r.val) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  have hc : CommRingCat.ofHom (algebraMap R (ChartRing R I d w)) ≫
      CommRingCat.ofHom (neighborhoodClassifyingMap R I d w S J r).toRingHom =
      CommRingCat.ofHom (algebraMap R (Localization.Away r.val)) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (neighborhoodClassifyingMap R I d w S J r).commutes
  have ht : CommRingCat.ofHom (algebraMap R S) ≫
      CommRingCat.ofHom (algebraMap S (Localization.Away r.val)) =
      CommRingCat.ofHom (algebraMap R (Localization.Away r.val)) := by
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq R S (Localization.Away r.val)).symm
  rw [neighborhoodChartMorphism, Category.assoc, ← Spec.map_comp, hc, ← ht,
    Spec.map_comp, ← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]

/-- The glued intrinsic classifying morphism is a morphism over `Spec R`. -/
theorem intrinsicChartMorphism_over :
    intrinsicChartMorphism R I d w S J ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w))) =
    Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (polynomialBasisSchemeCover R I d w S J).hom_ext
  intro r
  rw [← Category.assoc, intrinsicChartMorphism_restrict]
  change _ = (Spec (.of S)).homOfLE (neighborhood_basicOpen_le R I d w S J r) ≫ _
  rw [← Category.assoc, Scheme.homOfLE_ι]
  exact neighborhoodChartMorphism_over R I d w S J r

end FLT.Mazur.HilbertChart
