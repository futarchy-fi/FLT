/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisSchemeGluing

/-!
# Recovering the global ideal-classifying parameter

When the prescribed tuple is already a basis, the glued scheme morphism is
the restriction of the spectrum of the actual ideal-classifying algebra map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (J : PrescribedBasisIdeals R I d w S)

/-- Each principal parameter is the localization of the global classifying parameter. -/
theorem neighborhoodClassifyingMap_global
    (r : PolynomialBasisNeighborhoods R I d w S J.val) :
    neighborhoodClassifyingMap R I d w S J.val r =
      (IsScalarTower.toAlgHom R S (Localization.Away r.val)).comp
        (idealClassifyingMap R I d w S J) := by
  rw [← idealClassifyingMap_baseChangeIdeal]
  apply congrArg (idealClassifyingMap R I d w _)
  apply Subtype.ext
  rfl

variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J.val)]

/-- On each principal neighborhood the local map is the restriction of the global parameter. -/
theorem neighborhoodChartMorphism_global
    (r : PolynomialBasisNeighborhoods R I d w S J.val) :
    neighborhoodChartMorphism R I d w S J.val r =
      Scheme.Opens.ι (X := Spec (.of S)) (PrimeSpectrum.basicOpen r.val) ≫
        Spec.map (CommRingCat.ofHom (idealClassifyingMap R I d w S J).toRingHom) := by
  have h : CommRingCat.ofHom (R := ChartRing R I d w)
      (neighborhoodClassifyingMap R I d w S J.val r).toRingHom =
      CommRingCat.ofHom (R := ChartRing R I d w)
        (idealClassifyingMap R I d w S J).toRingHom ≫
        CommRingCat.ofHom (algebraMap S (Localization.Away r.val)) := by
    rw [neighborhoodClassifyingMap_global]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl
  rw [neighborhoodChartMorphism, h, Spec.map_comp, ← Category.assoc,
    basicOpenIsoSpecAway_hom_SpecMap]

/-- The glued morphism recovers the spectrum of the actual global ideal-classifying map. -/
theorem intrinsicChartMorphism_global :
    intrinsicChartMorphism R I d w S J.val =
      Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J.val) ≫
        Spec.map (CommRingCat.ofHom (idealClassifyingMap R I d w S J).toRingHom) := by
  apply (polynomialBasisSchemeCover R I d w S J.val).hom_ext
  intro r
  rw [intrinsicChartMorphism_restrict, neighborhoodChartMorphism_global]
  change _ = (Spec (.of S)).homOfLE (neighborhood_basicOpen_le R I d w S J.val r) ≫ _
  rw [← Category.assoc, Scheme.homOfLE_ι]

end FLT.Mazur.HilbertChart
