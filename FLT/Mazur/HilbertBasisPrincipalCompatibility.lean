/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisSchemeCover
public import FLT.Mazur.HilbertBasisNeighborhoodCompatibility
public import FLT.Mazur.HilbertPrincipalLocalizationScalars
public import FLT.Mazur.HilbertPrincipalRestriction

/-!
# Scheme compatibility on actual principal overlaps

The classifying maps agree on the localization at the product. Transporting
this equality through the principal affine charts gives equality of the
actual scheme morphisms on the intersection.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))

/-- On the actual product localization the two classifying parameters are identical. -/
theorem principal_product_classifying_agree
    (r s : PolynomialBasisNeighborhoods R I d w S J) :
    ((principalProductLeftMap r.val s.val).restrictScalars R).comp
      (neighborhoodClassifyingMap R I d w S J r) =
    ((principalProductRightMap r.val s.val).restrictScalars R).comp
      (neighborhoodClassifyingMap R I d w S J s) := by
  let _ := principalProductLeftScalars r.val s.val
  let _ := principalProductRightScalars r.val s.val
  let _ := principalProductLeftTower (R := S) r.val s.val
  let _ := principalProductRightTower (R := S) r.val s.val
  let _ := principalProductLeftTower (R := R) r.val s.val
  let _ := principalProductRightTower (R := R) r.val s.val
  exact neighborhoodClassifyingMap_agree R I d w S J (Localization.Away (r.val * s.val)) r s

variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]

/-- Restricting the local chart morphism is computed by its actual localization algebra map. -/
theorem neighborhoodChartMorphism_restrict (r : PolynomialBasisNeighborhoods R I d w S J)
    (t : S) (ht : PrimeSpectrum.basicOpen t ≤ PrimeSpectrum.basicOpen r.val)
    (a : Localization.Away r.val →ₐ[S] Localization.Away t) :
    (basicOpenIsoSpecAway (R := .of S) t).inv ≫ (Spec (.of S)).homOfLE ht ≫
      neighborhoodChartMorphism R I d w S J r =
    Spec.map (CommRingCat.ofHom
      (((a.restrictScalars R).comp (neighborhoodClassifyingMap R I d w S J r)).toRingHom)) := by
  have h := congrArg (fun f ↦ f ≫ Spec.map
    (CommRingCat.ofHom (R := ChartRing R I d w)
      (neighborhoodClassifyingMap R I d w S J r).toRingHom))
    (principal_restriction_SpecMap r.val t ht a)
  simp only [Category.assoc, ← Spec.map_comp] at h
  refine h.trans ?_
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rfl

/-- The local scheme morphisms agree on their product principal neighborhood. -/
theorem neighborhoodChartMorphism_product_agree
    (r s : PolynomialBasisNeighborhoods R I d w S J)
    (hr : PrimeSpectrum.basicOpen (r.val * s.val) ≤ PrimeSpectrum.basicOpen r.val)
    (hs : PrimeSpectrum.basicOpen (r.val * s.val) ≤ PrimeSpectrum.basicOpen s.val) :
    (Spec (.of S)).homOfLE hr ≫ neighborhoodChartMorphism R I d w S J r =
      (Spec (.of S)).homOfLE hs ≫ neighborhoodChartMorphism R I d w S J s := by
  apply (cancel_epi (basicOpenIsoSpecAway (R := .of S) (r.val * s.val)).inv).mp
  rw [neighborhoodChartMorphism_restrict R I d w S J r _ hr
      (principalProductLeftMap r.val s.val),
    neighborhoodChartMorphism_restrict R I d w S J s _ hs
      (principalProductRightMap r.val s.val)]
  exact congrArg (fun f : ChartRing R I d w →ₐ[R] Localization.Away (r.val * s.val) ↦
    Spec.map (CommRingCat.ofHom (R := ChartRing R I d w)
      (S := Localization.Away (r.val * s.val)) f.toRingHom))
    (principal_product_classifying_agree R I d w S J r s)

end FLT.Mazur.HilbertChart
