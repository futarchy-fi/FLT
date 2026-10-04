/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCanonicalOverlapRing
public import FLT.Mazur.PolygonOneGonPuncturedPullback
public import FLT.Mazur.PolygonSplitPuncturedPullback

/-!
# Canonical cubic equations on the concrete punctured node rings

The actual chosen denominator is retained in each localization. The right
branch acts on Laurent polynomials by inversion; the one-gon acts by its
Möbius substitution. These are identities for the actual cubic chart map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open PolygonPinching PolygonNodeAffineCharts PolygonNodeEqualizer PolygonNodeLocalization
open PolygonNodePresentation LocalizationJointRestriction
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (x : Spec (.of K))

/-- The equation on the first punctured branch of the chosen split-node open. -/
lemma split_left_canonical_equation (k : Fin (n * 3 + 1 + 1)) :
    let s := splitDenominator K n hn p q h a hn₂ i x
    let j := splitDenominatorChart K n hn p q h a hn₂ i x
    let c := affineCanonicalChartRingMap K n hn p q h a j
      (splitDenominatorChart_range_subset K n hn p q h a hn₂ i x)
    let t := torusChartRingMap K n hn p q h a i
    let g := algebraMap (LaurentPolynomial K) (Localization.Away (leftMap s))
    restriction leftMap s
        (c (ProjectiveSpace.coordinate K _ (canonicalIndex.{u} n) k)) *
      g (t (ProjectiveSpace.coordinate K _ (interiorIndex.{u} n) (canonicalIndex.{u} n))) =
      g (t (ProjectiveSpace.coordinate K _ (interiorIndex.{u} n) k)) :=
  canonical_overlap_ring K n hn p q h a _
    (splitDenominatorChart_range_subset K n hn p q h a hn₂ i x) i _ _
    (split_left_punctured_isPullback K n hn p q h a hn₂ i x) k

/-- The successor equation includes inversion of its original Laurent coordinate. -/
lemma split_right_canonical_equation (k : Fin (n * 3 + 1 + 1)) :
    let s := splitDenominator K n hn p q h a hn₂ i x
    let j := splitDenominatorChart K n hn p q h a hn₂ i x
    let c := affineCanonicalChartRingMap K n hn p q h a j
      (splitDenominatorChart_range_subset K n hn p q h a hn₂ i x)
    let t := torusChartRingMap K n hn p q h a (finRotate n i)
    let g := (algebraMap (LaurentPolynomial K) (Localization.Away (rightMap s))).comp
      (LaurentPolynomial.invert (R := K)).toRingHom
    restriction rightMap s
        (c (ProjectiveSpace.coordinate K _ (canonicalIndex.{u} n) k)) *
      g (t (ProjectiveSpace.coordinate K _ (interiorIndex.{u} n) (canonicalIndex.{u} n))) =
      g (t (ProjectiveSpace.coordinate K _ (interiorIndex.{u} n) k)) :=
  canonical_overlap_ring K n hn p q h a _
    (splitDenominatorChart_range_subset K n hn p q h a hn₂ i x) (finRotate n i) _ _
    (split_right_punctured_spec_isPullback K n hn p q h a hn₂ i x) k

end PolygonCubicSections
namespace PolygonCubicSections
open PolygonPinching PolygonNodeAffineCharts PolygonNodePresentation LocalizationJointRestriction
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (x : Spec (.of K))

/-- The self-incidence equation uses the genuine one-gon Möbius coordinate change. -/
lemma one_canonical_equation (i : Fin 1) (k : Fin (1 * 3 + 1 + 1)) :
    let s := oneDenominator K hn p q h a x
    let j := oneDenominatorChart K hn p q h a x
    let c := affineCanonicalChartRingMap K 1 hn p q h a j
      (oneDenominatorChart_range_subset K hn p q h a x)
    let t := torusChartRingMap K 1 hn p q h a i
    let g := (algebraMap (OneGonTransition.puncture K)
      (Localization.Away (bPunctureMap s))).comp (OneGonTransition.overlapMap K)
    restriction bPunctureMap s
        (c (ProjectiveSpace.coordinate K _ (canonicalIndex.{u} 1) k)) *
      g (t (ProjectiveSpace.coordinate K _ (interiorIndex.{u} 1) (canonicalIndex.{u} 1))) =
      g (t (ProjectiveSpace.coordinate K _ (interiorIndex.{u} 1) k)) :=
  canonical_overlap_ring K 1 hn p q h a _
    (oneDenominatorChart_range_subset K hn p q h a x) i _ _
    (one_punctured_spec_isPullback K hn p q h a x i) k

end FLT.Mazur.PolygonCubicSections
