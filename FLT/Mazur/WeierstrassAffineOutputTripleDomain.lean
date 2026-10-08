/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineOutputOpen

/-!
# Genuine triple intersections allowing reciprocal charts with affine output

Four pullbacks cut out the actual open locus of the triple product where the
proved affine-output comparison applies. The projections carry the original inputs;
associativity on this locus needs no supplied compatibility or output equality.
This locus is not asserted to cover the triple product.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- First affine-output inner domain, pulled back to the true triple product. -/
abbrev AffineOutputTripleFirst (i : AdditionChartIndex) :=
  pullback (additionAffineOpenDomain W i) (integralCurveTriplePair W)

/-- Its original triple input. -/
abbrev affineOutputTripleFirstMap (i : AdditionChartIndex) :
    AffineOutputTripleFirst W i ⟶ integralCurveTriple W :=
  pullback.snd _ _

/-- Impose the second affine-output inner domain on the first. -/
abbrev AffineOutputTripleInner (i j : AdditionChartIndex) :=
  pullback (additionAffineOpenDomain W j)
    (affineOutputTripleFirstMap W i ≫ integralCurveTripleLastPair W)

/-- The common inner domain retains its original triple input. -/
def affineOutputTripleInnerMap (i j : AdditionChartIndex) :
    AffineOutputTripleInner W i j ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ affineOutputTripleFirstMap W i

variable (hΔ : IsUnit W.Δ)

/-- Impose the actual left outer affine-output domain. -/
abbrev AffineOutputTripleOuterLeft (i j k : AdditionChartIndex) :=
  pullback (additionAffineOpenDomain W k)
    (affineOutputTripleInnerMap W i j ≫ integralCurveAddFirstPair W hΔ)

/-- The left outer domain retains the same triple. -/
def affineOutputTripleOuterLeftMap (i j k : AdditionChartIndex) :
    AffineOutputTripleOuterLeft W hΔ i j k ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ affineOutputTripleInnerMap W i j

/-- The genuine intersection where both outer additions use affine-output charts. -/
abbrev AffineOutputTripleDomain (i j k l : AdditionChartIndex) :=
  pullback (additionAffineOpenDomain W l)
    (affineOutputTripleOuterLeftMap W hΔ i j k ≫ integralCurveAddLastPair W hΔ)

/-- Inclusion of the actual four-domain intersection into the triple product. -/
def affineOutputTripleDomainMap (i j k l : AdditionChartIndex) :
    AffineOutputTripleDomain W hΔ i j k l ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ affineOutputTripleOuterLeftMap W hΔ i j k

instance affineOutputTripleDomainMap_isOpenImmersion (i j k l : AdditionChartIndex) :
    IsOpenImmersion (affineOutputTripleDomainMap W hΔ i j k l) := by
  unfold affineOutputTripleDomainMap affineOutputTripleOuterLeftMap affineOutputTripleInnerMap
  infer_instance

/-- Projection to the first affine-output inner chart. -/
def affineOutputTripleDomainFirst (i j k l : AdditionChartIndex) :
    AffineOutputTripleDomain W hΔ i j k l ⟶
    Spec (.of (AdditionAffineOpenRing W i)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the second affine-output inner chart. -/
def affineOutputTripleDomainLast (i j k l : AdditionChartIndex) :
    AffineOutputTripleDomain W hΔ i j k l ⟶
    Spec (.of (AdditionAffineOpenRing W j)) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the left outer affine-output chart. -/
def affineOutputTripleDomainLeft (i j k l : AdditionChartIndex) :
    AffineOutputTripleDomain W hΔ i j k l ⟶
    Spec (.of (AdditionAffineOpenRing W k)) :=
  pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the right outer affine-output chart. -/
abbrev affineOutputTripleDomainRight (i j k l : AdditionChartIndex) :
    AffineOutputTripleDomain W hΔ i j k l ⟶
    Spec (.of (AdditionAffineOpenRing W l)) := pullback.fst _ _

/-- The first chart carries the original first pair. -/
theorem affineOutputTripleDomainFirst_inputs (i j k l : AdditionChartIndex) :
    affineOutputTripleDomainFirst W hΔ i j k l ≫ additionAffineOpenDomain W i =
      affineOutputTripleDomainMap W hΔ i j k l ≫ integralCurveTriplePair W := by
  simp only [affineOutputTripleDomainFirst, affineOutputTripleDomainMap,
    affineOutputTripleOuterLeftMap, affineOutputTripleInnerMap, Category.assoc]
  rw [pullback.condition]

/-- The last chart carries the original last pair. -/
theorem affineOutputTripleDomainLast_inputs (i j k l : AdditionChartIndex) :
    affineOutputTripleDomainLast W hΔ i j k l ≫ additionAffineOpenDomain W j =
      affineOutputTripleDomainMap W hΔ i j k l ≫ integralCurveTripleLastPair W := by
  simp only [affineOutputTripleDomainLast, affineOutputTripleDomainMap,
    affineOutputTripleOuterLeftMap, affineOutputTripleInnerMap, Category.assoc]
  simp only [pullback.condition]

/-- The left outer chart carries the actual first sum and third input. -/
theorem affineOutputTripleDomainLeft_inputs (i j k l : AdditionChartIndex) :
    affineOutputTripleDomainLeft W hΔ i j k l ≫ additionAffineOpenDomain W k =
      affineOutputTripleDomainMap W hΔ i j k l ≫ integralCurveAddFirstPair W hΔ := by
  simp only [affineOutputTripleDomainLeft, affineOutputTripleDomainMap,
    affineOutputTripleOuterLeftMap, Category.assoc]
  simp only [pullback.condition]

/-- The right outer chart carries the actual first input and last sum. -/
theorem affineOutputTripleDomainRight_inputs (i j k l : AdditionChartIndex) :
    affineOutputTripleDomainRight W hΔ i j k l ≫ additionAffineOpenDomain W l =
      affineOutputTripleDomainMap W hΔ i j k l ≫ integralCurveAddLastPair W hΔ := by
  exact pullback.condition.trans (Category.assoc _ _ _).symm

/-- Associativity holds on the genuine four-chart intersection. -/
theorem affineOutputTripleDomain_associativity (i j k l : AdditionChartIndex) :
    affineOutputTripleDomainMap W hΔ i j k l ≫ integralCurveTripleAddLeft W hΔ =
      affineOutputTripleDomainMap W hΔ i j k l ≫ integralCurveTripleAddRight W hΔ :=
  integralCurveTripleAdd_affineOpen W hΔ (affineOutputTripleDomainMap W hΔ i j k l) i j k l
    (affineOutputTripleDomainFirst W hΔ i j k l) (affineOutputTripleDomainLast W hΔ i j k l)
    (affineOutputTripleDomainLeft W hΔ i j k l) (affineOutputTripleDomainRight W hΔ i j k l)
    (affineOutputTripleDomainFirst_inputs W hΔ i j k l)
    (affineOutputTripleDomainLast_inputs W hΔ i j k l)
    (affineOutputTripleDomainLeft_inputs W hΔ i j k l)
    (affineOutputTripleDomainRight_inputs W hΔ i j k l)

end FLT.Mazur.WeierstrassIntegralChart
