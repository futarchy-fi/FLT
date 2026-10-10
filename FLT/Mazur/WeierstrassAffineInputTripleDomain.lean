/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineInputTripleGlobal

/-!
# Genuine triple intersections for all affine-input charts

Four pullbacks intersect the original ordinary or reciprocal chart domains.
Both inner units follow from the outer input projections, so no output
localization is imposed. These opens are not asserted to cover the triple product.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- First affine-input inner domain, pulled back to the true triple product. -/
abbrev AffineInputTripleFirst (i : AdditionChartIndex) :=
  pullback (additionGlobalDomain W i) (integralCurveTriplePair W)

/-- Its original triple input. -/
abbrev affineInputTripleFirstMap (i : AdditionChartIndex) :
    AffineInputTripleFirst W i ⟶ integralCurveTriple W :=
  pullback.snd _ _

/-- Impose the second affine-input inner domain on the first. -/
abbrev AffineInputTripleInner (i j : AdditionChartIndex) :=
  pullback (additionGlobalDomain W j)
    (affineInputTripleFirstMap W i ≫ integralCurveTripleLastPair W)

/-- The common inner domain retains its original triple input. -/
def affineInputTripleInnerMap (i j : AdditionChartIndex) :
    AffineInputTripleInner W i j ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ affineInputTripleFirstMap W i

variable (hΔ : IsUnit W.Δ)

/-- Impose the actual left outer affine-input domain. -/
abbrev AffineInputTripleOuterLeft (i j k : AdditionChartIndex) :=
  pullback (additionGlobalDomain W k)
    (affineInputTripleInnerMap W i j ≫ integralCurveAddFirstPair W hΔ)

/-- The left outer domain retains the same triple. -/
def affineInputTripleOuterLeftMap (i j k : AdditionChartIndex) :
    AffineInputTripleOuterLeft W hΔ i j k ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ affineInputTripleInnerMap W i j

/-- The genuine intersection where both outer additions use affine-input charts. -/
abbrev AffineInputTripleDomain (i j k l : AdditionChartIndex) :=
  pullback (additionGlobalDomain W l)
    (affineInputTripleOuterLeftMap W hΔ i j k ≫ integralCurveAddLastPair W hΔ)

/-- Inclusion of the actual four-domain intersection into the triple product. -/
def affineInputTripleDomainMap (i j k l : AdditionChartIndex) :
    AffineInputTripleDomain W hΔ i j k l ⟶ integralCurveTriple W :=
  pullback.snd _ _ ≫ affineInputTripleOuterLeftMap W hΔ i j k

instance affineInputTripleDomainMap_isOpenImmersion (i j k l : AdditionChartIndex) :
    IsOpenImmersion (affineInputTripleDomainMap W hΔ i j k l) := by
  unfold affineInputTripleDomainMap affineInputTripleOuterLeftMap affineInputTripleInnerMap
  infer_instance

/-- Projection to the first affine-input inner chart. -/
def affineInputTripleDomainFirst (i j k l : AdditionChartIndex) :
    AffineInputTripleDomain W hΔ i j k l ⟶
    Spec (additionChartRing W i) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the second affine-input inner chart. -/
def affineInputTripleDomainLast (i j k l : AdditionChartIndex) :
    AffineInputTripleDomain W hΔ i j k l ⟶
    Spec (additionChartRing W j) :=
  pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the left outer affine-input chart. -/
def affineInputTripleDomainLeft (i j k l : AdditionChartIndex) :
    AffineInputTripleDomain W hΔ i j k l ⟶
    Spec (additionChartRing W k) :=
  pullback.snd _ _ ≫ pullback.fst _ _

/-- Projection to the right outer affine-input chart. -/
abbrev affineInputTripleDomainRight (i j k l : AdditionChartIndex) :
    AffineInputTripleDomain W hΔ i j k l ⟶
    Spec (additionChartRing W l) := pullback.fst _ _

/-- The first chart carries the original first pair. -/
theorem affineInputTripleDomainFirst_inputs (i j k l : AdditionChartIndex) :
    affineInputTripleDomainFirst W hΔ i j k l ≫ additionGlobalDomain W i =
      affineInputTripleDomainMap W hΔ i j k l ≫ integralCurveTriplePair W := by
  simp only [affineInputTripleDomainFirst, affineInputTripleDomainMap,
    affineInputTripleOuterLeftMap, affineInputTripleInnerMap, Category.assoc]
  rw [pullback.condition]

/-- The last chart carries the original last pair. -/
theorem affineInputTripleDomainLast_inputs (i j k l : AdditionChartIndex) :
    affineInputTripleDomainLast W hΔ i j k l ≫ additionGlobalDomain W j =
      affineInputTripleDomainMap W hΔ i j k l ≫ integralCurveTripleLastPair W := by
  simp only [affineInputTripleDomainLast, affineInputTripleDomainMap,
    affineInputTripleOuterLeftMap, affineInputTripleInnerMap, Category.assoc]
  simp only [pullback.condition]

/-- The left outer chart carries the actual first sum and third input. -/
theorem affineInputTripleDomainLeft_inputs (i j k l : AdditionChartIndex) :
    affineInputTripleDomainLeft W hΔ i j k l ≫ additionGlobalDomain W k =
      affineInputTripleDomainMap W hΔ i j k l ≫ integralCurveAddFirstPair W hΔ := by
  simp only [affineInputTripleDomainLeft, affineInputTripleDomainMap,
    affineInputTripleOuterLeftMap, Category.assoc]
  simp only [pullback.condition]

/-- The right outer chart carries the actual first input and last sum. -/
theorem affineInputTripleDomainRight_inputs (i j k l : AdditionChartIndex) :
    affineInputTripleDomainRight W hΔ i j k l ≫ additionGlobalDomain W l =
      affineInputTripleDomainMap W hΔ i j k l ≫ integralCurveAddLastPair W hΔ := by
  exact pullback.condition.trans (Category.assoc _ _ _).symm

/-- Associativity holds on the genuine four-chart intersection. -/
theorem affineInputTripleDomain_associativity (i j k l : AdditionChartIndex) :
    affineInputTripleDomainMap W hΔ i j k l ≫ integralCurveTripleAddLeft W hΔ =
      affineInputTripleDomainMap W hΔ i j k l ≫ integralCurveTripleAddRight W hΔ :=
  integralCurveTripleAdd_affineInputs W hΔ (affineInputTripleDomainMap W hΔ i j k l) i j k l
    (affineInputTripleDomainFirst W hΔ i j k l) (affineInputTripleDomainLast W hΔ i j k l)
    (affineInputTripleDomainLeft W hΔ i j k l) (affineInputTripleDomainRight W hΔ i j k l)
    (affineInputTripleDomainFirst_inputs W hΔ i j k l)
    (affineInputTripleDomainLast_inputs W hΔ i j k l)
    (affineInputTripleDomainLeft_inputs W hΔ i j k l)
    (affineInputTripleDomainRight_inputs W hΔ i j k l)

end FLT.Mazur.WeierstrassIntegralChart
