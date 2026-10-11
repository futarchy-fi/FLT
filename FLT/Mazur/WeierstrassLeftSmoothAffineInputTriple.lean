/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAffineOutputFactorization
public import FLT.Mazur.WeierstrassLeftSmoothAffineOutputFactorization
public import FLT.Mazur.WeierstrassLeftSmoothAffineOuterTriple

/-!
# Whole-cubic action associativity for every four affine-input chart choices

The outer laws give affine presentations of the two actual inner sums.
The overlap theorem forces both inner output units, even when an inner chart
is reciprocal. Ordinary replacement then proves associativity, with no
output-unit hypothesis and no restriction on the final output chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- All ordinary/reciprocal combinations associate on their actual common input domain. -/
theorem leftSmoothTripleAdd_affineInputs {X : Scheme.{u}}
    (t : X ⟶ leftSmoothTriple W) (i j k l : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W i))
    (g : X ⟶ Spec (additionChartRing W j))
    (h : X ⟶ Spec (additionChartRing W k))
    (q : X ⟶ Spec (additionChartRing W l))
    (hf : f ≫ additionGlobalDomain W i =
      t ≫ leftSmoothTriplePair W ≫ smoothFactorsInclusion W)
    (hg : g ≫ additionGlobalDomain W j =
      t ≫ leftSmoothTripleLastPair W ≫ leftSmoothFactorsInclusion W)
    (hh : h ≫ additionGlobalDomain W k =
      t ≫ leftSmoothAddFirstPair W ≫ leftSmoothFactorsInclusion W)
    (hq : q ≫ additionGlobalDomain W l =
      t ≫ leftSmoothAddLastPair W ≫ leftSmoothFactorsInclusion W) :
    t ≫ leftSmoothTripleAddLeft W = t ≫ leftSmoothTripleAddRight W := by
  have hh₁ := congrArg (fun a => a ≫ pullback.fst
    (integralCurveStructure W) (integralCurveStructure W)) hh
  have hq₂ := congrArg (fun a => a ≫ pullback.snd
    (integralCurveStructure W) (integralCurveStructure W)) hq
  simp only [Category.assoc, additionGlobalDomain_fst,
    leftSmoothFactorsInclusion_fst, leftSmoothAddFirstPair_fst_assoc] at hh₁
  simp only [Category.assoc, additionGlobalDomain_snd,
    leftSmoothFactorsInclusion_snd, leftSmoothAddLastPair_snd] at hq₂
  have hfa : (t ≫ leftSmoothTriplePair W) ≫ smoothFactorAddition W ≫
      (integralSmoothOpen W).ι =
      (h ≫ additionAffineInputLeft W k) ≫ integralCurveChart W 2 := by
    simpa only [Category.assoc] using hh₁.symm
  have hga : (t ≫ leftSmoothTripleLastPair W) ≫ leftSmoothFactorAddition W =
      (q ≫ additionAffineInputRight W l) ≫ integralCurveChart W 2 := by
    simpa only [Category.assoc] using hq₂.symm
  obtain ⟨f', hf'⟩ := exists_ordinary_of_smoothAddition_affine W
    (t ≫ leftSmoothTriplePair W) i f _ hf hfa
  obtain ⟨g', hg'⟩ := exists_ordinary_of_leftSmoothAddition_affine W
    (t ≫ leftSmoothTripleLastPair W) j g _ hg hga
  exact leftSmoothTripleAdd_affineOuter W t
    (additionOrdinaryChoice i) (additionOrdinaryChoice j) k l f' g' h q
    (hf'.trans hf) (hg'.trans hg) hh hq

end FLT.Mazur.WeierstrassIntegralChart
