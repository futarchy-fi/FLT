/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAffineOutputFactorization
public import FLT.Mazur.WeierstrassSmoothAffineOuterTriple

/-!
# Associativity for every four affine-input chart choices

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
theorem smoothFactorTripleAdd_affineInputs {X : Scheme.{u}}
    (t : X ⟶ smoothFactorTriple W) (i j k l : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W i))
    (g : X ⟶ Spec (additionChartRing W j))
    (h : X ⟶ Spec (additionChartRing W k))
    (q : X ⟶ Spec (additionChartRing W l))
    (hf : f ≫ additionGlobalDomain W i =
      t ≫ smoothFactorTriplePair W ≫ smoothFactorsInclusion W)
    (hg : g ≫ additionGlobalDomain W j =
      t ≫ smoothFactorTripleLastPair W ≫ smoothFactorsInclusion W)
    (hh : h ≫ additionGlobalDomain W k =
      t ≫ smoothFactorAddFirstPair W ≫ smoothFactorsInclusion W)
    (hq : q ≫ additionGlobalDomain W l =
      t ≫ smoothFactorAddLastPair W ≫ smoothFactorsInclusion W) :
    t ≫ smoothFactorTripleAddLeft W = t ≫ smoothFactorTripleAddRight W := by
  have hh₁ := congrArg (fun a => a ≫ pullback.fst
    (integralCurveStructure W) (integralCurveStructure W)) hh
  have hq₂ := congrArg (fun a => a ≫ pullback.snd
    (integralCurveStructure W) (integralCurveStructure W)) hq
  simp only [Category.assoc, additionGlobalDomain_fst,
    smoothFactorsInclusion_fst, smoothFactorAddFirstPair_fst_assoc] at hh₁
  simp only [Category.assoc, additionGlobalDomain_snd,
    smoothFactorsInclusion_snd, smoothFactorAddLastPair_snd_assoc] at hq₂
  have hfa : (t ≫ smoothFactorTriplePair W) ≫ smoothFactorAddition W ≫
      (integralSmoothOpen W).ι =
      (h ≫ additionAffineInputLeft W k) ≫ integralCurveChart W 2 := by
    simpa only [Category.assoc] using hh₁.symm
  have hga : (t ≫ smoothFactorTripleLastPair W) ≫ smoothFactorAddition W ≫
      (integralSmoothOpen W).ι =
      (q ≫ additionAffineInputRight W l) ≫ integralCurveChart W 2 := by
    simpa only [Category.assoc] using hq₂.symm
  obtain ⟨f', hf'⟩ := exists_ordinary_of_smoothAddition_affine W
    (t ≫ smoothFactorTriplePair W) i f _ hf hfa
  obtain ⟨g', hg'⟩ := exists_ordinary_of_smoothAddition_affine W
    (t ≫ smoothFactorTripleLastPair W) j g _ hg hga
  exact smoothFactorTripleAdd_affineOuter W t
    (additionOrdinaryChoice i) (additionOrdinaryChoice j) k l f' g' h q
    (hf'.trans hf) (hg'.trans hg) hh hq

end FLT.Mazur.WeierstrassIntegralChart
