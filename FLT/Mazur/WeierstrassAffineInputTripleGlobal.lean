/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineInputFactorization
public import FLT.Mazur.WeierstrassAffineOuterTripleGlobal

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
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- All ordinary/reciprocal combinations associate on their actual common input domain. -/
theorem integralCurveTripleAdd_affineInputs {X : Scheme.{u}}
    (t : X ⟶ integralCurveTriple W) (i j k l : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W i))
    (g : X ⟶ Spec (additionChartRing W j))
    (h : X ⟶ Spec (additionChartRing W k))
    (q : X ⟶ Spec (additionChartRing W l))
    (hf : f ≫ additionGlobalDomain W i = t ≫ integralCurveTriplePair W)
    (hg : g ≫ additionGlobalDomain W j = t ≫ integralCurveTripleLastPair W)
    (hh : h ≫ additionGlobalDomain W k = t ≫ integralCurveAddFirstPair W hΔ)
    (hq : q ≫ additionGlobalDomain W l = t ≫ integralCurveAddLastPair W hΔ) :
    t ≫ integralCurveTripleAddLeft W hΔ = t ≫ integralCurveTripleAddRight W hΔ := by
  have hh₁ := congrArg (fun a => a ≫ pullback.fst
    (integralCurveStructure W) (integralCurveStructure W)) hh
  have hq₂ := congrArg (fun a => a ≫ pullback.snd
    (integralCurveStructure W) (integralCurveStructure W)) hq
  simp only [Category.assoc, additionGlobalDomain_fst,
    integralCurveAddFirstPair_fst] at hh₁
  simp only [Category.assoc, additionGlobalDomain_snd,
    integralCurveAddLastPair_snd] at hq₂
  have hfa : f ≫ additionGlobalDomain W i ≫ integralCurveAddition W hΔ =
      (h ≫ additionAffineInputLeft W k) ≫ integralCurveChart W 2 := by
    rw [← Category.assoc, hf, Category.assoc]
    exact hh₁.symm.trans (Category.assoc _ _ _).symm
  have hga : g ≫ additionGlobalDomain W j ≫ integralCurveAddition W hΔ =
      (q ≫ additionAffineInputRight W l) ≫ integralCurveChart W 2 := by
    rw [← Category.assoc, hg, Category.assoc]
    exact hq₂.symm.trans (Category.assoc _ _ _).symm
  obtain ⟨f', hf'⟩ := exists_ordinary_of_addition_affine W hΔ i f _ hfa
  obtain ⟨g', hg'⟩ := exists_ordinary_of_addition_affine W hΔ j g _ hga
  exact integralCurveTripleAdd_affineOuter W hΔ t
    (additionOrdinaryChoice i) (additionOrdinaryChoice j) k l f' g' h q
    (hf'.trans hf) (hg'.trans hg) hh hq

end FLT.Mazur.WeierstrassIntegralChart
