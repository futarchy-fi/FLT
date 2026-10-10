/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAffinePairDescent
public import FLT.Mazur.WeierstrassSmoothAffineInputTriple

/-!
# Descent of associativity from the four affine-input addition domains

Pulling back the genuine four-chart cover for each pair removes every choice
of secant or tangent denominator. The remaining geometric hypotheses are only
that both original pairs and both intermediate pairs have affine inputs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Associativity descends to any scheme carrying affine presentations of the four pairs. -/
theorem smoothFactorTripleAdd_of_affinePairs {X : Scheme.{u}}
    (t : X ⟶ smoothFactorTriple W)
    (a b c d : X ⟶ Spec (.of (AffineProduct W)))
    (ha : a ≫ integralCurveProductChart W false false =
      t ≫ smoothFactorTriplePair W ≫ smoothFactorsInclusion W)
    (hb : b ≫ integralCurveProductChart W false false =
      t ≫ smoothFactorTripleLastPair W ≫ smoothFactorsInclusion W)
    (hc : c ≫ integralCurveProductChart W false false =
      t ≫ smoothFactorAddFirstPair W ≫ smoothFactorsInclusion W)
    (hd : d ≫ integralCurveProductChart W false false =
      t ≫ smoothFactorAddLastPair W ≫ smoothFactorsInclusion W) :
    t ≫ smoothFactorTripleAddLeft W = t ≫ smoothFactorTripleAddRight W := by
  apply smoothAffinePair_hom_ext W (t ≫ smoothFactorTriplePair W) a ha
  intro i X₁ u f hf
  have hf' : f ≫ additionGlobalDomain W i =
      u ≫ t ≫ smoothFactorTriplePair W ≫ smoothFactorsInclusion W := by
    rw [additionGlobalDomain, ← Category.assoc, hf, Category.assoc, ha]
  apply smoothAffinePair_hom_ext W (u ≫ t ≫ smoothFactorTripleLastPair W) (u ≫ b)
    (by simp only [Category.assoc, hb])
  intro j X₂ v g hg
  have hg' : g ≫ additionGlobalDomain W j =
      v ≫ u ≫ t ≫ smoothFactorTripleLastPair W ≫ smoothFactorsInclusion W := by
    calc
      _ = (v ≫ u ≫ b) ≫ integralCurveProductChart W false false :=
        congrArg (fun e => e ≫ integralCurveProductChart W false false) hg
      _ = _ := by simp only [Category.assoc, hb]
  apply smoothAffinePair_hom_ext W (v ≫ u ≫ t ≫ smoothFactorAddFirstPair W) (v ≫ u ≫ c)
    (by simp only [Category.assoc, hc])
  intro k X₃ w h hh
  have hh' : h ≫ additionGlobalDomain W k =
      w ≫ v ≫ u ≫ t ≫ smoothFactorAddFirstPair W ≫ smoothFactorsInclusion W := by
    calc
      _ = (w ≫ v ≫ u ≫ c) ≫ integralCurveProductChart W false false :=
        congrArg (fun e => e ≫ integralCurveProductChart W false false) hh
      _ = _ := by simp only [Category.assoc, hc]
  apply smoothAffinePair_hom_ext W (w ≫ v ≫ u ≫ t ≫ smoothFactorAddLastPair W)
    (w ≫ v ≫ u ≫ d) (by simp only [Category.assoc, hd])
  intro l X₄ x q hq
  have hq' : q ≫ additionGlobalDomain W l =
      x ≫ w ≫ v ≫ u ≫ t ≫ smoothFactorAddLastPair W ≫ smoothFactorsInclusion W := by
    calc
      _ = (x ≫ w ≫ v ≫ u ≫ d) ≫ integralCurveProductChart W false false :=
        congrArg (fun e => e ≫ integralCurveProductChart W false false) hq
      _ = _ := by simp only [Category.assoc, hd]
  have he := smoothFactorTripleAdd_affineInputs W (x ≫ w ≫ v ≫ u ≫ t) i j k l
    (x ≫ w ≫ v ≫ f) (x ≫ w ≫ g) (x ≫ h) q
    (by simp only [Category.assoc, hf']) (by simp only [Category.assoc, hg'])
    (by simp only [Category.assoc, hh']) (by simpa only [Category.assoc] using hq')
  simpa only [Category.assoc] using he

end FLT.Mazur.WeierstrassIntegralChart
