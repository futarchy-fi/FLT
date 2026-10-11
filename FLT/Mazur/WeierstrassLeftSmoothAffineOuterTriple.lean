/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineOutputDomains
public import FLT.Mazur.WeierstrassLeftSmoothAllOrdinaryTriple
public import FLT.Mazur.WeierstrassLeftSmoothReciprocalTriple
public import FLT.Mazur.WeierstrassLeftSmoothMixedLeftReciprocalTriple
public import FLT.Mazur.WeierstrassLeftSmoothMixedRightReciprocalTriple

/-!
# All affine-input outer charts with ordinary inner sums

The four proved combinations of ordinary and reciprocal outer laws exhaust
all affine-input outer charts, including their non-affine outputs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Ordinary inner sums associate with every pair of affine-input outer charts. -/
theorem leftSmoothTripleAdd_affineOuter {X : Scheme.{u}}
    (t : X ⟶ leftSmoothTriple W) (b c : Bool) (i j : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (ordinaryIndex c)))
    (h : X ⟶ Spec (additionChartRing W i))
    (k : X ⟶ Spec (additionChartRing W j))
    (hf : f ≫ ordinaryGlobalDomain W b =
      t ≫ leftSmoothTriplePair W ≫ smoothFactorsInclusion W)
    (hg : g ≫ ordinaryGlobalDomain W c =
      t ≫ leftSmoothTripleLastPair W ≫ leftSmoothFactorsInclusion W)
    (hh : h ≫ additionGlobalDomain W i =
      t ≫ leftSmoothAddFirstPair W ≫ leftSmoothFactorsInclusion W)
    (hk : k ≫ additionGlobalDomain W j =
      t ≫ leftSmoothAddLastPair W ≫ leftSmoothFactorsInclusion W) :
    t ≫ leftSmoothTripleAddLeft W = t ≫ leftSmoothTripleAddRight W := by
  cases i <;> cases j
  · exact leftSmoothTripleAdd_allOrdinary W t b c false false
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_allOrdinary W t b c false true
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_mixedRightReciprocal W t b c false false
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_mixedRightReciprocal W t b c false true
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_allOrdinary W t b c true false
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_allOrdinary W t b c true true
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_mixedRightReciprocal W t b c true false
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_mixedRightReciprocal W t b c true true
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_mixedLeftReciprocal W t b c false false
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_mixedLeftReciprocal W t b c false true
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_reciprocals W t b c false false
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_reciprocals W t b c false true
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_mixedLeftReciprocal W t b c true false
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_mixedLeftReciprocal W t b c true true
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_reciprocals W t b c true false
      f g h k hf hg hh hk
  · exact leftSmoothTripleAdd_reciprocals W t b c true true
      f g h k hf hg hh hk

end FLT.Mazur.WeierstrassIntegralChart
