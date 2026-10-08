/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineOutputDomains
public import FLT.Mazur.WeierstrassAllOrdinaryTripleGlobal
public import FLT.Mazur.WeierstrassReciprocalTripleGlobal
public import FLT.Mazur.WeierstrassMixedLeftReciprocalGlobal
public import FLT.Mazur.WeierstrassMixedRightReciprocalGlobal

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
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Ordinary inner sums associate with every pair of affine-input outer charts. -/
theorem integralCurveTripleAdd_affineOuter {X : Scheme.{u}}
    (t : X ⟶ integralCurveTriple W) (b c : Bool) (i j : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (ordinaryIndex c)))
    (h : X ⟶ Spec (additionChartRing W i))
    (k : X ⟶ Spec (additionChartRing W j))
    (hf : f ≫ ordinaryGlobalDomain W b = t ≫ integralCurveTriplePair W)
    (hg : g ≫ ordinaryGlobalDomain W c = t ≫ integralCurveTripleLastPair W)
    (hh : h ≫ additionGlobalDomain W i = t ≫ integralCurveAddFirstPair W hΔ)
    (hk : k ≫ additionGlobalDomain W j = t ≫ integralCurveAddLastPair W hΔ) :
    t ≫ integralCurveTripleAddLeft W hΔ = t ≫ integralCurveTripleAddRight W hΔ := by
  cases i <;> cases j
  · exact integralCurveTripleAdd_allOrdinary W hΔ t b c false false
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_allOrdinary W hΔ t b c false true
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_mixedRightReciprocal W hΔ t b c false false
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_mixedRightReciprocal W hΔ t b c false true
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_allOrdinary W hΔ t b c true false
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_allOrdinary W hΔ t b c true true
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_mixedRightReciprocal W hΔ t b c true false
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_mixedRightReciprocal W hΔ t b c true true
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_mixedLeftReciprocal W hΔ t b c false false
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_mixedLeftReciprocal W hΔ t b c false true
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_reciprocals W hΔ t b c false false
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_reciprocals W hΔ t b c false true
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_mixedLeftReciprocal W hΔ t b c true false
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_mixedLeftReciprocal W hΔ t b c true true
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_reciprocals W hΔ t b c true false
      f g h k hf hg hh hk
  · exact integralCurveTripleAdd_reciprocals W hΔ t b c true true
      f g h k hf hg hh hk

end FLT.Mazur.WeierstrassIntegralChart
