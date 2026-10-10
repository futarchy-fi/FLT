/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineOutputDomains
public import FLT.Mazur.WeierstrassAllOrdinaryTripleGlobal

/-!
# Associativity for ordinary and reciprocal charts with affine outputs

Any of the four laws may use an ordinary or reciprocal chart. If each output
z-coordinate is invertible, replacing each domain by its ordinary chart
proves equality of the two actual global sums on the original common scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The actual iterated additions agree on all affine-output chart combinations. -/
theorem integralCurveTripleAdd_affineOutputs {X : Scheme.{u}}
    (t : X ⟶ integralCurveTriple W) (i j k l : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W i))
    (g : X ⟶ Spec (additionChartRing W j))
    (h : X ⟶ Spec (additionChartRing W k))
    (q : X ⟶ Spec (additionChartRing W l))
    (hf : f ≫ additionGlobalDomain W i = t ≫ integralCurveTriplePair W)
    (hg : g ≫ additionGlobalDomain W j = t ≫ integralCurveTripleLastPair W)
    (hh : h ≫ additionGlobalDomain W k = t ≫ integralCurveAddFirstPair W hΔ)
    (hq : q ≫ additionGlobalDomain W l = t ≫ integralCurveAddLastPair W hΔ)
    (fz : IsUnit (specSectionHom f
      (additionChartAlgOutput W i (coord W (additionChartOutput i) 2))))
    (gz : IsUnit (specSectionHom g
      (additionChartAlgOutput W j (coord W (additionChartOutput j) 2))))
    (hz : IsUnit (specSectionHom h
      (additionChartAlgOutput W k (coord W (additionChartOutput k) 2))))
    (qz : IsUnit (specSectionHom q
      (additionChartAlgOutput W l (coord W (additionChartOutput l) 2)))) :
    t ≫ integralCurveTripleAddLeft W hΔ = t ≫ integralCurveTripleAddRight W hΔ :=
  integralCurveTripleAdd_allOrdinary W hΔ t
    (additionOrdinaryChoice i) (additionOrdinaryChoice j)
    (additionOrdinaryChoice k) (additionOrdinaryChoice l)
    (additionAffineOutputScheme W i f fz) (additionAffineOutputScheme W j g gz)
    (additionAffineOutputScheme W k h hz) (additionAffineOutputScheme W l q qz)
    ((additionAffineOutputScheme_inputs W i f fz).trans hf)
    ((additionAffineOutputScheme_inputs W j g gz).trans hg)
    ((additionAffineOutputScheme_inputs W k h hz).trans hh)
    ((additionAffineOutputScheme_inputs W l q qz).trans hq)

end FLT.Mazur.WeierstrassIntegralChart
