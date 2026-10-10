/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleInnerAdditionCover

/-!
# Simultaneous local formulas for all four additions in associativity

Refine the outer-addition cover by the genuine inner-addition cover. The result
is an actual open cover of the triple fiber product with projections to all
four original addition domains and all four original local output identities.
No local or global associativity identity is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Restrict both inner domains to one common outer-addition domain. -/
def integralCurveTripleFullRefinement (i : (integralCurveTripleAdditionCover W hΔ).I₀) :
    ((integralCurveTripleAdditionCover W hΔ).X i).OpenCover :=
  (integralCurveTripleInnerCover W hΔ).pullback₁ ((integralCurveTripleAdditionCover W hΔ).f i)

/-- A genuine common cover on which all four addition formulas are available. -/
def integralCurveTripleFullCover : (integralCurveTriple W).OpenCover :=
  (integralCurveTripleAdditionCover W hΔ).bind (integralCurveTripleFullRefinement W hΔ)

/-- Projection from the full refinement to the outer-addition domain. -/
def integralCurveTripleFullOuter (i : (integralCurveTripleFullCover W hΔ).I₀) :
    (integralCurveTripleFullCover W hΔ).X i ⟶
      (integralCurveTripleAdditionCover W hΔ).X i.1 :=
  (integralCurveTripleFullRefinement W hΔ i.1).f i.2

/-- Projection from the full refinement to the common inner-addition domain. -/
def integralCurveTripleFullInner (i : (integralCurveTripleFullCover W hΔ).I₀) :
    (integralCurveTripleFullCover W hΔ).X i ⟶
      (integralCurveTripleInnerCover W hΔ).X i.2 :=
  Scheme.Cover.pullbackHom (integralCurveTripleInnerCover W hΔ)
    ((integralCurveTripleAdditionCover W hΔ).f i.1) i.2

/-- The outer projection retains the original triple input. -/
theorem integralCurveTripleFullOuter_inputs (i : (integralCurveTripleFullCover W hΔ).I₀) :
    integralCurveTripleFullOuter W hΔ i ≫ (integralCurveTripleAdditionCover W hΔ).f i.1 =
      (integralCurveTripleFullCover W hΔ).f i := rfl

/-- The inner projection retains the same original triple input. -/
theorem integralCurveTripleFullInner_inputs (i : (integralCurveTripleFullCover W hΔ).I₀) :
    integralCurveTripleFullInner W hΔ i ≫ (integralCurveTripleInnerCover W hΔ).f i.2 =
      (integralCurveTripleFullCover W hΔ).f i :=
  Scheme.Cover.pullbackHom_map (integralCurveTripleInnerCover W hΔ)
    ((integralCurveTripleAdditionCover W hΔ).f i.1) i.2

/-- The left outer sum has its original local formula on the full refinement. -/
theorem integralCurveTripleFull_outerLeft (i : (integralCurveTripleFullCover W hΔ).I₀) :
    (integralCurveTripleFullCover W hΔ).f i ≫ integralCurveTripleAddLeft W hΔ =
      integralCurveTripleFullOuter W hΔ i ≫ integralCurveTripleLeftDomain W hΔ i.1 ≫
        integralCurveAdditionLocal W hΔ i.1.1 := by
  rw [← integralCurveTripleFullOuter_inputs, Category.assoc, integralCurveTripleAddLeft_local]

/-- The right outer sum has its original local formula on the full refinement. -/
theorem integralCurveTripleFull_outerRight (i : (integralCurveTripleFullCover W hΔ).I₀) :
    (integralCurveTripleFullCover W hΔ).f i ≫ integralCurveTripleAddRight W hΔ =
      integralCurveTripleFullOuter W hΔ i ≫ integralCurveTripleRightDomain W hΔ i.1 ≫
        integralCurveAdditionLocal W hΔ i.1.2 := by
  rw [← integralCurveTripleFullOuter_inputs, Category.assoc, integralCurveTripleAddRight_local]

/-- The first inner sum has its original local formula on the full refinement. -/
theorem integralCurveTripleFull_innerLeft (i : (integralCurveTripleFullCover W hΔ).I₀) :
    (integralCurveTripleFullCover W hΔ).f i ≫ integralCurveTriplePair W ≫
        integralCurveAddition W hΔ =
      integralCurveTripleFullInner W hΔ i ≫ integralCurveTripleInnerLeftDomain W hΔ i.2 ≫
        integralCurveAdditionLocal W hΔ i.2.1 := by
  rw [← integralCurveTripleFullInner_inputs, Category.assoc, integralCurveTripleInnerLeft_local]

/-- The last inner sum has its original local formula on the full refinement. -/
theorem integralCurveTripleFull_innerRight (i : (integralCurveTripleFullCover W hΔ).I₀) :
    (integralCurveTripleFullCover W hΔ).f i ≫ integralCurveTripleLastPair W ≫
        integralCurveAddition W hΔ =
      integralCurveTripleFullInner W hΔ i ≫ integralCurveTripleInnerRightDomain W hΔ i.2 ≫
        integralCurveAdditionLocal W hΔ i.2.2 := by
  rw [← integralCurveTripleFullInner_inputs, Category.assoc, integralCurveTripleInnerRight_local]

end FLT.Mazur.WeierstrassIntegralChart
