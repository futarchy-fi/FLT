/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralTripleProduct

/-!
# Genuine addition-domain covers for the two triple sums

Pull back the existing addition cover along each constructed intermediate
pair. Refining these two covers gives actual scheme domains on which both
iterated sums have their original local formulas. Local associativity on
these domains remains a separate proof obligation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The eight actual input charts cover the triple fiber product. -/
def integralCurveTripleInputCover : (integralCurveTriple W).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (integralCurveProductCover W)
    (integralCurveTwoChartCover W) (integralCurveProductStructure W) (integralCurveStructure W)

/-- Pull back local addition domains along the left-associated intermediate pair. -/
def integralCurveTripleLeftCover : (integralCurveTriple W).OpenCover :=
  (integralCurveAdditionCover W hΔ).pullback₁ (integralCurveAddFirstPair W hΔ)

/-- Pull back the right-associated domains to a member of the left-associated cover. -/
def integralCurveTripleRightRefinement (i : (integralCurveTripleLeftCover W hΔ).I₀) :
    ((integralCurveTripleLeftCover W hΔ).X i).OpenCover :=
  (integralCurveAdditionCover W hΔ).pullback₁
    ((integralCurveTripleLeftCover W hΔ).f i ≫ integralCurveAddLastPair W hΔ)

/-- A genuine common cover for the local formulas of both triple sums. -/
def integralCurveTripleAdditionCover : (integralCurveTriple W).OpenCover :=
  (integralCurveTripleLeftCover W hΔ).bind (integralCurveTripleRightRefinement W hΔ)

/-- Projection from a common member to its original left addition domain. -/
def integralCurveTripleLeftDomain (i : (integralCurveTripleAdditionCover W hΔ).I₀) :
    (integralCurveTripleAdditionCover W hΔ).X i ⟶ (integralCurveAdditionCover W hΔ).X i.1 :=
  (integralCurveTripleRightRefinement W hΔ i.1).f i.2 ≫
    Scheme.Cover.pullbackHom (integralCurveAdditionCover W hΔ)
      (integralCurveAddFirstPair W hΔ) i.1

/-- Projection from the same member to its original right addition domain. -/
def integralCurveTripleRightDomain (i : (integralCurveTripleAdditionCover W hΔ).I₀) :
    (integralCurveTripleAdditionCover W hΔ).X i ⟶ (integralCurveAdditionCover W hΔ).X i.2 :=
  Scheme.Cover.pullbackHom (integralCurveAdditionCover W hΔ)
    ((integralCurveTripleLeftCover W hΔ).f i.1 ≫ integralCurveAddLastPair W hΔ) i.2

/-- The left domain projection has the actual first-sum and third-input pair. -/
theorem integralCurveTripleLeftDomain_inputs
    (i : (integralCurveTripleAdditionCover W hΔ).I₀) :
    integralCurveTripleLeftDomain W hΔ i ≫ (integralCurveAdditionCover W hΔ).f i.1 =
      (integralCurveTripleAdditionCover W hΔ).f i ≫ integralCurveAddFirstPair W hΔ := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (integralCurveTripleRightRefinement W hΔ i.1).f i.2 ≫ f)
      (Scheme.Cover.pullbackHom_map (integralCurveAdditionCover W hΔ)
        (integralCurveAddFirstPair W hΔ) i.1)).trans (Category.assoc _ _ _).symm)

/-- The right domain projection has the actual first-input and last-sum pair. -/
theorem integralCurveTripleRightDomain_inputs
    (i : (integralCurveTripleAdditionCover W hΔ).I₀) :
    integralCurveTripleRightDomain W hΔ i ≫ (integralCurveAdditionCover W hΔ).f i.2 =
      (integralCurveTripleAdditionCover W hΔ).f i ≫ integralCurveAddLastPair W hΔ := by
  exact (Scheme.Cover.pullbackHom_map (integralCurveAdditionCover W hΔ)
    ((integralCurveTripleLeftCover W hΔ).f i.1 ≫ integralCurveAddLastPair W hΔ) i.2).trans
      (Category.assoc _ _ _).symm

/-- The left-associated triple sum restricts to its original local addition formula. -/
theorem integralCurveTripleAddLeft_local
    (i : (integralCurveTripleAdditionCover W hΔ).I₀) :
    (integralCurveTripleAdditionCover W hΔ).f i ≫ integralCurveTripleAddLeft W hΔ =
      integralCurveTripleLeftDomain W hΔ i ≫ integralCurveAdditionLocal W hΔ i.1 := by
  rw [integralCurveTripleAddLeft, ← Category.assoc, ← integralCurveTripleLeftDomain_inputs,
    Category.assoc, integralCurveAdditionLocal_glued]

/-- The right-associated triple sum restricts to its original local addition formula. -/
theorem integralCurveTripleAddRight_local
    (i : (integralCurveTripleAdditionCover W hΔ).I₀) :
    (integralCurveTripleAdditionCover W hΔ).f i ≫ integralCurveTripleAddRight W hΔ =
      integralCurveTripleRightDomain W hΔ i ≫ integralCurveAdditionLocal W hΔ i.2 := by
  rw [integralCurveTripleAddRight, ← Category.assoc, ← integralCurveTripleRightDomain_inputs,
    Category.assoc, integralCurveAdditionLocal_glued]

end FLT.Mazur.WeierstrassIntegralChart
