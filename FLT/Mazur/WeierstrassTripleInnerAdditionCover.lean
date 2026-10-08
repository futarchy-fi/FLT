/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleAdditionCover

/-!
# Genuine local domains for both inner sums of a triple

Pull back the existing addition cover along the first-pair and last-pair
projections. Their common refinement expresses both inner sums by the original
local formulas, independently of the outer-addition cover.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Pull back local addition domains along the first input pair. -/
def integralCurveTripleInnerLeftCover : (integralCurveTriple W).OpenCover :=
  (integralCurveAdditionCover W hΔ).pullback₁ (integralCurveTriplePair W)

/-- Pull back the last-pair domains to a member of the first-pair cover. -/
def integralCurveTripleInnerRightRefinement (i : (integralCurveTripleInnerLeftCover W hΔ).I₀) :
    ((integralCurveTripleInnerLeftCover W hΔ).X i).OpenCover :=
  (integralCurveAdditionCover W hΔ).pullback₁
    ((integralCurveTripleInnerLeftCover W hΔ).f i ≫ integralCurveTripleLastPair W)

/-- A genuine common cover for the local formulas of both inner sums. -/
def integralCurveTripleInnerCover : (integralCurveTriple W).OpenCover :=
  (integralCurveTripleInnerLeftCover W hΔ).bind (integralCurveTripleInnerRightRefinement W hΔ)

/-- Projection from a common member to its original left addition domain. -/
def integralCurveTripleInnerLeftDomain (i : (integralCurveTripleInnerCover W hΔ).I₀) :
    (integralCurveTripleInnerCover W hΔ).X i ⟶ (integralCurveAdditionCover W hΔ).X i.1 :=
  (integralCurveTripleInnerRightRefinement W hΔ i.1).f i.2 ≫
    Scheme.Cover.pullbackHom (integralCurveAdditionCover W hΔ)
      (integralCurveTriplePair W) i.1

/-- Projection from the same member to its original right addition domain. -/
def integralCurveTripleInnerRightDomain (i : (integralCurveTripleInnerCover W hΔ).I₀) :
    (integralCurveTripleInnerCover W hΔ).X i ⟶ (integralCurveAdditionCover W hΔ).X i.2 :=
  Scheme.Cover.pullbackHom (integralCurveAdditionCover W hΔ)
    ((integralCurveTripleInnerLeftCover W hΔ).f i.1 ≫ integralCurveTripleLastPair W) i.2

/-- The left domain projection has the actual first and second input pair. -/
theorem integralCurveTripleInnerLeftDomain_inputs
    (i : (integralCurveTripleInnerCover W hΔ).I₀) :
    integralCurveTripleInnerLeftDomain W hΔ i ≫ (integralCurveAdditionCover W hΔ).f i.1 =
      (integralCurveTripleInnerCover W hΔ).f i ≫ integralCurveTriplePair W := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (integralCurveTripleInnerRightRefinement W hΔ i.1).f i.2 ≫ f)
      (Scheme.Cover.pullbackHom_map (integralCurveAdditionCover W hΔ)
        (integralCurveTriplePair W) i.1)).trans (Category.assoc _ _ _).symm)

/-- The right domain projection has the actual second and third input pair. -/
theorem integralCurveTripleInnerRightDomain_inputs
    (i : (integralCurveTripleInnerCover W hΔ).I₀) :
    integralCurveTripleInnerRightDomain W hΔ i ≫ (integralCurveAdditionCover W hΔ).f i.2 =
      (integralCurveTripleInnerCover W hΔ).f i ≫ integralCurveTripleLastPair W := by
  exact (Scheme.Cover.pullbackHom_map (integralCurveAdditionCover W hΔ)
    ((integralCurveTripleInnerLeftCover W hΔ).f i.1 ≫ integralCurveTripleLastPair W) i.2).trans
      (Category.assoc _ _ _).symm

/-- The first inner sum restricts to its original local addition formula. -/
theorem integralCurveTripleInnerLeft_local
    (i : (integralCurveTripleInnerCover W hΔ).I₀) :
    (integralCurveTripleInnerCover W hΔ).f i ≫ integralCurveTriplePair W ≫
        integralCurveAddition W hΔ =
      integralCurveTripleInnerLeftDomain W hΔ i ≫ integralCurveAdditionLocal W hΔ i.1 := by
  rw [← Category.assoc, ← integralCurveTripleInnerLeftDomain_inputs,
    Category.assoc, integralCurveAdditionLocal_glued]

/-- The last inner sum restricts to its original local addition formula. -/
theorem integralCurveTripleInnerRight_local
    (i : (integralCurveTripleInnerCover W hΔ).I₀) :
    (integralCurveTripleInnerCover W hΔ).f i ≫ integralCurveTripleLastPair W ≫
        integralCurveAddition W hΔ =
      integralCurveTripleInnerRightDomain W hΔ i ≫ integralCurveAdditionLocal W hΔ i.2 := by
  rw [← Category.assoc, ← integralCurveTripleInnerRightDomain_inputs,
    Category.assoc, integralCurveAdditionLocal_glued]

end FLT.Mazur.WeierstrassIntegralChart
