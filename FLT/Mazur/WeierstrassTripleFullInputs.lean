/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleFullAdditionCover

/-!
# Inputs of the outer sums on the simultaneous addition cover

The outer domains really take the local inner output and the remaining original
input. These identities connect the four local laws on the common cover.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The outer left domain represents the actual intermediate pair. -/
@[reassoc] theorem integralCurveTripleFull_leftPair
    (i : (integralCurveTripleFullCover W hΔ).I₀) :
    integralCurveTripleFullOuter W hΔ i ≫ integralCurveTripleLeftDomain W hΔ i.1 ≫
        (integralCurveAdditionCover W hΔ).f i.1.1 =
      (integralCurveTripleFullCover W hΔ).f i ≫ integralCurveAddFirstPair W hΔ := by
  rw [integralCurveTripleLeftDomain_inputs, ← Category.assoc,
    integralCurveTripleFullOuter_inputs]

/-- The outer right domain represents the other actual intermediate pair. -/
@[reassoc] theorem integralCurveTripleFull_rightPair
    (i : (integralCurveTripleFullCover W hΔ).I₀) :
    integralCurveTripleFullOuter W hΔ i ≫ integralCurveTripleRightDomain W hΔ i.1 ≫
        (integralCurveAdditionCover W hΔ).f i.1.2 =
      (integralCurveTripleFullCover W hΔ).f i ≫ integralCurveAddLastPair W hΔ := by
  rw [integralCurveTripleRightDomain_inputs, ← Category.assoc,
    integralCurveTripleFullOuter_inputs]

/-- The first input of the left outer law is precisely the local first inner sum. -/
theorem integralCurveTripleFull_leftFirst
    (i : (integralCurveTripleFullCover W hΔ).I₀) :
    integralCurveTripleFullOuter W hΔ i ≫ integralCurveTripleLeftDomain W hΔ i.1 ≫
        (integralCurveAdditionCover W hΔ).f i.1.1 ≫ pullback.fst _ _ =
      integralCurveTripleFullInner W hΔ i ≫ integralCurveTripleInnerLeftDomain W hΔ i.2 ≫
        integralCurveAdditionLocal W hΔ i.2.1 := by
  rw [integralCurveTripleFull_leftPair_assoc, integralCurveAddFirstPair_fst,
    integralCurveTripleFull_innerLeft]

/-- The second input of the left outer law is the original third input. -/
theorem integralCurveTripleFull_leftSecond
    (i : (integralCurveTripleFullCover W hΔ).I₀) :
    integralCurveTripleFullOuter W hΔ i ≫ integralCurveTripleLeftDomain W hΔ i.1 ≫
        (integralCurveAdditionCover W hΔ).f i.1.1 ≫ pullback.snd _ _ =
      (integralCurveTripleFullCover W hΔ).f i ≫ integralCurveTripleThird W := by
  rw [integralCurveTripleFull_leftPair_assoc, integralCurveAddFirstPair_snd]

/-- The first input of the right outer law is the original first input. -/
theorem integralCurveTripleFull_rightFirst
    (i : (integralCurveTripleFullCover W hΔ).I₀) :
    integralCurveTripleFullOuter W hΔ i ≫ integralCurveTripleRightDomain W hΔ i.1 ≫
        (integralCurveAdditionCover W hΔ).f i.1.2 ≫ pullback.fst _ _ =
      (integralCurveTripleFullCover W hΔ).f i ≫ integralCurveTripleFirst W := by
  rw [integralCurveTripleFull_rightPair_assoc, integralCurveAddLastPair_fst]

/-- The second input of the right outer law is precisely the local last inner sum. -/
theorem integralCurveTripleFull_rightSecond
    (i : (integralCurveTripleFullCover W hΔ).I₀) :
    integralCurveTripleFullOuter W hΔ i ≫ integralCurveTripleRightDomain W hΔ i.1 ≫
        (integralCurveAdditionCover W hΔ).f i.1.2 ≫ pullback.snd _ _ =
      integralCurveTripleFullInner W hΔ i ≫ integralCurveTripleInnerRightDomain W hΔ i.2 ≫
        integralCurveAdditionLocal W hΔ i.2.2 := by
  rw [integralCurveTripleFull_rightPair_assoc, integralCurveAddLastPair_snd,
    integralCurveTripleFull_innerRight]

end FLT.Mazur.WeierstrassIntegralChart
