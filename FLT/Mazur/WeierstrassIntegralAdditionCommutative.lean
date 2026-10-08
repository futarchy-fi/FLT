/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalInfinitySwap

/-!
# Commutativity of the constructed integral Weierstrass addition

The three genuine opens of the Y-product and the three mixed input products
cover the actual scheme fiber product. Their established symmetry identities
descend to commutativity over every coefficient ring with unit discriminant.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Commutativity holds on the complete product of the two Y charts. -/
theorem integralCurveAddition_swap_yProduct :
    integralCurveProductChart W true true ≫ integralCurveSwap W ≫
        integralCurveAddition W hΔ =
      integralCurveProductChart W true true ≫ integralCurveAddition W hΔ := by
  apply (yProductOpenCover W).hom_ext
  intro i
  cases i
  · exact integralCurveAddition_swap_affineOverlap W hΔ true true
  · exact integralCurveAddition_swap_polynomial W hΔ true true
  · exact integralCurveAddition_swap_infinity W hΔ

/-- The constructed global addition is commutative on the actual scheme fiber product. -/
theorem integralCurveAddition_commutative :
    integralCurveSwap W ≫ integralCurveAddition W hΔ = integralCurveAddition W hΔ := by
  apply (integralCurveProductCover W).hom_ext
  rintro ⟨b, c⟩
  cases b <;> cases c
  · exact integralCurveAddition_swap_mixed W hΔ false false (.inl rfl)
  · exact integralCurveAddition_swap_mixed W hΔ false true (.inl rfl)
  · exact integralCurveAddition_swap_mixed W hΔ true false (.inr rfl)
  · exact integralCurveAddition_swap_yProduct W hΔ

end FLT.Mazur.WeierstrassIntegralChart
