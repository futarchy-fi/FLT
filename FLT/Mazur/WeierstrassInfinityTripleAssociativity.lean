/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityInputMinorRegular

/-!
# Associativity on the full infinity addition member

Regularity of the input XZ minor removes both remaining intermediate-coordinate
denominators. The two actual iterated scheme maps coincide, and the explicit
line residual E(6,2) and minor M(5,6) vanish in the original section ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The product of both actual intermediate Z coordinates is regular. -/
theorem infinityTripleIntermediateDenominator_regular :
    IsRegular (infinityTripleIntermediateDenominator W hΔ) :=
  infinityTripleIntermediateDenominator_regular_of_law W hΔ (infinityAdditionChart_z_regular W)

/-- The genuine left- and right-associated additions agree on the full infinity member. -/
theorem infinityTripleFull_assoc :
    infinityTripleFullMap W hΔ ≫ integralCurveTripleAddLeft W hΔ =
      infinityTripleFullMap W hΔ ≫ integralCurveTripleAddRight W hΔ :=
  infinityTripleFull_assoc_of_inputMinor_regular W hΔ (infinityInputXZMinor_regular W)

/-- The two original algebraic associativity obstructions vanish without localization. -/
theorem infinityTripleFull_residuals_zero :
    infinityTripleNegLineResidual W hΔ 6 2 = 0 ∧ infinityTripleNegMinor W hΔ 5 6 = 0 :=
  (infinityTripleFull_assoc_iff_line_residual W hΔ).mp (infinityTripleFull_assoc W hΔ)

/-- The remaining negated-line residual E(6,2) vanishes in the actual section ring. -/
theorem infinityTripleNegLineResidual_six_two : infinityTripleNegLineResidual W hΔ 6 2 = 0 :=
  (infinityTripleFull_residuals_zero W hΔ).1

/-- The remaining negated-coordinate minor M(5,6) vanishes in the actual section ring. -/
theorem infinityTripleNegMinor_five_six : infinityTripleNegMinor W hΔ 5 6 = 0 :=
  (infinityTripleFull_residuals_zero W hΔ).2

/-- The full infinity associativity identity remains valid after arbitrary source change. -/
theorem infinityTripleFull_assoc_comp {X : Scheme} (f : X ⟶ InfinityTripleFull W hΔ) :
    (f ≫ infinityTripleFullMap W hΔ) ≫ integralCurveTripleAddLeft W hΔ =
      (f ≫ infinityTripleFullMap W hΔ) ≫ integralCurveTripleAddRight W hΔ := by
  rw [Category.assoc, infinityTripleFull_assoc, Category.assoc]

end FLT.Mazur.WeierstrassIntegralChart
