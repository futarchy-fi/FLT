/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineEquationRigidity

/-!
# Detecting the equation in an actual function ring

An injective evaluation of the original affine chart detects all five
Weierstrass coefficients. The target need not be reduced or a domain.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
variable {R A : Type*} [CommRing R] [CommRing A]
  (W V : WeierstrassCurve R) (φ : R →+* A) (q : Coordinate W 2 →+* A)

/-- A faithful evaluation in any ring detects the complete original Weierstrass equation. -/
theorem affineEquation_curve_eq_of_injective
    (hq : Function.Injective q) (hs : ∀ a, q (algebraMap R _ a) = φ a)
    (h : (V.map φ).toAffine.Equation (q (coord W 2 0)) (q (coord W 2 1))) : V = W := by
  apply affineEquation_curve_eq W V
  rw [Affine.equation_iff] at h ⊢
  apply hq
  simpa only [map_add, map_mul, map_pow, hs, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] using h

end FLT.Mazur.WeierstrassIntegralChart
