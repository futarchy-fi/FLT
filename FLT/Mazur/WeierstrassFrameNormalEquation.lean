/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassFrameNormalization
public import FLT.Mazur.WeierstrassVariableChangeIntegralEquation

/-!
# The explicit three-coefficient equation of a normalized frame

The normalized points (0,0), (0,-d), and (-d,0), with d a unit,
force a6 = 0, a3 = d, and a4 = a2*d - d^2. Applying the constructed
change of variables puts every unit-separated original frame in this form.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassFrameNormalEquation

variable {R : Type*} [CommRing R]

/-- The normalized unit-separated frame determines two of the original five coefficients. -/
theorem coefficients (W : WeierstrassCurve R) (d : Rˣ)
    (hp : W.toAffine.Equation 0 0) (hn : W.toAffine.Equation 0 (-(d : R)))
    (hq : W.toAffine.Equation (-(d : R)) 0) :
    W.a₆ = 0 ∧ W.a₃ = d ∧ W.a₄ = W.a₂ * d - (d : R) ^ 2 := by
  have h6 : W.a₆ = 0 := Affine.equation_zero.mp hp
  rw [Affine.equation_iff'] at hn hq
  have h3 : W.a₃ = d := by
    apply sub_eq_zero.mp
    apply d.isUnit.mul_right_eq_zero.mp
    linear_combination -hn - h6
  refine ⟨h6, h3, ?_⟩
  apply sub_eq_zero.mp
  apply d.isUnit.mul_right_eq_zero.mp
  linear_combination hq + h6

/-- The actual cubic with only the three remaining normalized parameters. -/
def equation (a b : R) (d : Rˣ) : WeierstrassCurve R :=
  ⟨a, b, d, b * d - (d : R) ^ 2, 0⟩

/-- Equality with the three-parameter equation follows from the actual frame equations. -/
theorem eq_equation (W : WeierstrassCurve R) (d : Rˣ)
    (hp : W.toAffine.Equation 0 0) (hn : W.toAffine.Equation 0 (-(d : R)))
    (hq : W.toAffine.Equation (-(d : R)) 0) : W = equation W.a₁ W.a₂ d := by
  obtain ⟨h6, h3, h4⟩ := coefficients W d hp hn hq
  exact WeierstrassCurve.ext rfl rfl h3 h4 h6

open WeierstrassFrameNormalization

/-- Normalizing an actual three-point frame constructs the explicit three-parameter cubic. -/
theorem normalized_eq (W : WeierstrassCurve R) (x y y' z w : R) (h v : Rˣ)
    (hh : (h : R) = x - z) (hv : (v : R) = y - y')
    (hp : W.toAffine.Equation x y) (hn : W.toAffine.Equation x y')
    (hq : W.toAffine.Equation z w) :
    change x y w h v • W =
      equation (change x y w h v • W).a₁ (change x y w h v • W).a₂ (separation h v) := by
  apply eq_equation
  · apply (WeierstrassVariableChangeIntegralEquation.equation_iff W _ 0 0).mp
    simpa only [(change_first x y w h v).1, (change_first x y w h v).2] using hp
  · apply (WeierstrassVariableChangeIntegralEquation.equation_iff W _ 0 _).mp
    simpa only [(change_first x y w h v).1, change_inverse x y y' w h v hv] using hn
  · apply (WeierstrassVariableChangeIntegralEquation.equation_iff W _ _ 0).mp
    simpa only [(change_third x y z w h v hh).1, (change_third x y z w h v hh).2] using hq

end FLT.Mazur.WeierstrassFrameNormalEquation
