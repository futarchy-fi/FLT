/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchFormula

/-!
# The divided equation of a strict-branch tangent output

The branch inverses construct the divided slope and both output coordinates.
Regularity of the scale recovers the divided equation from the original
addition equation, with no original-output smoothness assumption.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s b3 b4 b6 a2 b4' b6' u₁ u₂ v₁ v₂ : R)
  (hc : IsUnit (v₁ + W.a₁ * u₁ + b3))
  (hd : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
local notation "k" => tangentBranchSlope W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd
local notation "X" => tangentBranchX W s a2 u₁ u₂ k
local notation "Y" => tangentBranchY W s b3 a2 u₁ u₂ v₁ k

/-- The explicit divided slope satisfies the original divided chord equation. -/
theorem tangentBranchSlope_chord
    (h2 : W.a₂ = s * a2) (h4 : b4 = s * b4') (h6 : b6 = s * b6')
    (he : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6) :
    (s * k) * (v₁ + v₂ + W.a₁ * u₂ + b3) =
      s * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + W.a₂ * (u₁ + u₂) + b4 - W.a₁ * v₁ := by
  have hinv : (↑hd.unit⁻¹ : R) * (v₁ + v₂ + W.a₁ * u₂ + b3) = 1 := hd.val_inv_mul
  have hv := tangentBranchOrdinate_mul W s b3 b4 b6 a2 b4' b6' u₁ v₁ hc h2 h4 h6 he
  unfold tangentBranchSlope
  rw [mul_assoc s, mul_assoc, hinv, mul_one, h2, h4]
  linear_combination -W.a₁ * hv

/-- The branch output lies in the divided equation, including over singular original outputs. -/
theorem tangentBranch_equation (hs : IsRegular s)
    (h2 : W.a₂ = s * a2) (h3 : W.a₃ = s * b3)
    (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
    (h4' : b4 = s * b4') (h6' : b6 = s * b6')
    (h₁ : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6)
    (h₂ : v₂ ^ 2 + (W.a₁ * u₂ + b3) * v₂ =
      s * u₂ ^ 3 + W.a₂ * u₂ ^ 2 + b4 * u₂ + b6) :
    Y ^ 2 + (W.a₁ * X + b3) * Y =
      s * X ^ 3 + W.a₂ * X ^ 2 + b4 * X + b6 := by
  have h := divided_tangent_add_equation W s b3 b4 b6 h3 h4 h6 h₁ h₂ hd
    (tangentBranchSlope_chord W s b3 b4 b6 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd h2 h4' h6' h₁)
  rw [← tangentBranchX_scale W s a2 u₁ u₂ h2,
    ← tangentBranchY_scale W s b3 a2 u₁ u₂ v₁ h2 h3] at h
  apply (hs.pow 2).left
  rw [Affine.equation_iff, h3, h4, h6] at h
  linear_combination h

end FLT.Mazur.WeierstrassDilatation
