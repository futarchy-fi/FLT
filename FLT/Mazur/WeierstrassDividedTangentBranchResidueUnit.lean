/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchResidue

/-!
# Terminal strict-branch outputs have invertible vertical derivative

The residue formulas imply smoothness at the terminal coefficient, including
in residue characteristic two. Invertibility follows from the actual branch
localizations and the next constant coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s b3 a2 b4' b6' u₁ u₂ v₁ v₂ : R)
  (hc : IsUnit (v₁ + W.a₁ * u₁ + b3))
  (hd : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
local notation "k" => tangentBranchSlope W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd
local notation "X" => tangentBranchX W s a2 u₁ u₂ k
local notation "Y" => tangentBranchY W s b3 a2 u₁ u₂ v₁ k

include hc hd in
/-- The actual branch denominators force both abscissas and the tangent coefficient to be units. -/
theorem tangentBranch_residue_input_units (h3 : b3 = 0) (h₁ : v₁ = 0) (h₂ : v₂ = 0) :
    IsUnit W.a₁ ∧ IsUnit u₁ ∧ IsUnit u₂ := by
  have hc' : IsUnit (W.a₁ * u₁) := by simpa only [h3, h₁, zero_add, add_zero] using hc
  have hd' : IsUnit (W.a₁ * u₂) := by
    simpa only [h3, h₁, h₂, zero_add, add_zero] using hd
  exact ⟨isUnit_of_mul_isUnit_left hc', isUnit_of_mul_isUnit_right hc',
    isUnit_of_mul_isUnit_right hd'⟩

/-- At the terminal constant coefficient the constructed output abscissa is invertible. -/
theorem tangentBranchX_residue_isUnit (hs : s = 0) (h3 : b3 = 0)
    (h₁ : v₁ = 0) (h₂ : v₂ = 0) (h6 : IsUnit b6') : IsUnit X := by
  have h := tangentBranchX_residue W s b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hs h3 h₁ h₂
  exact isUnit_of_mul_isUnit_right (h.symm ▸ h6.neg)

/-- The terminal exceptional output is vertically smooth over any residue ring. -/
theorem tangentBranch_residue_vertical_isUnit (hs : s = 0) (h3 : b3 = 0)
    (h₁ : v₁ = 0) (h₂ : v₂ = 0) (h6 : IsUnit b6') :
    IsUnit (2 * Y + W.a₁ * X + b3) := by
  have ha := (tangentBranch_residue_input_units W b3 u₁ u₂ v₁ v₂ hc hd h3 h₁ h₂).1
  have hx := tangentBranchX_residue_isUnit W s b3 a2 b4' b6' u₁ u₂ v₁ v₂
    hc hd hs h3 h₁ h₂ h6
  have hy := tangentBranchY_residue W s b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hs h3 h₁
  have he : 2 * Y + W.a₁ * X + b3 = -(W.a₁ * X) := by
    linear_combination 2 * hy + h3
  rw [he]
  exact (ha.mul hx).neg

end FLT.Mazur.WeierstrassDilatation
