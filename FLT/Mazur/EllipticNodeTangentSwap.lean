/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeUniformizerLabel
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The integral shear exchanging nodal tangent branches

The shear with s = -a₁ preserves the finite-depth coefficient conditions.
On coordinates its inverse sends (x,y) to (x,y+a₁x). This exchanges the two
strict branches and negates the signed depth label, including at the midpoint.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The integral shear exchanging the two residue tangent directions. -/
def nodeTangentSwap : VariableChange R := ⟨1, 0, -W.a₁, 0⟩

/-- The swapped model has negated a₁ and unchanged a₂,a₃,a₆. -/
theorem nodeTangentSwap_coefficients :
    (nodeTangentSwap W • W).a₁ = -W.a₁ ∧
    (nodeTangentSwap W • W).a₂ = W.a₂ ∧
    (nodeTangentSwap W • W).a₃ = W.a₃ ∧
    (nodeTangentSwap W • W).a₄ = W.a₄ + W.a₁ * W.a₃ ∧
    (nodeTangentSwap W • W).a₆ = W.a₆ := by
  simp only [nodeTangentSwap, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul,
    zero_mul, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0)]
  constructor
  · ring
  constructor
  · ring
  constructor
  · trivial
  constructor
  · ring
  · ring

/-- Swapping the tangents preserves the finite-depth split coefficient conditions. -/
theorem SplitNodeDepth.tangentSwap [IsLocalRing R] {π : R} {n : ℕ}
    (D : SplitNodeDepth W π n) : SplitNodeDepth (nodeTangentSwap W • W) π n := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := nodeTangentSwap_coefficients W
  refine ⟨D.depth_pos, D.uniformizer_ne_zero, D.maximalIdeal_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₁]
    exact D.a₁_unit.neg
  · simpa only [h₂] using D.a₂_mem
  · simpa only [h₃] using D.a₃_mem
  · rw [h₄]
    exact (maximalIdeal R ^ (n + 1)).add_mem D.a₄_mem
      ((maximalIdeal R ^ (n + 1)).mul_mem_left _ D.a₃_mem)
  · simpa only [h₆] using D.a₆_mem
  · simpa only [h₆] using D.a₆_not_mem

/-- The inverse shear sends an actual integral solution to a solution of the swapped model. -/
theorem nodeTangentSwap_equation {x y : R} (he : W.toAffine.Equation x y) :
    (nodeTangentSwap W • W).toAffine.Equation x (y + W.a₁ * x) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := nodeTangentSwap_coefficients W
  rw [Affine.equation_iff, h₁, h₂, h₃, h₄, h₆]
  have h := (Affine.equation_iff _ _).mp he
  linear_combination h

/-- The divided coordinate shear preserves primitive pairs. -/
theorem nodeTangentSwap_primitive [IsLocalRing R] {a b : R}
    (hp : IsUnit a ∨ IsUnit b) : IsUnit a ∨ IsUnit (b + W.a₁ * a) := by
  by_cases ha : IsUnit a
  · exact Or.inl ha
  · right
    apply (residue_ne_zero_iff_isUnit _).mp
    simpa [(residue_eq_zero_iff _).mpr ha] using
      (residue_ne_zero_iff_isUnit _).mpr (hp.resolve_left ha)

/-- Exchanging the tangent branches negates every bounded primitive signed depth. -/
theorem nodeTangentSwap_branchLabel [IsLocalRing R] [IsDomain R]
    {π : R} {n k : ℕ} (D : SplitNodeDepth W π n) (hk : k ≤ n / 2)
    (a b : R) (hp : IsUnit a ∨ IsUnit b)
    (he : W.toAffine.Equation (π ^ k * a) (π ^ k * b)) :
    nodeBranchLabel n k (b + W.a₁ * a) = -nodeBranchLabel n k b := by
  have h := nodeBranchLabel_neg W π D.uniformizer_ne_zero D.maximalIdeal_eq n k hk
    D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem a b 0 (Ideal.zero_mem _) hp he
  have heq : -b - W.a₁ * a - 0 = (-1 : R) * (b + W.a₁ * a) := by ring
  rw [heq, nodeBranchLabel_unit_mul n k _ (isUnit_one.neg)] at h
  exact h

end FLT.Mazur
