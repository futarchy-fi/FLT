/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCuspTangent
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Rational tangent directions of a normalized node

At a singularity translated to the origin, the existing node polynomial is
c₄ times the tangent quadratic. Its splitting gives a rational tangent shear;
nonzero c₄ ensures the two tangent directions are distinct in every characteristic.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve Polynomial

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The node polynomial at a normalized singularity is the scaled tangent quadratic. -/
theorem normalized_nodePoly (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    W.nodePoly = C W.c₄ * (X ^ 2 + C W.a₁ * X - C W.a₂) := by
  simp only [nodePoly, b₄, b₆, h3, h4, h6, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_add, add_zero, sub_zero, C_mul]
  ring

/-- Splitting of the node polynomial yields a tangent slope with nonzero transverse derivative. -/
theorem exists_node_shear (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
    (hc : W.c₄ ≠ 0) (hsplit : W.nodePoly.Splits) :
    ∃ s : F, W.a₂ - s * W.a₁ - s ^ 2 = 0 ∧ W.a₁ + 2 * s ≠ 0 := by
  have hp : W.nodePoly = C W.c₄ * X ^ 2 + C (W.a₁ * W.c₄) * X + C (-W.a₂ * W.c₄) := by
    rw [normalized_nodePoly W h3 h4 h6]
    simp only [map_mul, map_neg]
    ring
  rw [hp, splits_quadratic_iff_exists_root hc] at hsplit
  obtain ⟨s, hs⟩ := hsplit
  have hs0 : W.c₄ * (W.a₂ - s * W.a₁ - s ^ 2) = 0 := by
    linear_combination -hs
  have hs2 := (mul_eq_zero.mp hs0).resolve_left hc
  have hb : W.b₂ = (W.a₁ + 2 * s) ^ 2 := by
    rw [b₂]
    linear_combination 4 * hs2
  refine ⟨s, hs2, fun hs1 => hc ?_⟩
  rw [normalized_c₄_eq_b₂_sq W h3 h4, hb, hs1]
  simp

/-- A normalized split node admits a shear with nonzero a₁ and all other coefficients zero. -/
theorem exists_normalized_node_shear
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
    (hc : W.c₄ ≠ 0) (hsplit : W.nodePoly.Splits) :
    ∃ s : F, let V := VariableChange.mk 1 0 s 0 • W
      V.a₁ ≠ 0 ∧ V.a₂ = 0 ∧ V.a₃ = 0 ∧ V.a₄ = 0 ∧ V.a₆ = 0 := by
  obtain ⟨s, hs2, hs1⟩ := exists_node_shear W h3 h4 h6 hc hsplit
  refine ⟨s, ?_⟩
  simpa [variableChange_def, h3, h4, h6] using And.intro hs1 hs2

end FLT.Mazur
