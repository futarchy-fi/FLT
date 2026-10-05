/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentFieldFixed

/-!
# Descent of a norm-one tangent parameter

The inverse fractional linear transformation of a nonidentity norm-one
parameter is fixed by conjugation, so it is a slope over the ground field.
This calculation does not divide by two or three.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve Polynomial

variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [Fact (Irreducible (nodeTangentPolynomial W))]

local notation "L" => AdjoinRoot (nodeTangentPolynomial W)

/-- The tangent quadratic has no ground-field zero in the nonsplit case. -/
theorem nonsplit_tangent_value_ne_zero (t : F) : t ^ 2 + W.a₁ * t - W.a₂ ≠ 0 := by
  have hd : (nodeTangentPolynomial W).natDegree ≠ 1 := by
    rw [natDegree_eq_of_degree_eq_some (nodeTangentPolynomial_degree W)]
    decide
  simpa [Polynomial.IsRoot, nodeTangentPolynomial] using
    (Fact.out : Irreducible (nodeTangentPolynomial W)).not_isRoot_of_natDegree_ne_one hd (x := t)

/-- A nonidentity norm-one parameter determines a ground-field slope. -/
theorem exists_nodeTangent_slope (hb : W.b₂ ≠ 0) {u : L}
    (hu : u ≠ 1) (hn : nodeTangentConjugation W u * u = 1) :
    ∃ t : F, algebraMap F L t =
      (AdjoinRoot.root (nodeTangentPolynomial W) +
        (algebraMap F L W.a₁ + AdjoinRoot.root (nodeTangentPolynomial W)) * u) / (1 - u) := by
  have h0 : u ≠ 0 := by intro h; simp [h] at hn
  have hd : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hi : nodeTangentConjugation W u = u⁻¹ := by
    calc
      nodeTangentConjugation W u = (nodeTangentConjugation W u * u) * u⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ h0, mul_one]
      _ = u⁻¹ := by rw [hn, one_mul]
  have hd' : 1 - u⁻¹ ≠ 0 := by
    intro h
    have he : u⁻¹ = 1 := (sub_eq_zero.mp h).symm
    exact hu (inv_eq_one.mp he)
  apply (nodeTangentField_fixed_iff W hb _).mp
  have hs : nodeTangentConjugation W (AdjoinRoot.root (nodeTangentPolynomial W)) =
      -algebraMap F L W.a₁ - AdjoinRoot.root (nodeTangentPolynomial W) :=
    nodeTangentConjugationHom_root W
  rw [map_div₀, map_add, map_mul, map_add, AlgEquiv.commutes, hs, hi,
    map_sub, map_one, hi]
  apply (div_eq_div_iff hd' hd).mpr
  field_simp
  ring

end FLT.Mazur
