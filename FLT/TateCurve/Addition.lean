/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Collinearity

/-!
# Addition for the Tate point map

Periodicity and inversion prove the addition law whenever an argument or its
product lies in `q^ℤ`. The remaining cases require identities between coordinates.
-/

@[expose] public section

open ValuativeRel

namespace TateCurve

open WeierstrassCurve.Affine

section

variable {K : Type*} [Field K] [DecidableEq K]

/-- Collinearity with the negative of a third point identifies the sum when all
three abscissae are distinct. -/
private theorem point_add_of_collinear (W : WeierstrassCurve.Affine K) {x₁ y₁ x₂ y₂ x₃ y₃ : K}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (h₃ : W.Nonsingular x₃ y₃) (h12 : x₁ ≠ x₂) (h31 : x₃ ≠ x₁) (h32 : x₃ ≠ x₂)
    (hline : W.slope x₁ x₂ y₁ y₂ * (x₃ - x₁) + y₁ = W.negY x₃ y₃) :
    Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ := by
  have hzero : (W.addPolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)).eval x₃ = 0 := by
    have hn := (W.equation_neg x₃ y₃).mpr h₃.1
    rw [← hline] at hn
    simpa [Equation, addPolynomial, linePolynomial, polynomial, Polynomial.evalEval] using hn
  rw [W.addPolynomial_slope h₁.1 h₂.1 (fun h ↦ h12 h.1)] at hzero
  simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, neg_eq_zero] at hzero
  have hx : x₃ = W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr h31) (sub_ne_zero.mpr h32)))
  rw [Point.add_of_X_ne h12, Point.some.injEq]
  refine ⟨hx.symm, ?_⟩
  rw [addY, negAddY, ← hx, hline, negY_negY]

end

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DecidableEq K]

/-- The addition law holds when the first argument is a power of the parameter. -/
theorem uniformizationPoint_mul_of_left_mem (q : Kˣ)
    (hq : valuation K (q : K) < 1) (u v : Kˣ) (hu : u ∈ Subgroup.zpowers q) :
    uniformizationPoint q hq (u * v) =
      uniformizationPoint q hq u + uniformizationPoint q hq v := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [uniformizationPoint_zpow_mul]
  have hz : uniformizationPoint q hq (q ^ m) = 0 :=
    (uniformizationPoint_eq_zero q _ hq).mpr
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers q) m)
  rw [hz, zero_add]

/-- The addition law holds when the second argument is a power of the parameter. -/
theorem uniformizationPoint_mul_of_right_mem (q : Kˣ)
    (hq : valuation K (q : K) < 1) (u v : Kˣ) (hv : v ∈ Subgroup.zpowers q) :
    uniformizationPoint q hq (u * v) =
      uniformizationPoint q hq u + uniformizationPoint q hq v := by
  rw [mul_comm, uniformizationPoint_mul_of_left_mem q hq v u hv, add_comm]

/-- The addition law holds when the arguments are inverse modulo powers of the parameter. -/
theorem uniformizationPoint_mul_of_mul_mem (q : Kˣ)
    (hq : valuation K (q : K) < 1) (u v : Kˣ) (huv : u * v ∈ Subgroup.zpowers q) :
    uniformizationPoint q hq (u * v) =
      uniformizationPoint q hq u + uniformizationPoint q hq v := by
  have hz : uniformizationPoint q hq (u * v) = 0 :=
    (uniformizationPoint_eq_zero q _ hq).mpr huv
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp huv
  have hv : v = q ^ m * u⁻¹ := by rw [hm]; simp
  rw [hz, hv, uniformizationPoint_zpow_mul, uniformizationPoint_inv, add_neg_cancel]

/-- To prove the full addition law it suffices to treat three nonidentity quotient classes. -/
theorem uniformizationPoint_mul_of_nonexceptional (q : Kˣ)
    (hq : valuation K (q : K) < 1)
    (h : ∀ u v : Kˣ, u ∉ Subgroup.zpowers q → v ∉ Subgroup.zpowers q →
      u * v ∉ Subgroup.zpowers q → uniformizationPoint q hq (u * v) =
        uniformizationPoint q hq u + uniformizationPoint q hq v) (u v : Kˣ) :
    uniformizationPoint q hq (u * v) =
      uniformizationPoint q hq u + uniformizationPoint q hq v := by
  by_cases hu : u ∈ Subgroup.zpowers q
  · exact uniformizationPoint_mul_of_left_mem q hq u v hu
  by_cases hv : v ∈ Subgroup.zpowers q
  · exact uniformizationPoint_mul_of_right_mem q hq u v hv
  by_cases huv : u * v ∈ Subgroup.zpowers q
  · exact uniformizationPoint_mul_of_mul_mem q hq u v huv
  exact h u v hu hv huv

/-- For three distinct abscissae, the addition law follows from a single
cleared-denominator collinearity identity. This does not assert that identity. -/
theorem uniformizationPoint_mul_of_collinear (q : Kˣ)
    (hq : valuation K (q : K) < 1) (u v : Kˣ)
    (hu : u ∉ Subgroup.zpowers q) (hv : v ∉ Subgroup.zpowers q)
    (huv : u * v ∉ Subgroup.zpowers q)
    (h12 : tateX (u : K) (q : K) ≠ tateX (v : K) (q : K))
    (h31 : tateX ((u * v : Kˣ) : K) (q : K) ≠ tateX (u : K) (q : K))
    (h32 : tateX ((u * v : Kˣ) : K) (q : K) ≠ tateX (v : K) (q : K))
    (hcol :
      (tateX (u : K) (q : K) - tateX (v : K) (q : K)) *
        (tateY ((u * v : Kˣ) : K) (q : K) + tateX ((u * v : Kˣ) : K) (q : K) +
          tateY (u : K) (q : K)) +
      (tateY (u : K) (q : K) - tateY (v : K) (q : K)) *
        (tateX ((u * v : Kˣ) : K) (q : K) - tateX (u : K) (q : K)) = 0) :
    uniformizationPoint q hq (u * v) =
      uniformizationPoint q hq u + uniformizationPoint q hq v := by
  classical
  simp only [uniformizationPoint, dite_eq_right hu, dite_eq_right hv, dite_eq_right huv]
  apply Eq.symm
  apply point_add_of_collinear _ _ _ _ h12 h31 h32
  rw [slope_of_X_ne h12]
  simp only [negY, WeierstrassCurve.tateCurve, WeierstrassCurve.toAffine, one_mul, sub_zero]
  field_simp [sub_ne_zero.mpr h12]
  linear_combination hcol

/-- The addition law holds when the three Tate points have pairwise distinct abscissae. -/
theorem uniformizationPoint_mul_of_distinct_tateX (q : Kˣ)
    (hq : valuation K (q : K) < 1) (u v : Kˣ)
    (hu : u ∉ Subgroup.zpowers q) (hv : v ∉ Subgroup.zpowers q)
    (huv : u * v ∉ Subgroup.zpowers q)
    (h12 : tateX (u : K) (q : K) ≠ tateX (v : K) (q : K))
    (h31 : tateX ((u * v : Kˣ) : K) (q : K) ≠ tateX (u : K) (q : K))
    (h32 : tateX ((u * v : Kˣ) : K) (q : K) ≠ tateX (v : K) (q : K)) :
    uniformizationPoint q hq (u * v) =
      uniformizationPoint q hq u + uniformizationPoint q hq v := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  apply uniformizationPoint_mul_of_collinear q hq u v hu hv huv h12 h31 h32
  have h := tateCoordinates_collinear q hq u v (u * v)⁻¹ hu hv
    (fun h ↦ huv ((Subgroup.zpowers q).inv_mem_iff.mp h)) (mul_inv_cancel _)
  simp only [Units.val_inv_eq_inv_val, tateX_inv q.ne_zero (u * v).ne_zero,
    tateY_inv q.ne_zero (u * v).ne_zero (tendsto_pow_nhds_zero hq)] at h
  linear_combination h

end TateCurve
