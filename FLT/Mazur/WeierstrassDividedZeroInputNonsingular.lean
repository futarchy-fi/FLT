/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNormalizedSingularity
public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth
public import FLT.Mazur.WeierstrassDividedSecantNonsingularInputs

/-!
# Punctured zero-depth inputs are nonsingular on the original cubic

Unlike positive-depth divided inputs, scale-one inputs do not contract to
the original node. The original coefficient depths give nonsingularity
from the actual input abscissa in every residue characteristic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry WeierstrassCurve IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R F : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field F] [Algebra R F] {W : WeierstrassCurve R} {π : R} {m : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π 0)
  (a : Coordinate W (π ^ 0) d.b3 d.b4 d.b6 →ₐ[R] F)
local notation "orig" => fromOriginal W (π ^ 0) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6
local notation "A" => a.comp orig
local notation "x₀" => WeierstrassIntegralChart.coord W 2 0
local notation "y₀" => WeierstrassIntegralChart.coord W 2 1

include D

/-- Punctured scale-one inputs remain nonsingular after contraction to the original cubic. -/
theorem zeroDepthInput_nonsingular (hm : 0 < m) (hπ : algebraMap R F π = 0)
    (hx : a (x W (π ^ 0) d.b3 d.b4 d.b6) ≠ 0) :
    (W.map (algebraMap R F)).toAffine.Nonsingular (A x₀) (A y₀) := by
  have van (b : R) (hb : b ∈ maximalIdeal R) : algebraMap R F b = 0 := by
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
    obtain ⟨v, rfl⟩ := hb
    rw [map_mul, hπ, zero_mul]
  have hlin := divided_linear_deep_mem D d (by omega : 0 ≤ m + 1)
  have h3 := van d.b3 (Ideal.pow_le_self (by omega) hlin.1)
  have h4 := van d.b4 (Ideal.pow_le_self (by omega) hlin.2)
  have h6 := van d.b6 (Ideal.pow_le_self (by omega)
    (divided_constant_exact_depth D d (by omega : 2 * 0 ≤ m)).1)
  apply (normalized_nonsingular_iff (W.map (algebraMap R F))
    (by simp only [map_a₃, d.factor3, map_mul, h3, mul_zero])
    (by simp only [map_a₄, d.factor4, map_mul, h4, mul_zero])
    (by simp only [map_a₆, d.factor6, map_mul, h6, mul_zero])
    (WeierstrassIntegralChart.affine_equation_of_hom W A)).mpr
  intro h
  apply hx
  simpa only [AlgHom.comp_apply, fromOriginal_x, map_mul, AlgHom.commutes,
    pow_zero, map_one, one_mul] using h.1

end FLT.Mazur.WeierstrassDividedDepth
