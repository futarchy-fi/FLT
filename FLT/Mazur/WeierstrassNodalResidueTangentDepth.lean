/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalDividedDepth
public import FLT.Mazur.WeierstrassResidueTangentEquationData

/-!
# Nonsplit depth conditions in the actual residue tangent algebra

The original coefficient bounds kill the divided linear terms. The c₄ unit
condition gives a unit tangent separation, without a rational tangent choice.
The constant is zero strictly before middle depth and a unit at middle depth;
the incidence scale is one at depth zero and zero at positive depth.
-/

@[expose] public noncomputable section
open IsLocalRing WeierstrassCurve
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {depth k : ℕ}
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
local notation "q" => algebraMap R Q
local notation "U" => rootShearCurve (W.map q) r

include hπ hm in
/-- The original depth bounds kill both divided linear coefficients over the actual Q. -/
theorem nodalDepth_tangent_linear_zero (d : Data W π k) (hk : 2 * k ≤ depth)
    (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
    (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1)) : q d.b3 = 0 ∧ q d.b4 = 0 := by
  obtain ⟨g3, g4⟩ := nodalDepth_linear_mem hπ hm d hk h3 h4
  exact ⟨residueTangentEquation_zero W d.b3 g3, residueTangentEquation_zero W d.b4 g4⟩

omit [IsDomain R] in
/-- A normalized nodal c₄ unit forces the original tangent discriminant to be a unit. -/
theorem nodalDepth_b₂_isUnit
    (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
    (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄) : IsUnit W.b₂ := by
  apply (residue_ne_zero_iff_isUnit _).mp
  intro hz
  have g3 : (V).a₃ = 0 := (residue_eq_zero_iff _).mpr
    (Ideal.pow_le_self (by omega) h3)
  have g4 : (V).a₄ = 0 := (residue_eq_zero_iff _).mpr
    (Ideal.pow_le_self (by omega) h4)
  have he := normalized_c₄_eq_b₂_sq V g3 g4
  rw [map_c₄, map_b₂, hz, zero_pow (by decide : 2 ≠ 0)] at he
  exact (residue_ne_zero_iff_isUnit _).mpr hc he

omit [IsDomain R] in
/-- The actual sheared tangent separation is a unit in the residue root algebra. -/
theorem nodalDepth_tangent_a₁_isUnit
    (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
    (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄) : IsUnit (U).a₁ := by
  have hb : IsUnit (V).b₂ := by
    rw [map_b₂]
    exact (nodalDepth_b₂_isUnit h3 h4 hc).map (residue R)
  have ha := nodeTangentRoot_derivative_isUnit V hb
  rw [(rootShearCurve_coefficients r).1]
  simpa only [map_a₁, IsScalarTower.algebraMap_apply R K Q,
    ResidueField.algebraMap_eq] using ha

include hπ hm in
/-- Before equality depth the complete conic has zero constant in Q. -/
theorem nodalDepth_tangent_constant_zero (d : Data W π k) (hk : 2 * k < depth)
    (h6 : W.a₆ ∈ maximalIdeal R ^ depth) : q d.b6 = 0 :=
  residueTangentEquation_zero W d.b6 (nodalDepth_constant_mem hπ hm d hk h6)

omit [IsDomain R] in
include hm in
/-- At equality depth the complete conic has unit constant in Q. -/
theorem nodalDepth_tangent_constant_isUnit (d : Data W π k) (hk : 2 * k = depth)
    (h6 : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) : IsUnit (q d.b6) :=
  (nodalDepth_constant_isUnit hm d hk h6).map q

omit [IsDomain R] in
include hm in
/-- Positive depth kills the original scale after extending coefficients to Q. -/
theorem nodalDepth_tangent_scale_zero (hk : 0 < k) : q (π ^ k) = 0 :=
  residueTangentEquation_scale W (nodalDepth_residue_uniformizer hm) k hk

omit [IsDomain R] in
/-- The same scale at depth zero is one, so the positive-depth normal form does not apply. -/
theorem nodalDepth_tangent_scale_zeroDepth : q (π ^ 0) = 1 := by
  rw [pow_zero, map_one]

end FLT.Mazur.WeierstrassDividedDepth
