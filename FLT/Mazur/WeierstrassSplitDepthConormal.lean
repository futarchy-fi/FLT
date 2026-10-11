/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryConormalIdeal
public import FLT.Mazur.WeierstrassAdditionCenterContainment
public import FLT.Mazur.WeierstrassDividedDepthData
public import FLT.Mazur.WeierstrassDilatationResidueDepth

/-!
# Conormal characters at the original split-depth center

The coefficient depth and the actual divided datum imply all error memberships.
The center still has three generators, including the original uniformizer power.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open IsLocalRing WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] {W : WeierstrassCurve R} {π : R} {depth k : ℕ}
  (D : SplitNodeDepth W π depth) (d : Data W π k) (hk : 2 * k ≤ depth)
  (b : Bool) (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
local notation "I" => Ideal.map
  (AlgHom.toRingHom (AlgHom.comp f (ordinaryInputRight W b)))
  (modificationChartCenter W (π ^ k) 2)
local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "a" => algebraMap R S W.a₁
local notation "x" => f (ordinaryInputRight W b (coord W 2 0))
local notation "y" => f (ordinaryInputRight W b (coord W 2 1))
local notation "X" => f (ordinaryChartAddition W b (coord W 2 0))
local notation "Y" => f (ordinaryChartAddition W b (coord W 2 1))
local notation "l" => f (ordinaryChartSlope W b)

omit [IsDomain R] [IsLocalRing R] in
/-- The original scale remains a generator of the integral center. -/
theorem splitDepthConormal_scale_mem : algebraMap R S (π ^ k) ∈ I := by
  rw [modificationChartCenter_map]
  exact Ideal.subset_span (by simp)

include D d hk in
/-- Both divided linear coefficients supply a base factor after division by the scale. -/
theorem splitDepthConormal_linear_mem :
    algebraMap R S W.a₃ ∈ J * I ∧ algebraMap R S W.a₄ ∈ J * I := by
  obtain ⟨h3, h4⟩ := WeierstrassDilatation.divided_linear_mem D k hk
    d.b3 d.b4 d.factor3 d.factor4
  have hs := splitDepthConormal_scale_mem b f (π := π) (k := k)
  constructor
  · rw [d.factor3, map_mul, mul_comm (algebraMap R S (π ^ k))]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R S) h3) hs
  · rw [d.factor4, map_mul, mul_comm (algebraMap R S (π ^ k))]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R S) h4) hs

omit [IsDomain R] [IsLocalRing R] in
include d in
/-- The divided constant term contributes a quadratic center term, even at middle depth. -/
theorem splitDepthConormal_constant_mem : algebraMap R S W.a₆ ∈ I ^ 2 := by
  have hs := splitDepthConormal_scale_mem b f (π := π) (k := k)
  rw [d.factor6, map_mul, map_pow]
  apply Ideal.mul_mem_right
  simpa only [pow_two] using Ideal.mul_mem_mul hs hs

include D d hk in
/-- The two genuine integral addition characters in the residue conormal module. -/
theorem splitDepthConormal_characters :
    l * Y - (l + a) * y ∈ I ^ 2 + J * I ∧
      (l + a) * (Y + a * X) - l * (y + a * x) ∈ I ^ 2 + J * I := by
  obtain ⟨h3, h4⟩ := splitDepthConormal_linear_mem D d hk b f
  have h2 : algebraMap R S W.a₂ ∈ J := Ideal.mem_map_of_mem _ D.a₂_mem
  have hx : x ∈ I := by
    rw [modificationChartCenter_map]
    exact Ideal.subset_span (by simp)
  have hy : y ∈ I := by
    rw [modificationChartCenter_map]
    exact Ideal.subset_span (by simp)
  exact ⟨ordinarySpecialization_first_conormal W b f I J h2
    (Ideal.mul_le_right h3) h4 hx hy,
    ordinarySpecialization_second_conormal W b f I J h2 h3 h4 hx hy⟩

end FLT.Mazur.WeierstrassIntegralChart
