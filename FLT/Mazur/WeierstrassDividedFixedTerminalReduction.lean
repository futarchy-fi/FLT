/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFixedTerminalBoundary

/-!
# Tangent reductions of the actual fixed terminal parameters

These are necessary reductions of the full edge parameters. They preserve
both Boolean labels and the complete inverse terminal smoothing unit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
  (u : Rˣ) (hprimitive : Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W ha (π ^ 1) π m
local notation "s" => π ^ (start + j + 1)
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "c" => arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "v" => arithmeticFixedTerminalUnit π W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h3 h4 h6 u hprimitive m
local notation "E" => terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6
local notation "F" => AlgHom.comp (PolygonSmoothing.leftLaurentMap (algebraMap R Q π))
  (SuccessiveIncidence.toPolygon (algebraMap R Q π))
local notation "J" => ideal Q (parameter R π m)
local notation "K" => Ideal.map (algebraMap Q Q[T;T⁻¹]) J
local notation "z" => LaurentPolynomial.T (-1) (R := Q)
local notation "a" => algebraMap Q Q[T;T⁻¹] (algebraMap R Q W.a₁)

/-- The full small-boundary second factor reduces to a1 times the reciprocal parameter. -/
theorem terminalArithmeticSmall_q_sub_tangent_mem : E false (NodalFiber.q c) - z * a ∈ K := by
  have h := terminalArithmeticNodeEvaluation_q_reduction data m j hj ha hs h2 h3 h4 h6 false
  have hv := WeierstrassSuccessiveX.arithmeticLaurentSmallSlope_mem π m W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 F
  convert (K).add_mem h ((K).mul_mem_left z hv) using 1
  ring

/-- The opposite-boundary first factor reduces to minus a1 times the reciprocal parameter. -/
theorem terminalArithmeticOpposite_p_add_tangent_mem : E true (NodalFiber.p c) + z * a ∈ K := by
  have h := terminalArithmeticNodeEvaluation_p_reduction data m j hj ha hs h2 h3 h4 h6 true
  have hv := WeierstrassSuccessiveX.arithmeticLaurentOppositeSlope_add_mem π m W
    (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 F
  convert (K).add_mem h ((K).mul_mem_left z hv) using 1
  ring

/-- The unchanged full second parameter has the original positive tangent reduction. -/
theorem fixedTerminalPolygonSecondBoundaryUnit_sub_tangent_mem :
    (fixedTerminalPolygonSecondBoundaryUnit data m j hj ha hs h2 h3 h4 h6 : Q[T;T⁻¹]) -
      z * a ∈ K := by
  simpa only [fixedTerminalPolygonSecondBoundaryUnit, IsUnit.unit_spec,
    Bool.false_eq_true, ↓reduceIte] using
    terminalArithmeticSmall_q_sub_tangent_mem data m j hj ha hs h2 h3 h4 h6

include hprimitive in
/-- The full first parameter retains the inverse smoothing unit even in its reduction. -/
theorem fixedTerminalPolygonFirstBoundaryUnit_add_tangent_mem :
    (fixedTerminalPolygonFirstBoundaryUnit data m j hj ha hs h2 h3 h4 h6 u hprimitive :
        Q[T;T⁻¹]) + algebraMap Q Q[T;T⁻¹] (↑(v)⁻¹ : Q) * (z * a) ∈ K := by
  rw [fixedTerminalPolygonFirstBoundaryUnit, NodalFiber.unitNormalizedFirstUnit_coe]
  convert (K).mul_mem_left (algebraMap Q Q[T;T⁻¹] (↑(v)⁻¹ : Q))
    (terminalArithmeticOpposite_p_add_tangent_mem data m j hj ha hs h2 h3 h4 h6) using 1
  ring

end FLT.Mazur.WeierstrassDividedDepth
