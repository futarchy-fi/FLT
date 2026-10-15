/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalNodeBoundary
public import FLT.Mazur.WeierstrassDilatationTerminalFactorReduction
public import FLT.Mazur.WeierstrassSuccessiveArithmeticLaurentReduction

/-!
# Reductions of both normalized terminal boundary coordinates

The original reciprocal parameter and full Boolean slope are retained
in the two congruences modulo the arithmetic coefficient ideal.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q

variable (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "a" => depthOverlapEquiv W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d)

variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6) (opposite : Bool)
local notation "s" => π ^ (start + j + 1)
local notation "U" => W.map q
local notation "J" => ideal Q (parameter R π m)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "r" => WeierstrassDilatation.terminalTangentRoot U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "hrI" => WeierstrassDilatation.terminalTangentRoot_mem U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "hr" => WeierstrassDilatation.terminalTangentRoot_equation U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "h4₀" => arithmeticCoefficient_mem π m h4
local notation "h6₀" => arithmeticCoefficient_mem π m h6
local notation "v" => arithmeticBranchSlope π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "hv" => arithmeticBranchSlope_equation π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "G" => tensorTerminalLaurent W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q v hv
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6

local notation "E" => terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6 opposite
local notation "F" => AlgHom.comp (PolygonSmoothing.leftLaurentMap (q π))
  (SuccessiveIncidence.toPolygon (q π))
local notation "K" => Ideal.map (algebraMap Q Q[T;T⁻¹]) J
local notation "z" => LaurentPolynomial.T (-1) (R := Q)
local notation "a₁" => algebraMap Q Q[T;T⁻¹] (q W.a₁)
local notation "g" => AlgHom.comp G (WeierstrassDilatation.baseChangeBackward W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q)

/-- The original ordinate evaluation keeps the full reciprocal slope before normalization. -/
theorem terminalArithmeticOrdinate_evaluation :
    g (WeierstrassDilatation.y U (q s) (q (Data.b3 d)) (q (Data.b4 d)) (q (Data.b6 d))) =
      z * F v :=
  (congrArg G (WeierstrassDilatation.baseChangeBackward_y W s
    (Data.b3 d) (Data.b4 d) (Data.b6 d) Q)).trans
      (tensorTerminalLaurent_y W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) Q v hv)

/-- The first normalized coordinate reduces to the reciprocal parameter times the full slope. -/
theorem terminalArithmeticNodeEvaluation_p_reduction :
    E (NodalFiber.p c) - z * F v ∈ K := by
  have h := WeierstrassDilatation.terminalNodeSmall_sub_y_mem U (q s)
    (q (Data.b3 d)) (q (Data.b4 d)) (q (Data.b6 d)) r J hJ hrI (ha.map q) h4₀ h6₀ g
  rw [terminalArithmeticOrdinate_evaluation data m j hj ha hs h2 h3 h4 h6 opposite] at h
  rw [terminalArithmeticNodeEvaluation_p data m j hj ha hs h2 h3 h4 h6 opposite]
  exact h

/-- The second normalized coordinate retains the full opposite tangent and reciprocal parameter. -/
theorem terminalArithmeticNodeEvaluation_q_reduction :
    E (NodalFiber.q c) - z * (F v + a₁) ∈ K := by
  have h := WeierstrassDilatation.terminalNodeOpposite_sub_tangent_mem U (q s)
    (q (Data.b3 d)) (q (Data.b4 d)) (q (Data.b6 d)) r J hJ hrI (ha.map q) h4₀ h6₀ g
    (arithmeticCoefficient_mem π m h3)
  have hx :
      g (WeierstrassDilatation.x U (q s) (q (Data.b3 d)) (q (Data.b4 d)) (q (Data.b6 d))) =
        z :=
    (congrArg G (WeierstrassDilatation.baseChangeBackward_x W s
      (Data.b3 d) (Data.b4 d) (Data.b6 d) Q)).trans
        (tensorTerminalLaurent_x W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) Q v hv)
  rw [terminalArithmeticOrdinate_evaluation data m j hj ha hs h2 h3 h4 h6 opposite, hx] at h
  rw [terminalArithmeticNodeEvaluation_q data m j hj ha hs h2 h3 h4 h6 opposite]
  rw [mul_add]
  exact h

end FLT.Mazur.WeierstrassDividedDepth
