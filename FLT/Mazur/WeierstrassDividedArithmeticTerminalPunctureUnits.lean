/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalNodeReduction

/-!
# The original Boolean boundary labels select opposite terminal punctures

The small label has unit q and nilpotent p; the opposite label has unit p
and nilpotent q. All claims concern the full corrected node coordinates.
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
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
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
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6

local notation "E" => terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6
local notation "F" => AlgHom.comp (PolygonSmoothing.leftLaurentMap (q π))
  (SuccessiveIncidence.toPolygon (q π))
local notation "K" => Ideal.map (algebraMap Q Q[T;T⁻¹]) J
local notation "z" => LaurentPolynomial.T (-1) (R := Q)
local notation "a₁" => algebraMap Q Q[T;T⁻¹] (q W.a₁)
local notation "v" => arithmeticBranchSlope π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6

/-- The complete normalized small-branch p coordinate is in the arithmetic ideal. -/
theorem terminalArithmeticSmall_p_mem : E false (NodalFiber.p c) ∈ K := by
  have h := terminalArithmeticNodeEvaluation_p_reduction data m j hj ha hs h2 h3 h4 h6 false
  have hv := arithmeticLaurentSmallSlope_mem π m W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 F
  simpa only [sub_add_cancel] using (K).add_mem h ((K).mul_mem_left z hv)

/-- The complete normalized opposite-branch q coordinate is in the arithmetic ideal. -/
theorem terminalArithmeticOpposite_q_mem : E true (NodalFiber.q c) ∈ K := by
  have h := terminalArithmeticNodeEvaluation_q_reduction data m j hj ha hs h2 h3 h4 h6 true
  have hv := arithmeticLaurentOppositeSlope_add_mem π m W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 F
  simpa only [sub_add_cancel] using (K).add_mem h ((K).mul_mem_left z hv)

/-- The small boundary is contained in the entire standard q puncture. -/
theorem terminalArithmeticSmall_q_unit : IsUnit (E false (NodalFiber.q c)) := by
  apply NilpotentQuadraticDifference.isUnit_of_sub_mem J hJ (algebraMap Q Q[T;T⁻¹])
    ((LaurentPolynomial.isUnit_T (-1)).mul ?_)
    (terminalArithmeticNodeEvaluation_q_reduction data m j hj ha hs h2 h3 h4 h6 false)
  exact arithmeticLaurentSmallSlope_add_unit π m W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 F

/-- The opposite boundary is contained in the entire standard p puncture. -/
theorem terminalArithmeticOpposite_p_unit : IsUnit (E true (NodalFiber.p c)) := by
  apply NilpotentQuadraticDifference.isUnit_of_sub_mem J hJ (algebraMap Q Q[T;T⁻¹])
    ((LaurentPolynomial.isUnit_T (-1)).mul ?_)
    (terminalArithmeticNodeEvaluation_p_reduction data m j hj ha hs h2 h3 h4 h6 true)
  exact arithmeticLaurentOppositeSlope_unit π m W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 F

/-- Each original Boolean label has its selected standard node coordinate invertible. -/
theorem terminalArithmeticSelected_unit (opposite : Bool) :
    IsUnit (E opposite (if opposite then NodalFiber.p c else NodalFiber.q c)) := by
  cases opposite
  · exact terminalArithmeticSmall_q_unit data m j hj ha hs h2 h3 h4 h6
  · exact terminalArithmeticOpposite_p_unit data m j hj ha hs h2 h3 h4 h6

/-- The other node coordinate is nilpotent on the complete labeled boundary. -/
theorem terminalArithmeticUnselected_nilpotent (opposite : Bool) :
    IsNilpotent (E opposite (if opposite then NodalFiber.q c else NodalFiber.p c)) := by
  apply NilpotentQuadraticRoot.element_nilpotent K
    (NilpotentPolynomialInverse.mapIdeal_nilpotent J hJ (algebraMap Q Q[T;T⁻¹]))
  cases opposite
  · exact terminalArithmeticSmall_p_mem data m j hj ha hs h2 h3 h4 h6
  · exact terminalArithmeticOpposite_q_mem data m j hj ha hs h2 h3 h4 h6

end FLT.Mazur.WeierstrassDividedDepth
