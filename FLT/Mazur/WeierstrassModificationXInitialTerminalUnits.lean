/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialTerminalReduction
public import FLT.Mazur.WeierstrassModificationXLaurentBranchReduction

/-!
# Initial labels select opposite full terminal punctures

The small initial label lands in D(q), and the opposite initial label in D(p).
Their other coordinates are nilpotent on the complete original Laurent boundary.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "U" => W.map q
local notation "J" => ideal Q (parameter R π m)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m
local notation "r" => WeierstrassDilatation.terminalTangentRoot U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
local notation "hrI" => WeierstrassDilatation.terminalTangentRoot_mem U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
local notation "hr" => WeierstrassDilatation.terminalTangentRoot_equation U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
local notation "h4₀" => arithmeticCoefficient_mem π m h4
local notation "h6₀" => arithmeticCoefficient_mem π m h6
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  b3 b4 b6 ha hs h2 h4 h6
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W s
  b3 b4 b6 ha hs h2 h4 h6

local notation "E" => initialTerminalArithmeticNodeEvaluation
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6

local notation "K" => Ideal.map (algebraMap Q Q[T;T⁻¹]) J
local notation "z" => LaurentPolynomial.T 1 (R := Q)
local notation "a₁" => algebraMap Q Q[T;T⁻¹] (q W.a₁)

/-- The small initial branch has nilpotent first terminal coordinate. -/
theorem initialTerminalArithmeticSmall_p_mem : E false (NodalFiber.p c) ∈ K := by
  have h := initialTerminalArithmeticNodeEvaluation_p_reduction
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6 false
  have hv := laurentBranchSlope_small_mem U (q s) (q b3) (q b4) (q b6) J hJ (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) h4₀ h6₀
  simpa only [sub_add_cancel] using (K).add_mem h ((K).mul_mem_left z hv)

/-- The opposite initial branch has nilpotent opposite terminal coordinate. -/
theorem initialTerminalArithmeticOpposite_q_mem : E true (NodalFiber.q c) ∈ K := by
  have h := initialTerminalArithmeticNodeEvaluation_q_reduction
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6 true
  have hv := laurentBranchSlope_opposite_add_mem U (q s) (q b3) (q b4) (q b6) J hJ (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) h4₀ h6₀
  simpa only [WeierstrassCurve.map_a₁, sub_add_cancel] using (K).add_mem h ((K).mul_mem_left z hv)

/-- The small initial label lands in the full standard terminal q puncture. -/
theorem initialTerminalArithmeticSmall_q_unit : IsUnit (E false (NodalFiber.q c)) := by
  apply NilpotentQuadraticDifference.isUnit_of_sub_mem J hJ (algebraMap Q Q[T;T⁻¹])
    ((LaurentPolynomial.isUnit_T 1).mul ?_)
    (initialTerminalArithmeticNodeEvaluation_q_reduction
      π m W s b3 b4 b6 ha hs h2 h3 h4 h6 false)
  exact laurentBranchSlope_small_add_unit U (q s) (q b3) (q b4) (q b6) J hJ (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) h4₀ h6₀

/-- The opposite initial label lands in the full standard terminal p puncture. -/
theorem initialTerminalArithmeticOpposite_p_unit : IsUnit (E true (NodalFiber.p c)) := by
  apply NilpotentQuadraticDifference.isUnit_of_sub_mem J hJ (algebraMap Q Q[T;T⁻¹])
    ((LaurentPolynomial.isUnit_T 1).mul ?_)
    (initialTerminalArithmeticNodeEvaluation_p_reduction
      π m W s b3 b4 b6 ha hs h2 h3 h4 h6 true)
  exact laurentBranchSlope_opposite_unit U (q s) (q b3) (q b4) (q b6) J hJ (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) h4₀ h6₀

/-- Both original labels have their selected terminal coordinate invertible. -/
theorem initialTerminalArithmeticSelected_unit (opposite : Bool) :
    IsUnit (E opposite (if opposite then NodalFiber.p c else NodalFiber.q c)) := by
  cases opposite
  · exact initialTerminalArithmeticSmall_q_unit π m W s b3 b4 b6 ha hs h2 h3 h4 h6
  · exact initialTerminalArithmeticOpposite_p_unit π m W s b3 b4 b6 ha hs h2 h3 h4 h6

/-- The unselected terminal coordinate remains nilpotent for each full initial branch. -/
theorem initialTerminalArithmeticUnselected_nilpotent (opposite : Bool) :
    IsNilpotent (E opposite (if opposite then NodalFiber.q c else NodalFiber.p c)) := by
  apply NilpotentQuadraticRoot.element_nilpotent K
    (NilpotentPolynomialInverse.mapIdeal_nilpotent J hJ (algebraMap Q Q[T;T⁻¹]))
  cases opposite
  · exact initialTerminalArithmeticSmall_p_mem π m W s b3 b4 b6 ha hs h2 h3 h4 h6
  · exact initialTerminalArithmeticOpposite_q_mem π m W s b3 b4 b6 ha hs h2 h3 h4 h6

end FLT.Mazur.WeierstrassModificationX
