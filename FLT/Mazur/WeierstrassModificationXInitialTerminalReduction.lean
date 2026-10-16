/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialTerminalNodeBoundary
public import FLT.Mazur.WeierstrassDilatationTerminalFactorReduction

/-!
# Reductions of the full terminal coordinates on initial Laurent boundaries

Both complete normalized factors retain the original positive Laurent
parameter and chosen slope, modulo the nilpotent arithmetic ideal.
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
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6) (opposite : Bool)
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
local notation "v" => laurentBranchSlope U (q s) (q b3) (q b4) (q b6) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) h4₀ h6₀ opposite
local notation "hv" => laurentBranchSlope_equation U (q s) (q b3) (q b4) (q b6) J hJ
  (ha.map q) (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) h4₀ h6₀ opposite
local notation "G" => tensorInitialTerminalLaurent W s b3 b4 b6 Q v hv
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  b3 b4 b6 ha hs h2 h4 h6
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W s
  b3 b4 b6 ha hs h2 h4 h6

local notation "E" => initialTerminalArithmeticNodeEvaluation
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite

local notation "K" => Ideal.map (algebraMap Q Q[T;T⁻¹]) J
local notation "z" => LaurentPolynomial.T 1 (R := Q)
local notation "a₁" => algebraMap Q Q[T;T⁻¹] (q W.a₁)
local notation "g" => AlgHom.comp G (WeierstrassDilatation.baseChangeBackward W s b3 b4 b6 Q)

/-- The original terminal ordinate retains the whole positive Laurent slope. -/
theorem initialTerminalArithmeticOrdinate_evaluation :
    g (WeierstrassDilatation.y U (q s) (q b3) (q b4) (q b6)) = z * v :=
  (congrArg G (WeierstrassDilatation.baseChangeBackward_y W s b3 b4 b6 Q)).trans
    (tensorInitialTerminalLaurent_y W s b3 b4 b6 Q v hv)

/-- The first normalized terminal factor reduces to T times the full initial slope. -/
theorem initialTerminalArithmeticNodeEvaluation_p_reduction :
    E (NodalFiber.p c) - z * v ∈ K := by
  have h := WeierstrassDilatation.terminalNodeSmall_sub_y_mem U (q s)
    (q b3) (q b4) (q b6) r J hJ hrI (ha.map q) h4₀ h6₀ g
  rw [initialTerminalArithmeticOrdinate_evaluation
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite] at h
  rw [initialTerminalArithmeticNodeEvaluation_p π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite]
  exact h

/-- The opposite normalized factor retains the full opposite tangent on the initial boundary. -/
theorem initialTerminalArithmeticNodeEvaluation_q_reduction :
    E (NodalFiber.q c) - z * (v + a₁) ∈ K := by
  have h := WeierstrassDilatation.terminalNodeOpposite_sub_tangent_mem U (q s)
    (q b3) (q b4) (q b6) r J hJ hrI (ha.map q) h4₀ h6₀ g
    (arithmeticCoefficient_mem π m h3)
  have hx : g (WeierstrassDilatation.x U (q s) (q b3) (q b4) (q b6)) = z :=
    (congrArg G (WeierstrassDilatation.baseChangeBackward_x W s b3 b4 b6 Q)).trans
      (tensorInitialTerminalLaurent_x W s b3 b4 b6 Q v hv)
  rw [initialTerminalArithmeticOrdinate_evaluation
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite, hx] at h
  rw [initialTerminalArithmeticNodeEvaluation_q π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite]
  rw [mul_add]
  exact h

end FLT.Mazur.WeierstrassModificationX
