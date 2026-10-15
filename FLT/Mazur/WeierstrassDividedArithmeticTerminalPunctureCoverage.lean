/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalNodeGeometry
public import FLT.Mazur.WeierstrassDilatationTerminalHorizontalLocus
public import FLT.Mazur.PrincipalOpenTensorRange

/-!
# Each complete standard terminal puncture lies in the original covered horizontal open

This transports the cubic prime-ideal calculation through the actual
arithmetic tensor equivalence, preserving the original depth and quotient.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial TensorProduct
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

include h3 in
/-- Every point of either standard puncture is in the original terminal horizontal open. -/
theorem terminalArithmeticPuncture_horizontal (z : Spec (.of (NodalFiber.Coordinate c)))
    (hz : (if opposite then NodalFiber.p c else NodalFiber.q c) ∉ z.asIdeal) :
    ∃ y, PrincipalOpenTensor.inclusion Q x y = (e).hom z := by
  apply (PrincipalOpenTensor.mem_inclusion_range Q x ((e).hom z)).mpr
  change WeierstrassDilatation.tensorTerminalNodeEquiv W s
    (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r J hJ hrI (ha.map q) h4₀ h6₀ hr
      ((1 : Q) ⊗ₜ[R] x) ∉ z.asIdeal
  rw [WeierstrassDilatation.tensorTerminalNodeEquiv_tmul, one_smul,
    WeierstrassDilatation.coefficientMap_x]
  exact WeierstrassDilatation.terminalNodePuncture_horizontal U (q s)
    (q (Data.b3 d)) (q (Data.b4 d)) (q (Data.b6 d)) r J hJ hrI (ha.map q)
    (arithmeticCoefficient_mem π m h3) h4₀ h6₀ hr z.asIdeal opposite hz

/-- Every standard puncture point is reached by one of the full original labeled boundaries. -/
theorem terminalArithmeticPuncture_covered (z : Spec (.of (NodalFiber.Coordinate c)))
    (hz : (if opposite then NodalFiber.p c else NodalFiber.q c) ∉ z.asIdeal) :
    ∃ (label : Bool), ∃ y, Spec.map (CommRingCat.ofHom
      (terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6 label).toRingHom) y = z :=
  (terminalArithmeticNodeEvaluation_image data m j hj ha hs h2 h3 h4 h6 z).mpr
    (terminalArithmeticPuncture_horizontal data m j hj ha h2 h3 h4 h6 opposite z hz)

end FLT.Mazur.WeierstrassDividedDepth
