/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalBranch
public import FLT.Mazur.WeierstrassDilatationArithmeticTerminalNode
public import FLT.Mazur.WeierstrassDilatationTerminalTensorRestriction
public import FLT.Mazur.WeierstrassSuccessiveTerminalLaurentCoordinates

/-!
# Both original terminal boundaries in the complete computed smoothing node

The original arithmetic quotient, depth transition and Boolean branch label
are retained. Both full boundary maps commute with the entire tensor equivalence.
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

/-- Either full original terminal Laurent boundary, in the constructed node coordinates. -/
def terminalArithmeticNodeEvaluation : NodalFiber.Coordinate c →ₐ[Q] Q[T;T⁻¹] :=
  WeierstrassDilatation.tensorTerminalNodeRestriction W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
    Q r J hJ hrI (ha.map q) h4₀ h6₀ hr G
local notation "E" => terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6 opposite

/-- Each label retains W331's whole original terminal boundary through the tensor isomorphism. -/
@[reassoc] theorem terminalArithmeticNodeEvaluation_boundary :
    Spec.map (CommRingCat.ofHom (E).toRingHom) ≫ (e).hom =
      terminalArithmeticBranchBoundary data m j hj ha hs h2 h3 h4 h6 opposite := by
  rw [terminalArithmeticNodeEvaluation, WeierstrassDilatation.arithmeticTerminalNodeIso,
    WeierstrassDilatation.tensorTerminalNodeRestriction_spec, tensorTerminalLaurent_spec]
  rfl

/-- The first normalized boundary coordinate is the explicit factor of the original cubic. -/
theorem terminalArithmeticNodeEvaluation_p : E (NodalFiber.p c) =
    G (WeierstrassDilatation.baseChangeBackward W s (Data.b3 d) (Data.b4 d) (Data.b6 d) Q
      (WeierstrassDilatation.terminalNodeSmall U (q s) (q (Data.b3 d)) (q (Data.b4 d))
        (q (Data.b6 d)) r J hJ hrI (ha.map q) h4₀ h6₀)) :=
  WeierstrassDilatation.tensorTerminalNodeRestriction_p W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
    Q r J hJ hrI (ha.map q) h4₀ h6₀ hr G

/-- The opposite normalized boundary coordinate is the other explicit original cubic factor. -/
theorem terminalArithmeticNodeEvaluation_q : E (NodalFiber.q c) =
    G (WeierstrassDilatation.baseChangeBackward W s (Data.b3 d) (Data.b4 d) (Data.b6 d) Q
      (WeierstrassDilatation.terminalNodeOpposite U (q s) (q (Data.b3 d)) (q (Data.b4 d))
        (q (Data.b6 d)) r J hJ hrI (ha.map q) h4₀ h6₀)) :=
  WeierstrassDilatation.tensorTerminalNodeRestriction_q W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
    Q r J hJ hrI (ha.map q) h4₀ h6₀ hr G

/-- The original quotient smoothing survives on both full Laurent boundaries. -/
theorem terminalArithmeticNodeEvaluation_product :
    E (NodalFiber.p c) * E (NodalFiber.q c) = algebraMap Q Q[T;T⁻¹] c := by
  rw [← map_mul, NodalFiber.relation, AlgHom.commutes]

end FLT.Mazur.WeierstrassDividedDepth
