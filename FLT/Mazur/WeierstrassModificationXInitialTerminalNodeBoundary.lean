/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticNodeBoundary
public import FLT.Mazur.WeierstrassDilatationArithmeticTerminalNode
public import FLT.Mazur.WeierstrassDilatationTerminalTensorRestriction
public import FLT.Mazur.WeierstrassModificationXTensorTerminalCoordinates

/-!
# Both initial Laurent labels in the full terminal smoothing node

The original modification overlap transports both full initial Laurent roots
into the terminal node, preserving its computed smoothing and corrected factors.
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

/-- Either full original terminal Laurent boundary, in the constructed node coordinates. -/
def initialTerminalArithmeticNodeEvaluation : NodalFiber.Coordinate c →ₐ[Q] Q[T;T⁻¹] :=
  WeierstrassDilatation.tensorTerminalNodeRestriction W s b3 b4 b6
    Q r J hJ hrI (ha.map q) h4₀ h6₀ hr G
local notation "E" => initialTerminalArithmeticNodeEvaluation
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite

/-- Each original initial label commutes with the entire terminal tensor isomorphism. -/
@[reassoc] theorem initialTerminalArithmeticNodeEvaluation_boundary :
    Spec.map (CommRingCat.ofHom (E).toRingHom) ≫ (e).hom =
      Spec.map (CommRingCat.ofHom (G).toRingHom) := by
  rw [initialTerminalArithmeticNodeEvaluation, WeierstrassDilatation.arithmeticTerminalNodeIso,
    WeierstrassDilatation.tensorTerminalNodeRestriction_spec]

/-- The first normalized boundary coordinate is the explicit factor of the original cubic. -/
theorem initialTerminalArithmeticNodeEvaluation_p : E (NodalFiber.p c) =
    G (WeierstrassDilatation.baseChangeBackward W s b3 b4 b6 Q
      (WeierstrassDilatation.terminalNodeSmall U (q s) (q b3) (q b4)
        (q b6) r J hJ hrI (ha.map q) h4₀ h6₀)) :=
  WeierstrassDilatation.tensorTerminalNodeRestriction_p W s b3 b4 b6
    Q r J hJ hrI (ha.map q) h4₀ h6₀ hr G

/-- The opposite normalized boundary coordinate is the other explicit original cubic factor. -/
theorem initialTerminalArithmeticNodeEvaluation_q : E (NodalFiber.q c) =
    G (WeierstrassDilatation.baseChangeBackward W s b3 b4 b6 Q
      (WeierstrassDilatation.terminalNodeOpposite U (q s) (q b3) (q b4)
        (q b6) r J hJ hrI (ha.map q) h4₀ h6₀)) :=
  WeierstrassDilatation.tensorTerminalNodeRestriction_q W s b3 b4 b6
    Q r J hJ hrI (ha.map q) h4₀ h6₀ hr G

/-- The original quotient smoothing survives on both full Laurent boundaries. -/
theorem initialTerminalArithmeticNodeEvaluation_product :
    E (NodalFiber.p c) * E (NodalFiber.q c) = algebraMap Q Q[T;T⁻¹] c := by
  rw [← map_mul, NodalFiber.relation, AlgHom.commutes]

end FLT.Mazur.WeierstrassModificationX
