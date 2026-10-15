/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalTensorNode
public import FLT.Mazur.WeierstrassDilatationSmoothingCongruence
public import FLT.Mazur.WeierstrassSuccessiveArithmeticTensorBranches

/-!
# The complete terminal node at each original arithmetic quotient and depth

The nilpotent ideal and tangent root are constructed from the original
uniformizer and coefficients. The smoothing retains its original constant term.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages WeierstrassSuccessiveX
universe u
variable {R : Type u} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "U" => W.map q
local notation "J" => ideal Q (parameter R π m)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m
local notation "hs₀" => arithmeticCoefficient_mem π m hs
local notation "h2₀" => arithmeticCoefficient_mem π m h2
local notation "h4₀" => arithmeticCoefficient_mem π m h4
local notation "h6₀" => arithmeticCoefficient_mem π m h6
local notation "r" => terminalTangentRoot U (q s) J hJ (ha.map q) hs₀ h2₀
local notation "hrI" => terminalTangentRoot_mem U (q s) J hJ (ha.map q) hs₀ h2₀
local notation "hr" => terminalTangentRoot_equation U (q s) J hJ (ha.map q) hs₀ h2₀
local notation "T₀" => WeierstrassDilatation.ScalarExtension W s b3 b4 b6 Q

/-- The actual terminal smoothing over the original order-m arithmetic quotient. -/
def arithmeticTerminalSmoothing : Q :=
  terminalSmoothing U (q b3) (q b4) (q b6) r J hJ hrI (ha.map q) h4₀ h6₀
local notation "c" => arithmeticTerminalSmoothing π m W s b3 b4 b6 ha hs h2 h4 h6

/-- The smoothing lies in the original uniformizer ideal at every quotient order. -/
theorem arithmeticTerminalSmoothing_mem : c ∈ J :=
  terminalSmoothing_mem U (q b3) (q b4) (q b6) r J hJ hrI (ha.map q) h4₀ h6₀

/-- The exact original b6 is retained modulo the square of the uniformizer ideal. -/
theorem arithmeticTerminalSmoothing_sub_mem_sq (h3 : π ∣ b3) : c - q b6 ∈ J ^ 2 :=
  terminalSmoothing_sub_mem_sq U (q b3) (q b4) (q b6) r J hJ hrI (ha.map q)
    (arithmeticCoefficient_mem π m h3) h4₀ h6₀

/-- The whole original arithmetic tensor chart is the constructed terminal smoothing node. -/
def arithmeticTerminalNodeEquiv : T₀ ≃ₐ[Q] NodalFiber.Coordinate c :=
  tensorTerminalNodeEquiv W s b3 b4 b6 Q r J hJ hrI (ha.map q) h4₀ h6₀ hr

/-- The entire node isomorphism over the original quotient, including its horizontal origin. -/
def arithmeticTerminalNodeIso : Spec (.of (NodalFiber.Coordinate c)) ≅ Spec (.of T₀) :=
  tensorTerminalNodeIso W s b3 b4 b6 Q r J hJ hrI (ha.map q) h4₀ h6₀ hr

/-- The quotient-specific node isomorphism retains its original coefficient morphism. -/
@[reassoc] theorem arithmeticTerminalNodeIso_structure :
    (arithmeticTerminalNodeIso π m W s b3 b4 b6 ha hs h2 h4 h6).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q T₀)) =
        Spec.map (CommRingCat.ofHom (algebraMap Q (NodalFiber.Coordinate c))) :=
  tensorTerminalNodeIso_structure W s b3 b4 b6 Q r J hJ hrI (ha.map q) h4₀ h6₀ hr

end FLT.Mazur.WeierstrassDilatation
