/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationSmoothingNaturality
public import FLT.Mazur.WeierstrassDilatationArithmeticTerminalNode
public import FLT.Mazur.WeierstrassSuccessiveArithmeticRestrictionMaps

/-!
# The original terminal smoothing constants form a compatible arithmetic system

Both the polynomial tangent root and the complete constructed smoothing
commute with the original consecutive quotient restrictions.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] terminalTangentRoot terminalSmoothing
variable (R : Type*) [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "I" => ideal Q₁ (parameter R π (m + 1))
local notation "J" => ideal Q₀ (parameter R π m)
local notation "hI" => arithmeticParameterIdeal_nilpotent π (m + 1)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m
local notation "hf" => arithmeticParameterIdeal_restriction R π m
local notation "r₁" => terminalTangentRoot (W.map q₁) (q₁ s) I hI (ha.map q₁)
  (arithmeticCoefficient_mem π (m + 1) hs) (arithmeticCoefficient_mem π (m + 1) h2)
local notation "r₀" => terminalTangentRoot (W.map q₀) (q₀ s) J hJ (ha.map q₀)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)

/-- The complete original polynomial root commutes with quotient-order restriction. -/
theorem arithmeticTerminalTangentRoot_restriction : (r₁).map f = r₀ := by
  exact terminalTangentRoot_map f I J hf (W.map q₁) (q₁ s) hI hJ (ha.map q₁)
    (arithmeticCoefficient_mem π (m + 1) hs) (arithmeticCoefficient_mem π (m + 1) h2)

/-- The actual smoothing constants are compatible at every adjacent original quotient order. -/
theorem arithmeticTerminalSmoothing_restriction :
    restriction R π m (arithmeticTerminalSmoothing π (m + 1) W s b3 b4 b6 ha hs h2 h4 h6) =
      arithmeticTerminalSmoothing π m W s b3 b4 b6 ha hs h2 h4 h6 := by
  have h := terminalSmoothing_map f (W.map q₁) (q₁ b3) (q₁ b4) (q₁ b6) r₁ I hI J hJ hf
    (terminalTangentRoot_mem (W.map q₁) (q₁ s) I hI (ha.map q₁)
      (arithmeticCoefficient_mem π (m + 1) hs) (arithmeticCoefficient_mem π (m + 1) h2))
    (ha.map q₁) (arithmeticCoefficient_mem π (m + 1) h4)
      (arithmeticCoefficient_mem π (m + 1) h6)
  have hc : (W.map q₁).map f = W.map q₀ := by
    rw [WeierstrassCurve.map_map]
    exact congrArg W.map (restriction R π m).comp_algebraMap
  have hcoeff (a : R) : f (q₁ a) = q₀ a := (restriction R π m).commutes a
  simp only [hc, hcoeff, arithmeticTerminalTangentRoot_restriction R π m W s ha hs h2] at h
  exact h

end FLT.Mazur.WeierstrassDilatation
