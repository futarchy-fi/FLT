/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationNormalizationTransport
public import FLT.Mazur.WeierstrassDilatationArithmeticCoefficientRestriction

/-!
# Full terminal normalization over consecutive original arithmetic quotients

The original quotient map preserves the complete canonical normalization,
with independently constructed tangent roots and smoothing constants.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] terminalTangentRoot terminalSmoothing terminalNodeEquiv
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
local notation "c₁" => arithmeticTerminalSmoothing π (m + 1) W s b3 b4 b6 ha hs h2 h4 h6
local notation "c₀" => arithmeticTerminalSmoothing π m W s b3 b4 b6 ha hs h2 h4 h6
local notation "e₁" => canonicalTerminalNodeEquiv (W.map q₁) (q₁ s) (q₁ b3) (q₁ b4)
  (q₁ b6) I hI (ha.map q₁) (arithmeticCoefficient_mem π (m + 1) h4)
  (arithmeticCoefficient_mem π (m + 1) h6) (arithmeticCoefficient_mem π (m + 1) hs)
  (arithmeticCoefficient_mem π (m + 1) h2)
local notation "e₀" => canonicalTerminalNodeEquiv (W.map q₀) (q₀ s) (q₀ b3) (q₀ b4)
  (q₀ b6) J hJ (ha.map q₀) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6) (arithmeticCoefficient_mem π m hs)
  (arithmeticCoefficient_mem π m h2)
local notation "g" => arithmeticTerminalCoefficientMap R π m W s b3 b4 b6
local notation "N" => NodalFiber.coefficientRingMap f c₁ c₀
  (arithmeticTerminalSmoothing_restriction R π m W s b3 b4 b6 ha hs h2 h4 h6)

/-- The inverse full normalization commutes with the original quotient-order restriction. -/
theorem arithmeticTerminalNormalization_symm_restriction :
    (g).comp (e₁).symm.toAlgHom.toRingHom = (e₀).symm.toAlgHom.toRingHom.comp N := by
  exact canonicalTerminalNodeEquiv_symm_transport f (W.map q₁) (q₁ s) (q₁ b3)
    (q₁ b4) (q₁ b6) (W.map q₀) (q₀ s) (q₀ b3) (q₀ b4) (q₀ b6)
    (arithmeticTerminalCurve_restriction R π m W) ((restriction R π m).commutes s)
    ((restriction R π m).commutes b3) ((restriction R π m).commutes b4)
    ((restriction R π m).commutes b6) I hI J hJ hf (ha.map q₁)
    (arithmeticCoefficient_mem π (m + 1) hs) (arithmeticCoefficient_mem π (m + 1) h2)
    (arithmeticCoefficient_mem π (m + 1) h4) (arithmeticCoefficient_mem π (m + 1) h6)
    (ha.map q₀) (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)

/-- The forward full normalization commutes on every original cubic function. -/
theorem arithmeticTerminalNormalization_restriction :
    (e₀).toAlgHom.toRingHom.comp g = (N).comp (e₁).toAlgHom.toRingHom := by
  apply RingHom.ext
  intro z
  change e₀ (g z) = N (e₁ z)
  have h := DFunLike.congr_fun
    (arithmeticTerminalNormalization_symm_restriction R π m W s b3 b4 b6 ha hs h2 h4 h6)
    (e₁ z)
  change g ((e₁).symm (e₁ z)) = (e₀).symm (N (e₁ z)) at h
  simpa only [AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply] using congrArg e₀ h

end FLT.Mazur.WeierstrassDilatation
