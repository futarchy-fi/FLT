/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationArithmeticTensorRestriction

/-!
# Full arithmetic tensor normalization commutes with quotient restriction

The square uses the original tensor coefficient map and the independently
constructed full node isomorphisms, including all nilpotent corrections.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
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

local notation "E₁" => arithmeticTerminalNodeEquiv π (m + 1) W s b3 b4 b6 ha hs h2 h4 h6
local notation "E₀" => arithmeticTerminalNodeEquiv π m W s b3 b4 b6 ha hs h2 h4 h6
local notation "T" => arithmeticTerminalTensorMap R π m W s b3 b4 b6

/-- The inverse full tensor normalizations commute on every original node function. -/
theorem arithmeticTerminalNodeEquiv_symm_restriction :
    (T).toRingHom.comp (E₁).symm.toAlgHom.toRingHom =
      (E₀).symm.toAlgHom.toRingHom.comp N := by
  apply RingHom.ext
  intro z
  change T (baseChangeBackward W s b3 b4 b6 Q₁ ((e₁).symm z)) =
    baseChangeBackward W s b3 b4 b6 Q₀ ((e₀).symm (N z))
  have hb := DFunLike.congr_fun
    (arithmeticTerminalTensorMap_backward R π m W s b3 b4 b6) ((e₁).symm z)
  have hn := DFunLike.congr_fun
    (arithmeticTerminalNormalization_symm_restriction R π m W s b3 b4 b6 ha hs h2 h4 h6) z
  exact hb.trans (congrArg (baseChangeBackward W s b3 b4 b6 Q₀) hn)

/-- The full tensor normalizations commute on every original tensor function. -/
theorem arithmeticTerminalNodeEquiv_restriction :
    (E₀).toAlgHom.toRingHom.comp (T).toRingHom = (N).comp (E₁).toAlgHom.toRingHom := by
  apply RingHom.ext
  intro z
  change E₀ (T z) = N (E₁ z)
  have h := DFunLike.congr_fun
    (arithmeticTerminalNodeEquiv_symm_restriction R π m W s b3 b4 b6 ha hs h2 h4 h6) (E₁ z)
  change T ((E₁).symm (E₁ z)) = (E₀).symm (N (E₁ z)) at h
  simpa only [AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply] using congrArg E₀ h

/-- The actual original full node isomorphisms form a commuting arithmetic scheme square. -/
@[reassoc] theorem arithmeticTerminalNodeIso_restriction :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom N) ≫
      (arithmeticTerminalNodeIso π (m + 1) W s b3 b4 b6 ha hs h2 h4 h6).hom =
    (arithmeticTerminalNodeIso π m W s b3 b4 b6 ha hs h2 h4 h6).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (T).toRingHom) := by
  change AlgebraicGeometry.Spec.map _ ≫ AlgebraicGeometry.Spec.map _ =
    AlgebraicGeometry.Spec.map _ ≫ AlgebraicGeometry.Spec.map _
  simp only [← AlgebraicGeometry.Spec.map_comp]
  exact congrArg (fun h ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom h))
    (arithmeticTerminalNodeEquiv_restriction R π m W s b3 b4 b6 ha hs h2 h4 h6).symm

/-- The inverse full node isomorphisms retain the same original quotient restriction. -/
@[reassoc] theorem arithmeticTerminalNodeIso_inv_restriction :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (T).toRingHom) ≫
      (arithmeticTerminalNodeIso π (m + 1) W s b3 b4 b6 ha hs h2 h4 h6).inv =
    (arithmeticTerminalNodeIso π m W s b3 b4 b6 ha hs h2 h4 h6).inv ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom N) := by
  change AlgebraicGeometry.Spec.map _ ≫ AlgebraicGeometry.Spec.map _ =
    AlgebraicGeometry.Spec.map _ ≫ AlgebraicGeometry.Spec.map _
  simp only [← AlgebraicGeometry.Spec.map_comp]
  exact congrArg (fun h ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom h))
    (arithmeticTerminalNodeEquiv_symm_restriction R π m W s b3 b4 b6 ha hs h2 h4 h6)

end FLT.Mazur.WeierstrassDilatation
