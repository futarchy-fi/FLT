/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationArithmeticNormalizationRestriction

/-!
# The original tensor restriction on full terminal arithmetic cubics

The tensor map applies the actual quotient restriction to the coefficient
factor. The explicit cubic base-change equivalences commute with this map.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Constants and both original cubic coordinates determine every ring map. -/
theorem coefficient_ringHom_ext {R T : Type*} [CommRing R] [CommRing T]
    (W : WeierstrassCurve R) (s b3 b4 b6 : R)
    (g h : Coordinate W s b3 b4 b6 →+* T)
    (hc : ∀ a, g (algebraMap R _ a) = h (algebraMap R _ a))
    (hx : g (x W s b3 b4 b6) = h (x W s b3 b4 b6))
    (hy : g (y W s b3 b4 b6) = h (y W s b3 b4 b6)) : g = h := by
  let _ := (g.comp (algebraMap R (Coordinate W s b3 b4 b6))).toAlgebra
  let g' : Coordinate W s b3 b4 b6 →ₐ[R] T := ⟨g, fun _ ↦ rfl⟩
  let h' : Coordinate W s b3 b4 b6 →ₐ[R] T := ⟨h, fun a ↦ (hc a).symm⟩
  exact congrArg AlgHom.toRingHom (hom_ext W s b3 b4 b6 g' h' hx hy)

variable (R : Type*) [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "T₀" => ScalarExtension W s b3 b4 b6 Q₀
local notation "T₁" => ScalarExtension W s b3 b4 b6 Q₁
local notation "g" => arithmeticTerminalCoefficientMap R π m W s b3 b4 b6

/-- Apply the original quotient restriction to the actual tensor coefficient factor. -/
def arithmeticTerminalTensorMap : T₁ →ₐ[R] T₀ :=
  Algebra.TensorProduct.map (restriction R π m) (AlgHom.id R _)

/-- The original cubic factor is retained on every pure tensor. -/
theorem arithmeticTerminalTensorMap_tmul (a : Q₁) (z : Coordinate W s b3 b4 b6) :
    arithmeticTerminalTensorMap R π m W s b3 b4 b6 (a ⊗ₜ[R] z) =
      restriction R π m a ⊗ₜ[R] z := rfl

/-- Coefficients use precisely the original quotient restriction. -/
theorem arithmeticTerminalTensorMap_scalar (a : Q₁) :
    arithmeticTerminalTensorMap R π m W s b3 b4 b6 (algebraMap Q₁ T₁ a) =
      algebraMap Q₀ T₀ (f a) := by
  change arithmeticTerminalTensorMap R π m W s b3 b4 b6 (a ⊗ₜ[R] 1) = _
  rw [arithmeticTerminalTensorMap_tmul]
  rfl

/-- The actual tensor restriction commutes with the entire cubic base-change inverse. -/
theorem arithmeticTerminalTensorMap_backward :
    (arithmeticTerminalTensorMap R π m W s b3 b4 b6).toRingHom.comp
        (baseChangeBackward W s b3 b4 b6 Q₁).toRingHom =
      (baseChangeBackward W s b3 b4 b6 Q₀).toRingHom.comp g := by
  apply coefficient_ringHom_ext (W.map q₁) (q₁ s) (q₁ b3) (q₁ b4) (q₁ b6)
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, arithmeticTerminalTensorMap_scalar,
      arithmeticTerminalCoefficientMap_scalar]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      baseChangeBackward_x, arithmeticTerminalCoefficientMap_x,
      arithmeticTerminalTensorMap_tmul, map_one]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      baseChangeBackward_y, arithmeticTerminalCoefficientMap_y,
      arithmeticTerminalTensorMap_tmul, map_one]

end FLT.Mazur.WeierstrassDilatation
