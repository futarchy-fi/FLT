/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RootModuleLinear
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Characters of finite prime-field modules

Every multiplicative character takes values in the prime roots of unity.
Primitive-root coordinates identify these characters with the linear dual.
-/

@[expose] public noncomputable section
namespace KummerTheory

variable {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
  {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
  (V : Type*) [AddCommGroup V] [Module (ZMod p) V]

/-- A linear functional determines a root-valued multiplicative character. -/
def primeDualCharacter (f : Module.Dual (ZMod p) V) : Multiplicative V →* L where
  toFun a := rootUnit (primeRootCoordinates hζ (f a.toAdd))
  map_one' := by simp
  map_mul' a b := by simp [map_add]

/-- A character of a prime-field module takes values in p-th roots of unity. -/
def primeCharacterRoot (χ : Multiplicative V →* L) (x : V) : RootModule L p :=
  Additive.ofMul ⟨χ.toHomUnits (Multiplicative.ofAdd x), by
    change χ.toHomUnits (Multiplicative.ofAdd x) ^ p = 1
    rw [← map_pow]
    simp [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), CharP.cast_eq_zero]⟩

/-- Root extraction preserves the additive law. -/
theorem primeCharacterRoot_add (χ : Multiplicative V →* L) (x y : V) :
    primeCharacterRoot (p := p) V χ (x + y) =
      primeCharacterRoot (p := p) V χ x + primeCharacterRoot (p := p) V χ y := by
  apply rootUnit_injective
  exact map_mul χ.toHomUnits (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

/-- Extract the linear functional of an arbitrary character. -/
def primeCharacterDual (χ : Multiplicative V →* L) : Module.Dual (ZMod p) V :=
  ((primeRootCoordinates hζ).symm.toAddMonoidHom.comp
    (AddMonoidHom.mk' (primeCharacterRoot (p := p) V χ)
      (primeCharacterRoot_add (p := p) V χ))).toZModLinearMap p

/-- Extracting coordinates from the constructed character recovers the functional. -/
@[simp] theorem primeCharacterDual_character (f : Module.Dual (ZMod p) V) :
    primeCharacterDual hζ V (primeDualCharacter hζ V f) = f := by
  ext x
  apply (primeRootCoordinates hζ).injective
  change primeRootCoordinates hζ ((primeRootCoordinates hζ).symm _) = _
  rw [AddEquiv.apply_symm_apply]
  apply rootUnit_injective
  apply Units.ext
  rfl

/-- Reconstructing a character from its extracted functional recovers every value. -/
@[simp] theorem primeDualCharacter_dual (χ : Multiplicative V →* L) :
    primeDualCharacter hζ V (primeCharacterDual hζ V χ) = χ := by
  ext a
  change (rootUnit (primeRootCoordinates hζ ((primeRootCoordinates hζ).symm _)) : L) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The full character group is the prime-field linear dual, without counting points. -/
def primeDualCharacterEquiv : Module.Dual (ZMod p) V ≃ (Multiplicative V →* L) where
  toFun := primeDualCharacter hζ V
  invFun := primeCharacterDual hζ V
  left_inv := primeCharacterDual_character hζ V
  right_inv := primeDualCharacter_dual hζ V

end KummerTheory
