/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PrimeCyclotomicCoefficients
public import Mathlib.Algebra.Module.ZMod

/-!
# The canonical prime-field structure on root coefficients

The module structure uses the exponent relation, independently of a
primitive root. Galois automorphisms commute with these scalars.
-/

@[expose] public section

namespace KummerTheory

variable {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- The root group has exponent dividing p. -/
theorem rootModule_p_nsmul (x : RootModule L p) : p • x = 0 := by
  apply rootUnit_injective
  exact rootUnit_pow x

instance : Module (ZMod p) (RootModule L p) := AddCommGroup.zmodModule rootModule_p_nsmul

variable {K : Type*} [Field K] [Algebra K L]

instance : SMulCommClass Gal(L/K) (ZMod p) (RootModule L p) where
  smul_comm g a x := ZMod.map_smul
    ({ toFun := fun y ↦ g • y
       map_zero' := smul_zero g
       map_add' := smul_add g } : RootModule L p →+ RootModule L p) a x

variable {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)

/-- Primitive-root coordinates are linear for the canonical prime-field structure. -/
noncomputable def primeCyclotomicLinearCoordinates :
    GaloisRepresentation.Extensions.CharacterModule
      (primeCyclotomicCharacter (K := K) hζ) (ZMod p) ≃ₗ[ZMod p] RootModule L p :=
  { primeCyclotomicCoordinates hζ with
    map_smul' := fun a x ↦ ZMod.map_smul (primeCyclotomicCoordinates hζ) a x }

end KummerTheory
