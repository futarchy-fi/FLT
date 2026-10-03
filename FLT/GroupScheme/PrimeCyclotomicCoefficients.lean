/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PrimeRootCoordinates
public import FLT.GaloisRepresentation.Extensions.CharacterCoefficients
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# The prime cyclotomic character and root coefficients

The character is the actual action on roots of unity. A primitive root
supplies the coefficient equivalence, not an assumed comparison of classes.
-/

@[expose] public section

namespace KummerTheory

open GaloisRepresentation.Extensions

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)

/-- Restrict the modular cyclotomic character to the relative Galois group. -/
noncomputable def primeCyclotomicCharacter : Gal(L/K) →* (ZMod p)ˣ :=
  (modularCyclotomicCharacter L hζ.card_rootsOfUnity').comp
    { toFun := fun g ↦ g.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }

/-- The prime-field cyclotomic line is the natural root coefficient group. -/
noncomputable def primeCyclotomicCoordinates :
    CharacterModule (primeCyclotomicCharacter (K := K) hζ) (ZMod p) ≃+ RootModule L p :=
  primeRootCoordinates hζ

/-- The chosen coordinates intertwine the actual cyclotomic action. -/
theorem primeCyclotomicCoordinates_equivariant (g : Gal(L/K))
    (x : CharacterModule (primeCyclotomicCharacter (K := K) hζ) (ZMod p)) :
    primeCyclotomicCoordinates hζ (g • x) = g • primeCyclotomicCoordinates hζ x := by
  dsimp [CharacterModule] at x
  change primeRootCoordinates hζ ((primeCyclotomicCharacter hζ g : ZMod p) * x) = _
  rw [primeRootCoordinates_mul]
  apply rootUnit_injective
  change rootUnit (primeRootCoordinates hζ x) ^
    (primeCyclotomicCharacter hζ g : ZMod p).val = g • rootUnit (primeRootCoordinates hζ x)
  apply Units.ext
  exact (modularCyclotomicCharacter.spec L hζ.card_rootsOfUnity' g.toRingEquiv
    (primeRootCoordinates hζ x).toMul.property).symm

/-- Continuous prime-character classes identify with continuous root classes. -/
noncomputable def primeCyclotomicClassEquiv :
    ContinuousClass Gal(L/K)
      (CharacterModule (primeCyclotomicCharacter (K := K) hζ) (ZMod p)) ≃
        ContinuousClass Gal(L/K) (RootModule L p) :=
  coefficientClassEquiv (primeCyclotomicCoordinates hζ)
    (primeCyclotomicCoordinates_equivariant hζ)

end KummerTheory
