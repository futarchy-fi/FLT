/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarPrimeThickenings
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual transitions between original local scalar orders

All orders use the same original localization. Their quotient transitions
are surjective, preserve the original scalar map, and compose exactly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ScalarPrimeThickenings
variable {R : Type} [CommRing R] (P : PrimeSpectrum R) {m n l : ℕ}

/-- The actual quotient map from a higher local order to a lower one. -/
def primeThickeningTransition (h : m ≤ n) :
    primeThickeningRing P n →+* primeThickeningRing P m :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- Each transition preserves the unchanged original scalar action. -/
theorem primeThickeningTransition_scalars (h : m ≤ n) :
    (primeThickeningTransition P h).comp (primeThickeningMap P n) =
      primeThickeningMap P m := rfl

/-- Every lower-order scalar lifts to the higher order. -/
theorem primeThickeningTransition_surjective (h : m ≤ n) :
    Function.Surjective (primeThickeningTransition P h) :=
  Ideal.Quotient.factor_surjective _

/-- Equal-order transition is the identity. -/
theorem primeThickeningTransition_self :
    primeThickeningTransition P (le_refl n) = RingHom.id _ := Ideal.Quotient.factor_eq

/-- Quotient transitions compose on the original local ring. -/
theorem primeThickeningTransition_comp (h : l ≤ m) (h' : m ≤ n) :
    (primeThickeningTransition P h).comp (primeThickeningTransition P h') =
      primeThickeningTransition P (h.trans h') :=
  Ideal.Quotient.factor_comp _ _

/-- The actual infinitesimal test over the original scalar spectrum. -/
abbrev primeThickeningTest (n : ℕ) := Spec.map (CommRingCat.ofHom (primeThickeningMap P n))

/-- The transition is an actual scheme map between these tests. -/
abbrev primeThickeningInclusion (h : m ≤ n) :=
  Spec.map (CommRingCat.ofHom (primeThickeningTransition P h))

/-- The test transition lies over the unchanged scalar spectrum. -/
theorem primeThickeningInclusion_scalars (h : m ≤ n) :
    primeThickeningInclusion P h ≫ primeThickeningTest P n = primeThickeningTest P m := by
  rw [← Spec.map_comp]
  rfl

/-- Scalar transitions are closed immersions, retaining every infinitesimal order. -/
instance primeThickeningInclusion_isClosedImmersion (h : m ≤ n) :
    IsClosedImmersion (primeThickeningInclusion P h) :=
  IsClosedImmersion.spec_of_surjective _ (primeThickeningTransition_surjective P h)

end FLT.Mazur.ScalarPrimeThickenings
