/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.RationalComplexConjugation

/-!
# Complex conjugation on integral characters

The chosen rational complex conjugation is an involution. A character valued
in the units of a domain therefore sends it to one or minus one.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- A domain-valued integral character sends complex conjugation to one of the two signs. -/
theorem character_conjugation_of_domain
    {O : Type*} [CommRing O] [IsDomain O]
    (ψ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Oˣ) :
    (ψ rationalComplexConjugation : O) = 1 ∨
      (ψ rationalComplexConjugation : O) = -1 := by
  apply mul_self_eq_one_iff.mp
  have h := congrArg (fun g ↦ (ψ g : O)) rationalComplexConjugation_mul_self
  simpa only [map_mul, Units.val_mul, map_one, Units.val_one] using h

end ThreeAdicPlan
