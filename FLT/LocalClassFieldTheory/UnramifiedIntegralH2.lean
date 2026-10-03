/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedFrobeniusCharacters
public import FLT.LocalClassFieldTheory.IntegralH2Characters

/-!
# Integral H2 of the constructed unramified quotient

The integral connecting isomorphism followed by Frobenius evaluation gives
Q/Z coordinates. This concerns constant integral coefficients, not multiplicative units.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

attribute [local instance] trivialCoefficientAction trivialCoefficientIntComm
  trivialCoefficientContinuous rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]


local notation "U" => maximalUnramified R K C
local notation "Frob" => unramifiedFrobenius R K C

local instance unramifiedH2Galois : IsGalois K U := maximalUnramified_isGalois R K C

/-- Integral H2 of the unramified Galois quotient is parametrized by Q/Z. -/
def unramifiedIntegralH2Equiv : continuousCohomology ℤ Gal(U/K) ℤ 2 ≃ AddCircle (1 : ℚ) :=
  (integralH2CharacterEquiv Gal(U/K)).symm.trans (unramifiedFrobeniusCharacterEquiv R K C)

/-- The boundary of a character has the character's arithmetic Frobenius value. -/
theorem unramifiedIntegralH2Equiv_character
    (χ : Gal(U/K) →ₜ* Multiplicative (AddCircle (1 : ℚ))) :
    unramifiedIntegralH2Equiv R K C (integralH2CharacterEquiv Gal(U/K) χ) =
      (χ Frob).toAdd := by
  change unramifiedFrobeniusCharacterEquiv R K C
    ((integralH2CharacterEquiv Gal(U/K)).symm (integralH2CharacterEquiv Gal(U/K) χ)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The degree-n character gives the positive integral H2 coordinate 1/n. -/
theorem unramifiedIntegralH2Equiv_degree (n : UnramifiedIndex) :
    unramifiedIntegralH2Equiv R K C
        (integralH2CharacterEquiv Gal(U/K) (unramifiedRationalCircleCharacter R K C n)) =
      (↑((1 : ℚ) / n.degree) : AddCircle (1 : ℚ)) := by
  rw [unramifiedIntegralH2Equiv_character, unramifiedRationalCircleCharacter_frobenius]

/-- All rational-circle coordinates are realized by actual integral cohomology classes. -/
theorem unramifiedIntegralH2Equiv_surjective :
    Function.Surjective (unramifiedIntegralH2Equiv R K C) :=
  (unramifiedIntegralH2Equiv R K C).surjective

end LocalClassFieldTheory
