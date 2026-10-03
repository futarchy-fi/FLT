/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FrobeniusRestrictionScale
public import FLT.LocalClassFieldTheory.TrivialRestrictionNaturality
public import FLT.LocalClassFieldTheory.UnramifiedIntegralH2Additive

/-!
# Residue-degree scaling on integral unramified H2

The proved Frobenius restriction formula and naturality of the integral
connecting map give the residue-degree factor on rational-circle coordinates.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing HomologicalComplex

variable (R S K L C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [Field C] [Algebra L C] [Algebra K C] [Algebra R C] [Algebra S C]
  [IsScalarTower K L C] [IsScalarTower R K C] [IsScalarTower R L C]
  [IsScalarTower S L C] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [Algebra.IsSeparable L C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S L C


attribute [local instance] unramifiedH2Galois
  trivialCoefficientAction trivialCoefficientIntComm trivialCoefficientContinuous
  rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

/-- The actual restriction of unramified Galois groups, as a continuous homomorphism. -/
def unramifiedBaseChangeContinuousRestriction : Gal(B/L) →ₜ* Gal(A/K) :=
  ⟨unramifiedBaseChangeRestriction R S K L C,
    unramifiedBaseChangeRestriction_continuous R S K L C⟩

/-- Integral H2 restriction multiplies Frobenius coordinates by the residue degree. -/
theorem unramifiedIntegralH2_baseChange (x : continuousCohomology ℤ Gal(A/K) ℤ 2) :
    unramifiedIntegralH2AddEquiv S L C
        ((homologyMap (trivialRestriction
          (unramifiedBaseChangeContinuousRestriction R S K L C) ℤ) 2).hom x) =
      Module.finrank (ResidueField R) (ResidueField S) •
        unramifiedIntegralH2AddEquiv R K C x := by
  obtain ⟨χ, rfl⟩ := (integralH2CharacterEquiv Gal(A/K)).surjective x
  rw [integralH2CharacterEquiv_restriction]
  change unramifiedIntegralH2Equiv S L C _ = _ • unramifiedIntegralH2Equiv R K C _
  rw [unramifiedIntegralH2Equiv_character, unramifiedIntegralH2Equiv_character]
  change (χ (unramifiedBaseChangeRestriction R S K L C (unramifiedFrobenius S L C))).toAdd = _
  rw [unramifiedFrobenius_baseChange, map_pow]
  rfl

end LocalClassFieldTheory
