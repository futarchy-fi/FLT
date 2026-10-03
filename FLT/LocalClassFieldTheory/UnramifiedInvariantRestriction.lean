/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalDegreeFormula
public import FLT.LocalClassFieldTheory.UnramifiedBaseChangeOrderCohomology

/-!
# Degree multiplication for the unramified invariant

Ramification scales coefficient order, residue degree scales the integral
Frobenius coordinate, and their product is the fraction-field degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex

variable (R S K L C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [Field C] [Algebra L C] [Algebra K C] [Algebra R C] [Algebra S C]
  [IsScalarTower K L C] [IsScalarTower R K C] [IsScalarTower R L C]
  [IsScalarTower S L C] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [Algebra.IsSeparable L C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S L C

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  trivialCoefficientAction trivialCoefficientIntComm trivialCoefficientContinuous
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete

/-- The unramified multiplicative invariant scales by e times f under actual base change. -/
theorem unramifiedMultiplicativeInvariant_baseChange_ef
    (x : continuousCohomology ℤ Gal(A/K) (Additive Aˣ) 2) :
    unramifiedMultiplicativeInvariant S L C
        ((unramifiedBaseChangeCohomology R S K L C 2).hom x) =
      ((maximalIdeal R).ramificationIdx' (maximalIdeal S) *
        Module.finrank (ResidueField R) (ResidueField S)) •
          unramifiedMultiplicativeInvariant R K C x := by
  have h := congrArg (fun t => t.hom x) (unramifiedBaseChangeOrder_cohomology R S K L C 2)
  change unramifiedIntegralH2AddEquiv S L C
    ((continuousCoefficientCohomologyMap (unramifiedUnionOrderMap S L C) 2).hom
      ((unramifiedBaseChangeCohomology R S K L C 2).hom x)) = _
  change (continuousCoefficientCohomologyMap (unramifiedUnionOrderMap S L C) 2).hom
      ((unramifiedBaseChangeCohomology R S K L C 2).hom x) =
    (maximalIdeal R).ramificationIdx' (maximalIdeal S) •
      (homologyMap (trivialRestriction (unramifiedBaseChangeContinuousRestriction R S K L C) ℤ)
        2).hom ((continuousCoefficientCohomologyMap (unramifiedUnionOrderMap R K C) 2).hom x) at h
  rw [h, map_nsmul, unramifiedIntegralH2_baseChange, ← mul_smul]
  rfl

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- Actual base change multiplies the unramified invariant in Q/Z by the field degree. -/
theorem unramifiedMultiplicativeInvariant_baseChange
    (x : continuousCohomology ℤ Gal(A/K) (Additive Aˣ) 2) :
    unramifiedMultiplicativeInvariant S L C
        ((unramifiedBaseChangeCohomology R S K L C 2).hom x) =
      Module.finrank K L • unramifiedMultiplicativeInvariant R K C x := by
  rw [unramifiedMultiplicativeInvariant_baseChange_ef,
    localDegree_eq_ramification_mul_residue R S K L]

end LocalClassFieldTheory
