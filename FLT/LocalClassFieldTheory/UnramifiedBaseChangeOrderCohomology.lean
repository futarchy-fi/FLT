/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedBaseChangeCohomology
public import FLT.LocalClassFieldTheory.UnramifiedIntegralH2Restriction
public import FLT.LocalClassFieldTheory.UnramifiedMultiplicativeInvariant

/-!
# Ramification scaling on continuous order cohomology

The proved coefficient-order square commutes on continuous cochains and
therefore on cohomology. This keeps the ramification factor separate from
the residue-degree factor in restriction of integral cohomology.
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

/-- Base change followed by normalized order is ramification times integral restriction. -/
theorem unramifiedBaseChangeOrder_cochains :
    continuousRestriction (unramifiedBaseChangeRestriction R S K L C)
        (unramifiedBaseChangeRestriction_continuous R S K L C)
        (unramifiedBaseChangeCoefficients R S K L C) ≫
      continuousCoefficientMap (unramifiedUnionOrderMap S L C) =
    (maximalIdeal R).ramificationIdx' (maximalIdeal S) •
      (continuousCoefficientMap (unramifiedUnionOrderMap R K C) ≫
        trivialRestriction (unramifiedBaseChangeContinuousRestriction R S K L C) ℤ) := by
  ext n c : 3
  apply Subtype.ext
  funext g
  exact unramifiedBaseChangeCoefficients_order R S K L C
    (c.val (unramifiedBaseChangeRestriction R S K L C ∘ g))

/-- The ramification order square descends to actual continuous cohomology. -/
theorem unramifiedBaseChangeOrder_cohomology (n : ℕ) :
    unramifiedBaseChangeCohomology R S K L C n ≫
        continuousCoefficientCohomologyMap (unramifiedUnionOrderMap S L C) n =
      (maximalIdeal R).ramificationIdx' (maximalIdeal S) •
        (continuousCoefficientCohomologyMap (unramifiedUnionOrderMap R K C) n ≫
          homologyMap (trivialRestriction
            (unramifiedBaseChangeContinuousRestriction R S K L C) ℤ) n) := by
  unfold unramifiedBaseChangeCohomology continuousCoefficientCohomologyMap
  rw [← homologyMap_comp, ← homologyMap_comp, unramifiedBaseChangeOrder_cochains]
  exact (homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).map_nsmul

end LocalClassFieldTheory
