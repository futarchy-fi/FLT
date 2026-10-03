/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedContinuousOrderH2
public import FLT.LocalClassFieldTheory.ContinuousRestrictionCohomology

/-!
# Multiplicative inflation to the separable closure

Restriction of automorphisms and inclusion of field units define inflation
on actual continuous cohomology. This constructs the map and its colimit
compatibility; it does not assert that inflation is an isomorphism.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex Limits

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "U" => maximalUnramified R K C
local notation "G" => Gal(U/K)
local notation "H" => Gal(C/K)
local notation "res" => unramifiedRestriction R K C

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete

local instance separableClosureGalois : IsGalois K C := by
  let : IsSepClosure K C := ⟨inferInstance, inferInstance⟩
  infer_instance

/-- The multiplicative coefficients of the separable closure use the discrete topology. -/
local instance separableClosureUnitTopology : TopologicalSpace (Additive Cˣ) := ⊥
local instance separableClosureUnitDiscrete : DiscreteTopology (Additive Cˣ) := ⟨rfl⟩

/-- Inclusion of unramified field units, equivariant under Galois restriction. -/
def unramifiedMultiplicativeInflationCoefficients :
    Rep.res res (Rep.of (Representation.ofDistribMulAction ℤ G (Additive Uˣ))) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ H (Additive Cˣ)) :=
  Rep.ofHom ⟨(Units.map (maximalUnramified R K C).val.toMonoidHom).toAdditive.toIntLinearMap,
    fun g => by
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Units.ext
      exact AlgEquiv.restrictNormal_apply U g (Additive.toMul x : Uˣ)⟩

/-- The actual multiplicative inflation from the unramified union to the separable closure. -/
def unramifiedMultiplicativeInflation (i : ℕ) :
    continuousCohomology ℤ G (Additive Uˣ) i ⟶ continuousCohomology ℤ H (Additive Cˣ) i :=
  homologyMap (continuousRestriction res (unramifiedRestriction_continuous R K C)
    (unramifiedMultiplicativeInflationCoefficients R K C)) i

/-- Inflation agrees with the maps on the genuine finite invariant stages. -/
theorem unramifiedMultiplicativeInflation_colimit (i : ℕ) :
    colimMap (restrictionStageCohomologyNat res (unramifiedRestriction_continuous R K C)
        (unramifiedMultiplicativeInflationCoefficients R K C) i) ≫
      colimit.pre (invariantStageCohomologyDiagram ℤ H (Additive Cˣ) i)
        (restrictionStageFunctor res (unramifiedRestriction_continuous R K C)) ≫
      (continuousCohomologyColimitIso ℤ H (Additive Cˣ) i).hom =
    (continuousCohomologyColimitIso ℤ G (Additive Uˣ) i).hom ≫
      unramifiedMultiplicativeInflation R K C i :=
  continuousRestriction_cohomologyColimit res (unramifiedRestriction_continuous R K C)
    (unramifiedMultiplicativeInflationCoefficients R K C) i

end LocalClassFieldTheory
