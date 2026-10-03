/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeFundamentalRestriction
public import FLT.LocalClassFieldTheory.RelativeFundamentalTateCup
public import FLT.LocalClassFieldTheory.FiniteRestrictionComparison

/-!
# Ordinary finite-relative fundamental restriction

Transport the proved arithmetic restriction identity through the finite
continuous comparison. This supplies the ordinary two-class identity needed
by the concrete two-extension construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R S T K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Algebra R T] [Module.Finite R T] [FaithfulSMul R T]
  [Algebra S T] [Module.Finite S T] [FaithfulSMul S T]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C) (F : IntermediateField E C)
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S E] [IsScalarTower R S C]
  [Algebra T F] [IsFractionRing T F] [Algebra T C] [IsScalarTower T F C]
  [IsScalarTower R T C] [IsScalarTower S T C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)] [Finite (ResidueField T)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]
  [IsAdicComplete (maximalIdeal T) T]
  [IsGalois K (F.restrictScalars K)] [IsGalois E F]
  [FiniteDimensional K E] [FiniteDimensional K (F.restrictScalars K)]

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

attribute [local instance] relativeFundamentalRestrictionFinite
  relativeFundamentalRestrictionFiniteOverBase relativeFundamentalRestrictionTopAlgebra
  relativeFundamentalRestrictionTopFractionRing relativeFundamentalRestrictionTopTower
  relativeFundamentalRestrictionBaseTower relativeFundamentalRestrictionMiddleTower
  relativeRestrictionGalois

variable [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]

attribute [local instance] relativeFundamentalRestrictionUnitTopology
  relativeFundamentalRestrictionUnitDiscrete

variable [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p]

include p in
/-- The ordinary two-class restricts to the fundamental class over the intermediate field. -/
theorem relativeFundamentalOrdinaryClass_restriction :
    groupCohomology.map (AlgEquiv.restrictScalarsHom K)
        (relativeRestrictionCoefficients K C E F) 2
        (relativeFundamentalOrdinaryClass R T K C (F.restrictScalars K)) =
      relativeFundamentalOrdinaryClass S T E C F := by
  have h := finiteContinuousCohomologyIso_restriction
    (AlgEquiv.restrictScalarsHom K : Gal(F/E) →* Gal(F/K))
    continuous_of_discreteTopology (relativeRestrictionCoefficients K C E F) 2
  have he := congrArg (fun u => u.hom
    (relativeFundamentalClass R T K C (F.restrictScalars K))) h
  change (finiteContinuousCohomologyIso ℤ Gal(F/E) (Additive Fˣ) 2).hom
    ((relativeRestriction K C E F 2).hom
      (relativeFundamentalClass R T K C (F.restrictScalars K))) = _ at he
  rw [relativeFundamentalClass_restriction R S T K C E F p] at he
  exact he.symm

end LocalClassFieldTheory
