/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.InvariantTwoExtensionInflation
public import FLT.LocalClassFieldTheory.RelativeFundamentalQuotientSequences
public import FLT.LocalClassFieldTheory.TwoExtensionDeflation

/-!
# Normalization of the invariant fundamental two-class under inflation

The two actual exact-sequence comparisons show that inflation of the
constructed quotient class is the subgroup-order multiple of the original
fundamental class. The factor is proved at the scalar projection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (F : IntermediateField K C) [IsGalois K F] [FiniteDimensional K F]
  [Algebra S F] [IsFractionRing S F] [Algebra S C] [IsScalarTower S F C]
  [IsScalarTower R S F] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p]

local notation "M" => Rep.ofAlgebraAutOnUnits K F
local notation "c" => twoClassRepresentative M (relativeFundamentalOrdinaryClass R S K C F)
local notation "Q" => shiftedCoefficients M
local notation "b" => shiftedTwoCocycle M c

variable (N : Subgroup Gal(F/K)) [N.Normal] [Fintype N]

/-- The constructed invariant two-class has the required inflation normalization. -/
theorem relativeFundamentalInvariantTwoClass_inflation :
    groupCohomology.map (QuotientGroup.mk' N) (quotientInflationCoefficients M N) 2
      (relativeFundamentalInvariantTwoClass R S K C F p N) =
        Fintype.card N • relativeFundamentalOrdinaryClass R S K C F := by
  have h := congrArg (fun u => u.hom
    ((groupCohomology.H0Iso (Rep.trivial ℤ (Gal(F/K) ⧸ N) ℤ)).inv
      ⟨(1 : ℤ), fun _ => rfl⟩))
    (invariantTwoExtension_inflation M c N
      (relativeFundamentalShifted_subgroup_zero R S K C F p N)
      (relativeFundamentalExtension_allSubgroup_isZero R S K C F p N 0) 0)
  change groupCohomology.map (QuotientGroup.mk' N) (quotientInflationCoefficients M N) 2
      (relativeFundamentalInvariantTwoClass R S K C F p N) =
    twoExtensionCohomologyMap M c 0
      (groupCohomology.map (QuotientGroup.mk' N)
        ((Fintype.card N : ℤ) • 𝟙 (Rep.trivial ℤ Gal(F/K) ℤ)) 0
        ((groupCohomology.H0Iso (Rep.trivial ℤ (Gal(F/K) ⧸ N) ℤ)).inv
          ⟨(1 : ℤ), fun _ => rfl⟩)) at h
  rw [groupScalarUnit_map] at h
  have hs := (twoExtensionCohomologyMap M c 0).hom.map_smul (Fintype.card N : ℤ)
    ((groupCohomology.H0Iso (Rep.trivial ℤ Gal(F/K) ℤ)).inv ⟨(1 : ℤ), fun _ => rfl⟩)
  have he := h.trans hs
  rw [twoExtensionCohomologyMap_one, twoClassRepresentative_spec] at he
  simpa only [RingHom.id_apply, Nat.cast_smul_eq_nsmul,
    Int.cast_smul_eq_zsmul, natCast_zsmul] using he

end LocalClassFieldTheory
