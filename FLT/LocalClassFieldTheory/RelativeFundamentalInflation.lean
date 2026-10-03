/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeInflationTower
public import FLT.LocalClassFieldTheory.FundamentalClassBaseChange
public import FLT.LocalClassFieldTheory.FundamentalClasses

/-!
# Inflation of the finite relative fundamental class

The class for E/K inflates to [F:E] times the class for F/K.
The positive rational normalization fixes the integer factor and its sign.
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
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C) (F : IntermediateField E C)
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S E] [IsScalarTower R S C]
  [Algebra T F] [IsFractionRing T F] [Algebra T C] [IsScalarTower T F C]
  [IsScalarTower R T C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)] [Finite (ResidueField T)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]
  [IsAdicComplete (maximalIdeal T) T]
  [IsGalois K E] [IsGalois K (F.restrictScalars K)]
  [FiniteDimensional K E] [FiniteDimensional K (F.restrictScalars K)]

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalInflationFinite : FiniteDimensional K F :=
  inferInstanceAs (FiniteDimensional K (F.restrictScalars K))
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalInflationFiniteOverBase : FiniteDimensional E F :=
  FiniteDimensional.right K E F
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalInflationTopAlgebra : Algebra T (F.restrictScalars K) :=
  inferInstanceAs (Algebra T F)
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalInflationTopFractionRing :
    IsFractionRing T (F.restrictScalars K) :=
  inferInstanceAs (IsFractionRing T F)
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalInflationTopTower : IsScalarTower T (F.restrictScalars K) C :=
  inferInstanceAs (IsScalarTower T F C)
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalInflationBaseTower : IsScalarTower R T (F.restrictScalars K) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    apply (algebraMap (F.restrictScalars K) C).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
variable [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]

/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalInflationUnitTopology :
    TopologicalSpace (Additive (F.restrictScalars K)ˣ) :=
  inferInstanceAs (TopologicalSpace (Additive Fˣ))
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalInflationUnitDiscrete :
    DiscreteTopology (Additive (F.restrictScalars K)ˣ) :=
  inferInstanceAs (DiscreteTopology (Additive Fˣ))

variable [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p]

include p in
/-- Inflation scales the relative fundamental class by the remaining top-field degree. -/
theorem relativeFundamentalClass_tower :
    (relativeInflation K C E F 2).hom (relativeFundamentalClass R S K C E) =
      Module.finrank E F • relativeFundamentalClass R T K C (F.restrictScalars K) := by
  apply galoisMultiplicativeInflationH2_injective K C (F.restrictScalars K)
  rw [map_nsmul, relativeFundamentalClass_inflation R T K C (F.restrictScalars K) p]
  change (relativeInflation K C E F 2 ≫
    galoisMultiplicativeInflation K C (F.restrictScalars K) 2).hom
      (relativeFundamentalClass R S K C E) = _
  rw [relativeInflation_tower, relativeFundamentalClass_inflation R S K C E p]
  apply (absoluteInvariant R K C p).injective
  rw [map_nsmul, absoluteFundamentalClass_invariant, absoluteFundamentalClass_invariant,
    ← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  have hd : Module.finrank K (F.restrictScalars K) =
      Module.finrank K E * Module.finrank E F := (Module.finrank_mul_finrank K E F).symm
  have he : (Module.finrank K E : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hf : (Module.finrank E F : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [hd, Nat.cast_mul]
  field_simp

end LocalClassFieldTheory
