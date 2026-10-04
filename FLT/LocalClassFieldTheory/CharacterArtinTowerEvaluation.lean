/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CharacterCarryArtinEvaluation
public import FLT.LocalClassFieldTheory.PositiveFiniteArtinTower

/-!
# Character evaluation on arbitrary finite Galois overfields

The field above the constructed character field need not be cyclic.
Unrestricted positive Artin tower compatibility transports the proved
character-field evaluation through actual restriction of automorphisms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable (R S T K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Algebra R T] [Module.Finite R T] [FaithfulSMul R T]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  {n : ℕ} [NeZero n] (χ : ContinuousScalarCharacter Gal(C/K) (ZMod n))

local notation "E" => characterFixedField K C (scalarCharacterHom χ)
local notation "ψ" => descendedFiniteCharacter K C (scalarCharacterHom χ)

variable (F : IntermediateField (characterFixedField K C (scalarCharacterHom χ)) C)
  [Algebra S (characterFixedField K C (scalarCharacterHom χ))]
  [IsFractionRing S (characterFixedField K C (scalarCharacterHom χ))]
  [Algebra S C] [IsScalarTower S (characterFixedField K C (scalarCharacterHom χ)) C]
  [IsScalarTower R S (characterFixedField K C (scalarCharacterHom χ))]
  [IsScalarTower R S C]
  [Algebra T F] [IsFractionRing T F] [Algebra T C] [IsScalarTower T F C]
  [IsScalarTower R T C]
  [IsGalois K (F.restrictScalars K)] [FiniteDimensional K (F.restrictScalars K)]
  [Finite (ResidueField R)] [Finite (ResidueField S)] [Finite (ResidueField T)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]
  [IsAdicComplete (maximalIdeal T) T]
  [TopologicalSpace (Additive (characterFixedField K C (scalarCharacterHom χ))ˣ)]
  [DiscreteTopology (Additive (characterFixedField K C (scalarCharacterHom χ))ˣ)]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p] [CharP (ResidueField T) p]

attribute [local instance] relativeFundamentalInflationFinite
  relativeFundamentalInflationFiniteOverBase
  relativeFundamentalInflationTopFractionRing relativeFundamentalInflationTopTower
  relativeFundamentalInflationBaseTower relativeInflationGalois
  relativeInflationMiddleAlgebra relativeInflationMiddleTower
  relativeFundamentalInflationUnitTopology relativeFundamentalInflationUnitDiscrete

attribute [local instance 100] relativeFundamentalInflationTopAlgebra

local notation "f" =>
  (AlgEquiv.restrictNormalHom E : Gal((F.restrictScalars K)/K) →* Gal(E/K))

include S in
/-- General character evaluation on every finite Galois overfield of the character field. -/
theorem characterCarry_artin_tower_evaluation (u : Additive Kˣ) :
    absoluteInvariant R K C p
      (integralH2Class (k := ℤ)
        (cyclicParameterCarry (M := Additive Cˣ) χ (finiteUnitInvariantInclusion K C u).val)
        (cyclicParameterCarry_isCocycle (M := Additive Cˣ) _ _
          (finiteUnitInvariantInclusion K C u).property)) =
      zmodToRatCircle n (finiteCharacterAbelianization ((ψ).comp f)
        (positiveFiniteArtin R T K C (F.restrictScalars K) p u)) := by
  rw [characterCarry_artin_evaluation R S K C χ p,
    positiveFiniteArtin_tower R S T K C E F p]
  congr 1
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (commutator Gal((F.restrictScalars K)/K))
    (Additive.toMul (positiveFiniteArtin R T K C (F.restrictScalars K) p u))
  have ha : positiveFiniteArtin R T K C (F.restrictScalars K) p u =
      Additive.ofMul (Abelianization.of g) := (congrArg Additive.ofMul hg).symm
  rw [ha]
  rfl

end LocalClassFieldTheory
