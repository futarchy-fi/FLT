/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicCarryArtinInvariant
public import FLT.LocalClassFieldTheory.CyclicCharacterCoordinates
public import FLT.LocalClassFieldTheory.ParameterCarryCharacterComparison

/-!
# Arbitrary character evaluation in a cyclic local extension

The character may have a proper image. Its rational coordinate determines
both the carry class and its value on the independently defined Artin map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory groupCohomology

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

variable {n : ℕ} [NeZero n] (χ : Gal(F/K) →* Multiplicative (ZMod n))
  [IsCyclic Gal(F/K)] (u : Additive Kˣ)

local notation "x" => finiteUnitInvariantInclusion K F u
local notation "c" => finiteParameterCarryClass χ (Additive Fˣ) x

/-- All finite characters of a cyclic extension evaluate the positive parameter carry. -/
theorem cyclicExtension_character_evaluation :
    absoluteInvariant R K C p ((galoisMultiplicativeInflation K C F 2).hom c) =
      zmodToRatCircle n
        (finiteCharacterAbelianization χ (positiveFiniteArtin R S K C F p u)) := by
  let e := cyclicGroupCoordinate Gal(F/K)
  obtain ⟨m, hm⟩ := cyclicCharacter_rational_multiple Gal(F/K) χ
  have hc := finiteParameterCarryClass_character_multiple χ e.toMonoidHom m (Additive Fˣ) x hm
  rw [hc, map_nsmul, map_nsmul,
    cyclicCarry_artin_invariant R S K C F p e.toMonoidHom e.bijective u]
  obtain ⟨g, hg⟩ := (QuotientGroup.mk'_surjective (commutator Gal(F/K)))
    (Additive.toMul (positiveFiniteArtin R S K C F p u))
  have ha : positiveFiniteArtin R S K C F p u = Additive.ofMul (Abelianization.of g) :=
    (congrArg Additive.ofMul hg).symm
  rw [ha, finiteCharacterAbelianization_of, finiteCharacterAbelianization_of]
  exact (hm g).symm

end LocalClassFieldTheory
