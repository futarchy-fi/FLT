/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CharacterFieldCarry
public import FLT.LocalClassFieldTheory.CyclicExtensionCharacterEvaluation

/-!
# Evaluation of every finite continuous character's parameter carry

The character's finite cyclic field is constructed from its open kernel.
The absolute invariant evaluates the existing positive Artin map on that
field; neither descent nor the character evaluation is a premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  {n : ℕ} [NeZero n] (χ : ContinuousScalarCharacter Gal(C/K) (ZMod n))

local notation "F" => characterFixedField K C (scalarCharacterHom χ)
local notation "ψ" => descendedFiniteCharacter K C (scalarCharacterHom χ)

variable [Algebra S (characterFixedField K C (scalarCharacterHom χ))]
  [IsFractionRing S (characterFixedField K C (scalarCharacterHom χ))]
  [Algebra S C] [IsScalarTower S (characterFixedField K C (scalarCharacterHom χ)) C]
  [IsScalarTower R S (characterFixedField K C (scalarCharacterHom χ))]
  [IsScalarTower R S C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]
  [TopologicalSpace (Additive (characterFixedField K C (scalarCharacterHom χ))ˣ)]
  [DiscreteTopology (Additive (characterFixedField K C (scalarCharacterHom χ))ˣ)]
  [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p]

/-- General finite-character evaluation of the actual positive parameter carry. -/
theorem characterCarry_artin_evaluation (u : Additive Kˣ) :
    absoluteInvariant R K C p
      (integralH2Class (k := ℤ)
        (cyclicParameterCarry (M := Additive Cˣ) χ (finiteUnitInvariantInclusion K C u).val)
        (cyclicParameterCarry_isCocycle (M := Additive Cˣ) _ _
          (finiteUnitInvariantInclusion K C u).property)) =
      zmodToRatCircle n
        (finiteCharacterAbelianization ψ (positiveFiniteArtin R S K C F p u)) := by
  rw [← characterField_carry_inflation K C χ u]
  exact cyclicExtension_character_evaluation R S K C F p ψ u

end LocalClassFieldTheory
