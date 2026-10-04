/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteCharacterDescent
public import FLT.LocalClassFieldTheory.ParameterCarryInflation
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The parameter carry on the character's own cyclic field

Every finite continuous scalar character cuts out a finite cyclic Galois
extension. Its parameter carry is the actual inflation from that field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] {n : ℕ} [NeZero n]

/-- Turn the additive scalar character into a continuous multiplicative homomorphism. -/
def scalarCharacterHom (χ : ContinuousScalarCharacter G (ZMod n)) :
    G →ₜ* Multiplicative (ZMod n) where
  toFun g := Multiplicative.ofAdd (χ.val g)
  map_one' := by
    have h := χ.property 1 1
    change χ.val 1 = 0
    exact add_left_cancel (show χ.val 1 + χ.val 1 = χ.val 1 + 0 by
      simpa only [one_mul, add_zero] using h.symm)
  map_mul' g h := χ.property g h
  continuous_toFun := χ.val.continuous

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  (χ : ContinuousScalarCharacter Gal(C/K) (ZMod n))

local notation "F" => characterFixedField K C (scalarCharacterHom χ)
local notation "ψ" => descendedFiniteCharacter K C (scalarCharacterHom χ)

/-- The character field is cyclic, proved from its faithful finite character. -/
instance characterFixedFieldCyclic : IsCyclic Gal(F/K) :=
  isCyclic_of_injective ψ (descendedFiniteCharacter_injective K C (scalarCharacterHom χ))

omit [NeZero n] in
/-- Descent followed by restriction recovers the actual scalar character. -/
theorem characterField_scalar_restriction :
    restrictedFiniteScalarCharacter K C F ψ = χ := by
  apply Subtype.ext
  ext g
  exact congrArg Multiplicative.toAdd
    (descendedFiniteCharacter_restrict K C (scalarCharacterHom χ) g)

variable [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)]
  [TopologicalSpace (Additive (characterFixedField K C (scalarCharacterHom χ))ˣ)]
  [DiscreteTopology (Additive (characterFixedField K C (scalarCharacterHom χ))ˣ)]

attribute [local instance] fieldUnitAction

/-- The original parameter carry is the inflated class on the constructed cyclic field. -/
theorem characterField_carry_inflation (u : Additive Kˣ) :
    (galoisMultiplicativeInflation K C F 2).hom
      (finiteParameterCarryClass ψ (Additive Fˣ) (finiteUnitInvariantInclusion K F u)) =
    integralH2Class (k := ℤ)
      (cyclicParameterCarry (M := Additive Cˣ) χ (finiteUnitInvariantInclusion K C u).val)
      (cyclicParameterCarry_isCocycle (M := Additive Cˣ) _ _
        (finiteUnitInvariantInclusion K C u).property) := by
  rw [finiteParameterCarryClass_inflation, characterField_scalar_restriction]

end LocalClassFieldTheory
