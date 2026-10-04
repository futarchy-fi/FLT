/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CharacterCarryArtinEvaluation
public import FLT.LocalClassFieldTheory.KummerParameterCarry

/-!
# Kummer–Artin evaluation with the root-ratio-first sign

The existing Kummer cup, included into field units, has invariant minus the
character on positive finite reciprocity. Its vanishing is detected there.
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
  [Field C] [IsAlgClosed C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  {q : ℕ} [Fact q.Prime] (χ : ContinuousScalarCharacter Gal(C/K) (ZMod q))

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

/-- The root-ratio-first Kummer cup has the negative Artin evaluation. -/
theorem kummerCup_artin_invariant (a : Kˣ) :
    absoluteInvariant R K C p
      (integralH2Class (k := ℤ) (kummerIncludedCup K C q a χ)
        (kummerIncludedCup_isCocycle K C q a χ)) =
      -zmodToRatCircle q
        (finiteCharacterAbelianization ψ
          (positiveFiniteArtin R S K C F p (Additive.ofMul a))) := by
  rw [kummerCarryCup_class, map_neg]
  exact congrArg Neg.neg (characterCarry_artin_evaluation R S K C χ p (Additive.ofMul a))

/-- The included Kummer cup vanishes exactly when the character kills the Artin image. -/
theorem kummerIncludedCup_class_zero_iff (a : Kˣ) :
    integralH2Class (k := ℤ) (kummerIncludedCup K C q a χ)
        (kummerIncludedCup_isCocycle K C q a χ) = 0 ↔
      finiteCharacterAbelianization ψ
        (positiveFiniteArtin R S K C F p (Additive.ofMul a)) = 0 := by
  rw [← map_eq_zero_iff _ (absoluteInvariant R K C p).injective,
    kummerCup_artin_invariant R S K C χ p a, neg_eq_zero, zmodToRatCircle_eq_zero]

end LocalClassFieldTheory
