/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CharacterStageTower
public import FLT.LocalClassFieldTheory.CanonicalCharacterArtin

/-!
# Character evaluation on a caller-selected finite Galois stage

The character field is proved to lie in the supplied finite stage. Its
canonical integral closure supplies the smaller DVR, and unrestricted
Artin tower compatibility gives evaluation on the original stage.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable (R T K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra R T] [Module.Finite R T] [FaithfulSMul R T]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  (F : IntermediateField K C) [IsGalois K F] [FiniteDimensional K F]
  [Algebra T F] [IsFractionRing T F] [Algebra T C] [IsScalarTower T F C]
  [IsScalarTower R T F] [IsScalarTower R T C]
  [Finite (ResidueField R)] [Finite (ResidueField T)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal T) T]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField T) p]
  {n : ℕ} [NeZero n] (χ : Gal(F/K) →* Multiplicative (ZMod n))

attribute [local instance] characterFieldUnitTopology characterFieldUnitDiscrete
  characterFieldBaseTorsionFree characterIntegersFinite characterIntegersFraction
  characterIntegersDvr characterIntegersComplete characterIntegersResidueFinite
  characterIntegersResidueChar finiteStageKernelAlgebra finiteStageKernelBaseTower
  finiteStageKernelClosureTower finiteStageOverfieldAlgebra finiteStageOverfieldFraction
  finiteStageOverfieldTower finiteStageOverfieldUnitTopology finiteStageOverfieldUnitDiscrete
  finiteStageOverfieldGalois finiteStageOverfieldFinite

/-- Finite-stage characters evaluate the parameter carry on that stage's positive Artin map. -/
theorem finiteStage_character_evaluation (u : Additive Kˣ) :
    absoluteInvariant R K C p
      ((galoisMultiplicativeInflation K C F 2).hom
        (finiteParameterCarryClass χ (Additive Fˣ) (finiteUnitInvariantInclusion K F u))) =
      zmodToRatCircle n (finiteCharacterAbelianization χ (positiveFiniteArtin R T K C F p u)) := by
  have ht := characterCarry_artin_tower_evaluation R
    (integralClosure R (characterFixedField K C
      (scalarCharacterHom (restrictedFiniteScalarCharacter K C F χ)))) T K C
    (restrictedFiniteScalarCharacter K C F χ) (finiteStageCharacterOverfield K C F χ) p u
  rw [finiteParameterCarryClass_inflation]
  exact ht.trans (congrArg (fun d => zmodToRatCircle n
    (finiteCharacterAbelianization d (positiveFiniteArtin R T K C F p u)))
      (finiteStage_descendedCharacter K C F χ))

end LocalClassFieldTheory
