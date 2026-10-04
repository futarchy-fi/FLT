/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CharacterCarryArtinEvaluation

/-!
# Character evaluation with canonical integers

The integral closure in the character field supplies all local arithmetic
structures. No valuation ring or finite descent is requested from the caller.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C] [CharZero C]
  [IsAdicComplete (maximalIdeal R) R]
  {n : ℕ} [NeZero n] (χ : ContinuousScalarCharacter Gal(C/K) (ZMod n))

local notation "F" => characterFixedField K C (scalarCharacterHom χ)
local notation "S" => integralClosure R F
local notation "ψ" => descendedFiniteCharacter K C (scalarCharacterHom χ)

/-- Discrete units in the finite character field. -/
local instance characterFieldUnitTopology : TopologicalSpace (Additive Fˣ) := ⊥
local instance characterFieldUnitDiscrete : DiscreteTopology (Additive Fˣ) := ⟨rfl⟩

/-- The character field is torsion-free over the base integers. -/
local instance characterFieldBaseTorsionFree : Module.IsTorsionFree R F :=
  .trans_faithfulSMul R K F

/-- The canonical integers are finite over the base. -/
local instance characterIntegersFinite : Module.Finite R S := IsIntegralClosure.finite R K F S

/-- Their fraction field is the constructed character field. -/
local instance characterIntegersFraction : IsFractionRing S F :=
  integralClosure.isFractionRing_of_finite_extension K F

/-- The canonical integers are a DVR by the proved finite-extension theorem. -/
local instance characterIntegersDvr : IsDiscreteValuationRing S := finiteExtension_dvr R K F

/-- Completeness is inherited by the finite integral extension. -/
local instance characterIntegersComplete : IsAdicComplete (maximalIdeal S) S :=
  finiteDvr_complete R S

/-- The canonical residue field is finite. -/
local instance characterIntegersResidueFinite : Finite (ResidueField S) :=
  ResidueField.finite_of_finite (R := R) («S» := S) inferInstance

variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

/-- The residue characteristic is inherited through the residue-field inclusion. -/
local instance characterIntegersResidueChar : CharP (ResidueField S) p :=
  charP_of_injective_ringHom (ResidueField.map (algebraMap R S)).injective p

/-- Evaluate the descended character on positive reciprocity with canonical integers. -/
def characterArtinValue : Additive Kˣ →+ ZMod n :=
  (finiteCharacterAbelianization ψ).comp (positiveFiniteArtin R S K C F p)

/-- The absolute carry invariant is the canonical Artin character value. -/
theorem characterArtinValue_carry (u : Additive Kˣ) :
    absoluteInvariant R K C p
      (integralH2Class (k := ℤ)
        (cyclicParameterCarry (M := Additive Cˣ) χ (finiteUnitInvariantInclusion K C u).val)
        (cyclicParameterCarry_isCocycle (M := Additive Cˣ) _ _
          (finiteUnitInvariantInclusion K C u).property)) =
      zmodToRatCircle n (characterArtinValue R K C χ p u) :=
  characterCarry_artin_evaluation R S K C χ p u

end LocalClassFieldTheory
