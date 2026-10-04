/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CharacterArtinTowerEvaluation

/-!
# The actual tower from a character kernel to its finite stage

The restricted character's kernel field lies in its original finite Galois
stage. The resulting tower uses the actual inclusion of intermediate fields.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  (F : IntermediateField K C) [IsGalois K F] [FiniteDimensional K F]
  {n : ℕ} [NeZero n] (χ : Gal(F/K) →* Multiplicative (ZMod n))

omit [NeZero n] in
/-- The kernel field of a restricted finite character lies in the original finite stage. -/
theorem restrictedCharacterField_le :
    characterFixedField K C (scalarCharacterHom (restrictedFiniteScalarCharacter K C F χ)) ≤ F := by
  apply le_trans ?_ (le_of_eq (InfiniteGalois.fixedField_fixingSubgroup F))
  apply IntermediateField.fixedField_le
  intro g hg
  have hr : g.restrictNormal F = 1 := by
    change g ∈ (AlgEquiv.restrictNormalHom F : Gal(C/K) →* Gal(F/K)).ker
    rwa [IntermediateField.restrictNormalHom_ker]
  change χ (g.restrictNormal F) = 1
  rw [hr, map_one]


/-- The original finite stage, viewed over the constructed kernel field. -/
def finiteStageCharacterOverfield :
    IntermediateField (characterFixedField K C
      (scalarCharacterHom (restrictedFiniteScalarCharacter K C F χ))) C :=
  IntermediateField.extendScalars (restrictedCharacterField_le K C F χ)

omit [NeZero n] in
/-- Scalar restriction recovers the original finite stage exactly. -/
theorem finiteStageCharacterOverfield_restrict :
    (finiteStageCharacterOverfield K C F χ).restrictScalars K = F := rfl

/-- The kernel field acts on the original stage by its actual inclusion. -/
local instance finiteStageKernelAlgebra :
    Algebra (characterFixedField K C
      (scalarCharacterHom (restrictedFiniteScalarCharacter K C F χ))) F :=
  inferInstanceAs (Algebra _ (finiteStageCharacterOverfield K C F χ))

/-- The base-field tower is the one induced by actual intermediate-field inclusions. -/
local instance finiteStageKernelBaseTower :
    IsScalarTower K (characterFixedField K C
      (scalarCharacterHom (restrictedFiniteScalarCharacter K C F χ))) F :=
  inferInstanceAs (IsScalarTower K _ (finiteStageCharacterOverfield K C F χ))

/-- The inclusion tower ends in the original separable closure. -/
local instance finiteStageKernelClosureTower :
    IsScalarTower (characterFixedField K C
      (scalarCharacterHom (restrictedFiniteScalarCharacter K C F χ))) F C :=
  inferInstanceAs (IsScalarTower _ (finiteStageCharacterOverfield K C F χ) C)

omit [NeZero n] in
/-- Restricting to the kernel field and evaluating its descended character recovers the input. -/
theorem finiteStage_descendedCharacter :
    (descendedFiniteCharacter K C
      (scalarCharacterHom (restrictedFiniteScalarCharacter K C F χ))).comp
      (AlgEquiv.restrictNormalHom (characterFixedField K C
        (scalarCharacterHom (restrictedFiniteScalarCharacter K C F χ))) :
          Gal(F/K) →* _) = χ := by
  apply MonoidHom.ext
  intro s
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective C s
  rw [MonoidHom.comp_apply, ← IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply
    (characterFixedField K C (scalarCharacterHom (restrictedFiniteScalarCharacter K C F χ))) F σ]
  exact descendedFiniteCharacter_restrict K C
    (scalarCharacterHom (restrictedFiniteScalarCharacter K C F χ)) σ

/-- The original Galois property is unchanged by the tower presentation. -/
local instance finiteStageOverfieldGalois :
    IsGalois K ((finiteStageCharacterOverfield K C F χ).restrictScalars K) :=
  inferInstanceAs (IsGalois K F)

/-- The original finite degree is unchanged by the tower presentation. -/
local instance finiteStageOverfieldFinite :
    FiniteDimensional K ((finiteStageCharacterOverfield K C F χ).restrictScalars K) :=
  inferInstanceAs (FiniteDimensional K F)

/-- Discrete-unit topology can be reused on the same field presented over its kernel field. -/
local instance finiteStageOverfieldUnitTopology [TopologicalSpace (Additive Fˣ)] :
    TopologicalSpace (Additive (finiteStageCharacterOverfield K C F χ)ˣ) :=
  inferInstanceAs (TopologicalSpace (Additive Fˣ))

/-- Discreteness can be reused on the same field presented over its kernel field. -/
local instance finiteStageOverfieldUnitDiscrete [TopologicalSpace (Additive Fˣ)]
    [DiscreteTopology (Additive Fˣ)] :
    DiscreteTopology (Additive (finiteStageCharacterOverfield K C F χ)ˣ) :=
  inferInstanceAs (DiscreteTopology (Additive Fˣ))

variable (T : Type) [CommRing T] [Algebra T F]

/-- Integer algebras are unchanged by the intermediate-field tower presentation. -/
local instance finiteStageOverfieldAlgebra : Algebra T (finiteStageCharacterOverfield K C F χ) :=
  inferInstanceAs (Algebra T F)

/-- Fraction fields are unchanged by the intermediate-field tower presentation. -/
local instance finiteStageOverfieldFraction [IsFractionRing T F] :
    IsFractionRing T (finiteStageCharacterOverfield K C F χ) := inferInstanceAs (IsFractionRing T F)

/-- The integer-to-closure tower is unchanged. -/
local instance finiteStageOverfieldTower [Algebra T C] [IsScalarTower T F C] :
    IsScalarTower T (finiteStageCharacterOverfield K C F χ) C :=
  inferInstanceAs (IsScalarTower T F C)

end LocalClassFieldTheory
