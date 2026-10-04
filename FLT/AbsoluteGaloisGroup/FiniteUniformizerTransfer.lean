/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteUniformizerRootCharacter
public import FLT.AbsoluteGaloisGroup.UniformizerCharacterTransfer

/-!
# Transfer to a specified finite inertia model

For an inclusion of actual finite Galois levels, construct the integral and
residue inclusions and prove their uniformizer-character power relation.
The exponent is the valuation of the original uniformizer in the larger field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing IntermediateField
namespace LocalRamification
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
variable (N M : OpenNormalSubgroup (Field.absoluteGaloisGroup (v.adicCompletion K)))
  (hle : M ≤ N)
local notation "L" => fixedField N.toSubgroup
local notation "E" => fixedField M.toSubgroup
local notation "R" => IntegralClosure O L
local notation "S" => IntegralClosure O E
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

/-- The inclusion of the actual integral closures of nested finite Galois levels. -/
def finiteClosureInclusion : R →+* S :=
  IntegralClosure.map ((IntermediateField.inclusion (fixedField_le hle)).restrictScalars O)

/-- The finite integral inclusion is injective. -/
theorem finiteClosureInclusion_injective :
    Function.Injective (finiteClosureInclusion v N M hle) :=
  IntegralClosure.map_injective _
    ((IntermediateField.inclusion (fixedField_le hle)).restrictScalars O).injective

/-- The integral inclusion induces the canonical residue inclusion. -/
instance finiteClosureInclusion_isLocalHom : IsLocalHom (finiteClosureInclusion v N M hle) := by
  have hi : ((finiteClosureInclusion v N M hle).comp (algebraMap O R)).IsIntegral := by
    change (algebraMap O S).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  exact (RingHom.IsIntegral.tower_top _ _ hi).isLocalHom
    (finiteClosureInclusion_injective v N M hle)

/-- Finite inclusion commutes with inclusion in the absolute integral closure. -/
theorem finiteClosureInclusion_absolute (x : R) :
    finiteClosureToAbsolute v M (finiteClosureInclusion v N M hle x) =
      finiteClosureToAbsolute v N x := rfl

/-- The residue inclusions commute with the absolute residue inclusion. -/
theorem finiteClosureInclusion_residue (x : ResidueField R) :
    ResidueField.map (finiteClosureToAbsolute v M)
      (ResidueField.map (finiteClosureInclusion v N M hle) x) =
        ResidueField.map (finiteClosureToAbsolute v N) x := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  rfl

/-- The actual inclusions intertwine the restricted absolute Galois actions. -/
theorem finiteClosureInclusion_equivariant (σ : Field.absoluteGaloisGroup F) (x : R) :
    finiteClosureInclusion v N M hle ((AlgEquiv.restrictNormalHom L σ) • x) =
      (AlgEquiv.restrictNormalHom E σ) • finiteClosureInclusion v N M hle x := by
  apply Subtype.ext
  apply Subtype.ext
  change (σ.restrictNormal L x.1 : AlgebraicClosure F) =
    (σ.restrictNormal E ((IntermediateField.inclusion (fixedField_le hle)) x.1) :
      AlgebraicClosure F)
  simp only [AlgEquiv.restrictNormal_apply]
  rfl

set_option maxHeartbeats 1000000 in
-- Finite integral-closure inertia actions require a larger elaboration budget.
set_option synthInstance.maxHeartbeats 100000 in
/-- Transfer back to the prescribed model, with the actual valuation as exponent. -/
theorem finiteUniformizer_character_transfer {π : R} (hπ : Irreducible π)
    {ϖ : S} (hϖ : Irreducible ϖ) :
    ∃ e : ℕ, IsDiscreteValuationRing.addVal S (finiteClosureInclusion v N M hle π) = e ∧
      ∀ σ : localInertiaGroup v,
        ResidueField.map (finiteClosureInclusion v N M hle)
          (ThreeAdicPlan.uniformizerCharacter hπ (finiteIdealInertiaRestriction v N σ) :
            ResidueField R) =
          (ThreeAdicPlan.uniformizerCharacter hϖ (finiteIdealInertiaRestriction v M σ) :
            ResidueField S) ^ e := by
  obtain ⟨e, he, hc⟩ := ThreeAdicPlan.uniformizerCharacter_transfer
    (G := Gal(L/F)) (H := Gal(E/F)) (finiteClosureInclusion v N M hle)
    (finiteClosureInclusion_injective v N M hle) hπ hϖ
  exact ⟨e, he, fun σ ↦ hc _ _ (finiteClosureInclusion_equivariant v N M hle σ.val π)⟩

end LocalRamification
