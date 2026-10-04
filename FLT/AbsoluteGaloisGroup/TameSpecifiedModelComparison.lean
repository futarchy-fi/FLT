/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteUniformizerTransfer
public import FLT.AbsoluteGaloisGroup.TameCommonLevel

/-!
# Comparing the specified finite model with the absolute tame character

Both characters are computed in a constructed common finite level. Taking
powers eliminates its uniformizer character and gives a relation in the
actual absolute residue field. This does not cancel noninvertible exponents
or classify niveau-two representations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing IntermediateField LocalRamification
namespace LocalRoot
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
variable (N : OpenNormalSubgroup (Field.absoluteGaloisGroup (v.adicCompletion K)))
local notation "R" => IntegralClosure O (fixedField N.toSubgroup)
local notation "M" => tameCommonLevel v N
local notation "S" => IntegralClosure O (fixedField
  (OpenSubgroup.toSubgroup (OpenNormalSubgroup.toOpenSubgroup (tameCommonLevel v N))))
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

set_option maxHeartbeats 1000000 in
-- Comparing the three integral-closure towers needs extra elaboration time.
set_option synthInstance.maxHeartbeats 100000 in
/-- The original finite uniformizer character and tameCharacter satisfy their actual
common-level power relation, with both exponents constructed from valuations. -/
theorem tameCharacter_specifiedModel_power {π : R} (hπ : Irreducible π) :
    ∃ e k : ℕ, 0 < e ∧ 0 < k ∧
      IsDiscreteValuationRing.addVal S
        (finiteClosureInclusion v N M inf_le_left π) = e ∧
      (maximalIdeal S).ramificationIdx O = (Nat.card (ResidueField O) - 1) * k ∧
      ∀ σ : localInertiaGroup v,
        ResidueField.map (finiteClosureToAbsolute v N)
          (ThreeAdicPlan.uniformizerCharacter hπ (finiteIdealInertiaRestriction v N σ) :
            ResidueField R) ^ k =
          residueFieldMap v (tameCharacter v σ : ResidueField O) ^ e := by
  obtain ⟨ϖ, hϖ, k, hk, hc⟩ := tameCommonLevel_character v N
  obtain ⟨e, he, ht⟩ := finiteUniformizer_character_transfer v N M inf_le_left hπ hϖ
  have hepos : 0 < e := by
    apply Nat.pos_of_ne_zero
    intro he0
    have hu : IsUnit (finiteClosureInclusion v N M inf_le_left π) :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.mp (by simpa [he0] using he)
    exact hπ.not_isUnit (isUnit_of_map_unit _ π hu)
  let : Module.Finite O S := IsIntegralClosure.finite O F (fixedField (M).toSubgroup)
    (integralClosure O (fixedField (M).toSubgroup))
  have hkpos : 0 < k := by
    have hp := (maximalIdeal S).ramificationIdx_pos O
    rw [hk] at hp
    by_contra hk0
    have hz : k = 0 := by omega
    simp [hz] at hp
  refine ⟨e, k, hepos, hkpos, he, hk, fun σ ↦ ?_⟩
  have hh := congrArg (ResidueField.map (finiteClosureToAbsolute v M)) (ht σ)
  rw [finiteClosureInclusion_residue, map_pow] at hh
  rw [hh, ← pow_mul, Nat.mul_comm e k, pow_mul, ← map_pow, hc σ]

end LocalRoot
