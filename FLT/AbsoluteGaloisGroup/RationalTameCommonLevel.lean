/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteTameRootExponent
public import FLT.AbsoluteGaloisGroup.RationalTameRootModel

/-!
# A common tame-root level for any rational finite Galois model

Intersect the given open normal subgroup with the fixing subgroup of the
chosen tame root. This constructs a finite comparison field containing both
models and proves its ramification-exponent character formula.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing IntermediateField LocalRamification
namespace LocalRoot
variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "F" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "Ω" => AlgebraicClosure F
variable (level : OpenNormalSubgroup (Field.absoluteGaloisGroup
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)))

/-- A canonical finite level containing both the given model and the chosen tame root. -/
def rationalTameCommonLevel : OpenNormalSubgroup (Field.absoluteGaloisGroup F) :=
  level ⊓ rationalTameRootLevel p

local notation "M" => rationalTameCommonLevel p level
local notation "L" => fixedField
  (OpenSubgroup.toSubgroup (OpenNormalSubgroup.toOpenSubgroup (rationalTameCommonLevel p level)))
local notation "D" => IntegralClosure O L
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

/-- The original finite model embeds into the common comparison field. -/
theorem rationalTameCommonLevel_contains_model : fixedField level.toSubgroup ≤ L :=
  fixedField_le (show (M).toSubgroup ≤ level.toSubgroup from inf_le_left)

/-- The common comparison field contains the actual tame-root field. -/
theorem rationalTameCommonLevel_contains_root : tameRootField v ≤ L := by
  rw [← rationalTameRootLevel_fixedField p]
  exact fixedField_le (show (M).toSubgroup ≤ (rationalTameRootLevel p).toSubgroup from
    inf_le_right)

/-- The chosen root becomes an integer of the constructed common finite field. -/
def rationalTameCommonRoot : D := by
  let a : L := ⟨tameUniformizerRoot v,
    rationalTameCommonLevel_contains_root p level (mem_adjoin_simple_self _ _)⟩
  refine ⟨a, IsIntegral.of_pow (tameDegree_pos v) ?_⟩
  have h : a ^ (Nat.card (ResidueField O) - 1) = algebraMap O L (tameUniformizer v) :=
    Subtype.ext (tameUniformizerRoot_spec v)
  rw [h]
  exact isIntegral_algebraMap

set_option maxHeartbeats 1000000 in
-- The actual integral-closure and finite inertia actions need additional elaboration time.
set_option synthInstance.maxHeartbeats 100000 in
/-- Every finite model has a constructed common level with the ramification-exponent formula. -/
theorem rationalTameCommonLevel_character :
    ∃ (π : D) (hπ : Irreducible π) (k : ℕ),
      (maximalIdeal D).ramificationIdx O = (Nat.card (ResidueField O) - 1) * k ∧
      ∀ σ : localInertiaGroup v,
        ResidueField.map (finiteClosureToAbsolute v M)
          ((ThreeAdicPlan.uniformizerCharacter hπ (finiteIdealInertiaRestriction v M σ) :
            ResidueField D) ^ k) = residueFieldMap v (tameCharacter v σ : ResidueField O) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible D
  obtain ⟨k, hk, hc⟩ := finiteTameRoot_character_exponent v M
    (y := rationalTameCommonRoot p level) rfl hπ
  exact ⟨π, hπ, k, hk, hc⟩

end LocalRoot
