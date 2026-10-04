/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteCharacterInertia
public import Mathlib.GroupTheory.Coset.Card

/-!
# The finite splitting field of an unramified coefficient character

The field is constructed from the actual open character kernel. Its Galois
character is faithful, its group has prime-to-p order for characteristic-p
coefficients, and its integral inertia is trivial for an unramified character.
This is a field-level step; effective descent of integral group schemes is
still required for the ordinary unramified twist.
-/

@[expose] public noncomputable section
open NumberField IsLocalRing GaloisRepresentation.Extensions
namespace LocalRamification
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
variable {k : Type*} [Field k] [TopologicalSpace k] [DiscreteTopology k]
  (χ : Field.absoluteGaloisGroup (v.adicCompletion K) →* kˣ) (hc : Continuous χ)
local notation "N" => characterOpenNormal v χ hc
local notation "L" => openNormalFixedField N
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

/-- The character of its kernel's fixed field is faithful. -/
theorem finiteModelCharacter_injective : Function.Injective (finiteModelCharacter v χ hc) :=
  (QuotientGroup.kerLift_injective χ).comp (openNormalQuotientEquiv N).symm.injective

/-- The finite Galois group embeds into the original coefficient units. -/
theorem finiteCharacter_group_card_dvd : Nat.card Gal(L/Kv) ∣ Nat.card kˣ :=
  Subgroup.card_dvd_of_injective (finiteModelCharacter v χ hc)
    (finiteModelCharacter_injective v χ hc)

/-- The splitting group has order prime to the residual characteristic. -/
theorem finiteCharacter_group_card_coprime [Finite k] (p : ℕ) [CharP k p] :
    Nat.Coprime p (Nat.card Gal(L/Kv)) :=
  (GaloisRepresentation.Extensions.finiteField_units_card_coprime (p := p) k).of_dvd_right
    (finiteCharacter_group_card_dvd v χ hc)

set_option maxHeartbeats 1000000 in
-- The finite integral-closure inertia types require the restriction theorem's search budget.
/-- An unramified character has trivial integral inertia on its constructed splitting field. -/
theorem finiteCharacter_inertia_eq_bot
    (hχ : localInertiaGroup v ≤ χ.ker) :
    (maximalIdeal (IntegralClosure O L)).inertia Gal(L/Kv) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro g hg
  change g = 1
  obtain ⟨σ, hσ⟩ := finiteIdealInertiaRestriction_surjective v N ⟨g, hg⟩
  apply finiteModelCharacter_injective v χ hc
  rw [map_one]
  have he : (finiteIdealInertiaRestriction v N σ).val = g := congrArg Subtype.val hσ
  rw [← he]
  exact (finiteModelCharacter_restrict v χ hc σ.val).trans (hχ σ.property)

/-- Restriction to the actual open splitting subgroup trivializes the character. -/
theorem finiteCharacter_trivial_on_splitting_subgroup : χ.comp (N).toSubgroup.subtype = 1 := by
  apply MonoidHom.ext
  intro σ
  exact σ.property

end LocalRamification
